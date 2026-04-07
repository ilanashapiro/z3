/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    search_tree.h

Abstract:

    A binary search tree for managing the search space of a DPLL(T) solver.
    It supports splitting on atoms, backtracking on conflicts, and activating nodes.

    Nodes can be in one of three states: open, closed, or active.
    - Closed nodes are fully explored (both children are closed).
    - Active nodes are currently assigned to a worker.
    - Open nodes are unsolved and available for future activation.

    Tree activation follows an SMTS-style policy: prefer nodes in lower
    accumulated-effort bands, and then prefer deeper nodes within the same band.

    Tree expansion is also SMTS-inspired: a timeout does not force an immediate
    split. Instead, expansion is gated to avoid overgrowing the tree and prefers
    shallow timed-out leaves so that internal nodes can be revisited.

    Backtracking on a conflict closes all nodes below the last node whose atom is in the conflict set.

    Activation selects a best-ranked open node using accumulated effort and depth.

Author:

    Ilana Shapiro   2025-9-06

--*/

#include "util/util.h"
#include "util/vector.h"
#pragma once

namespace search_tree {

    enum class status { open, closed, active };

    template <typename Config> class node {
        typedef typename Config::literal literal;
        literal m_literal;
        node *m_left = nullptr, *m_right = nullptr, *m_parent = nullptr;
        status m_status;
        vector<literal> m_core;
        unsigned m_num_activations = 0;
        unsigned m_effort_spent = 0;
        // unsigned m_active_workers = 0; 

    public:
        node(literal const &l, node *parent) : m_literal(l), m_parent(parent), m_status(status::open) {}
        ~node() {
            dealloc(m_left);
            dealloc(m_right);
        }

        status get_status() const {
            return m_status;
        }
        void set_status(status s) {
            m_status = s;
        }
        literal const &get_literal() const {
            return m_literal;
        }
        bool literal_is_null() const {
            return Config::is_null(m_literal);
        }
        void split(literal const &a, literal const &b) {
            SASSERT(!Config::literal_is_null(a));
            SASSERT(!Config::literal_is_null(b));
            if (m_status != status::active)
                return;
            SASSERT(!m_left);
            SASSERT(!m_right);
            m_left = alloc(node<Config>, a, this);
            m_right = alloc(node<Config>, b, this);
            m_status = status::open;
        }

        node* left() const { return m_left; }
        node* right() const { return m_right; }
        node* parent() const { return m_parent; }
        bool is_leaf() const { return !m_left && !m_right; }

        unsigned depth() const {
            unsigned d = 0;
            node* p = m_parent;
            while (p) {
                ++d;
                p = p->parent();
            }
            return d;
        }
        
        void display(std::ostream &out, unsigned indent) const {
            for (unsigned i = 0; i < indent; ++i)
                out << " ";
            Config::display_literal(out, m_literal);
            out << (get_status() == status::open ? " (o)" : get_status() == status::closed ? " (c)" : " (a)");
            out << "\n";
            if (m_left)
                m_left->display(out, indent + 2);
            if (m_right)
                m_right->display(out, indent + 2);
        }

        void set_core(vector<literal> const &core) {
            m_core = core;
        }
        vector<literal> const &get_core() const {
            return m_core;
        }
        void clear_core() {
            m_core.clear();
        }
        unsigned num_activations() const {
            return m_num_activations;
        }
        void mark_new_activation() {
            set_status(status::active);
            ++m_num_activations;
            // inc_active_workers();
        }
        unsigned effort_spent() const {
            return m_effort_spent;
        }
        void add_effort(unsigned effort) {
            m_effort_spent += effort;
        }
        // void inc_active_workers() { 
        //     ++m_active_workers; 
        // }
        // void dec_active_workers() { 
        //     SASSERT(m_active_workers > 0); 
        //     --m_active_workers; 
        // }
        // unsigned active_workers() const { 
        //     return m_active_workers; 
        // }
    };

    template <typename Config> class tree {
        typedef typename Config::literal literal;
        scoped_ptr<node<Config>> m_root = nullptr;
        literal m_null_literal;
        random_gen m_rand;
        unsigned m_expand_factor = 2;       // k in paper's Algorithm 4
        unsigned m_effort_unit = 1;         // TS (solver timeout) in paper's Algorithm 2
        unsigned m_num_workers = 1;         // n in paper's Algorithm 4 (number of available solvers/workers)
        unsigned m_max_timeout_factor = 4;  // Threshold for excluding heavily timed-out nodes from tree size

        struct candidate {
            node<Config>* n = nullptr;
            unsigned effort_band = UINT64_MAX;  // corresponds to maxTouts in paper's Algorithm 2
            unsigned depth = 0;
        };

        // Compute the effort band (timeout threshold) for a node.
        // This corresponds to maxTouts in the paper's Algorithm 2:
        // effort_band = floor(node.time / TS) where TS is the solver timeout unit.
        unsigned effort_band(node<Config> const* n) const {
            return n->effort_spent() / m_effort_unit;
        }

        // Compare two candidate nodes according to the SMTS selection policy (Algorithm 2).
        // 
        // Paper's Algorithm 2 priority:
        //   1. Lower effort band (fewer timeouts) - corresponds to outer loop over maxTouts
        //   2. Greater depth (depth-first bias) - corresponds to inner loop from maxDepth down to 0
        //
        // This ensures unvisited nodes (effort_band=0) are always preferred before any node
        // that has timed out, matching the paper's nested loop structure.
        bool better(candidate const& a, candidate const& b) const {
            if (!a.n)
                return false;
            if (!b.n)
                return true;
            if (a.effort_band != b.effort_band)
                return a.effort_band < b.effort_band;
            if (a.depth != b.depth)
                return a.depth > b.depth;
            return false;
        }

        // Traverse the entire subtree and select the best open (or active! -> portfolio solving mode) node according to
        // the SMTS node selection policy (paper's Algorithm 2):
        //
        // 1. Prefer nodes with lower effort bands (fewer accumulated timeouts).
        //    - effort_band = floor(node.time / TS) corresponds to maxTouts in the paper
        //    - This ensures NEW (unvisited) nodes are always tried before revisiting timed-out nodes
        //
        // 2. Break ties by preferring deeper nodes (depth-first bias within same timeout band).
        //    - Corresponds to the inner loop: for d = maxDepth; d >= 0; d--
        //
        // This function does NOT activate nodes; it only updates `best` with the
        // highest-ranked open candidate found during traversal.
        void select_next_node(node<Config>* cur, status target_status, candidate& best) const {
            if (!cur || cur->get_status() == status::closed)
                return;

            if (cur->get_status() == target_status) {
                candidate cand;
                cand.n = cur;
                cand.effort_band = effort_band(cur);
                cand.depth = cur->depth();

                if (better(cand, best))
                    best = cand;
            }

            select_next_node(cur->left(), target_status, best);
            select_next_node(cur->right(), target_status, best);
        }

        // Select and activate the best available open node in the tree.
        //
        // Uses `select_next_node` to globally rank all open nodes based on:
        //   (1) lowest effort band
        //   (2) greatest depth (tie-break)
        //
        // The selected node is marked as active and its activation counter is updated.
        //
        // Returns nullptr if no open node is available.
        node<Config>* activate_best_node() {
            candidate best;
            select_next_node(m_root.get(), status::open, best);
            if (!best.n) {
                IF_VERBOSE(1, verbose_stream() << "NO OPEN NODES, trying active nodes for portfolio solving\n";);
                select_next_node(m_root.get(), status::active, best); // If no open nodes, only then consider active nodes for selection
            }
                
            if (!best.n)
                return nullptr;
            best.n->mark_new_activation();
            return best.n;
        }

        // Count nodes for expansion decision, with optimization from paper.
        //
        // Paper's optimization (after Algorithm 4):
        //   "Alg. 4 excludes nodes that have already timed out a certain number
        //    of times when computing the size of the tree |tree| (e.g., when
        //    node.time >= 4·TS)."
        //
        // This makes the tree appear smaller, encouraging expansion on hard instances
        // where some nodes have consumed many timeouts without solving.
        // Count ALL nodes in the tree (including closed ones).
        // This matches the paper's |tree| definition used in Algorithm 4.
        unsigned count_unsolved_nodes(node<Config>* cur) const {
            if (!cur || cur->get_status() == status::closed)
                return 0;

            // Optimization: exclude nodes that have timed out too many times
            // Paper suggests threshold of 4·TS (4 timeout periods)
            // if (cur->effort_spent() >= m_max_timeout_factor * m_effort_unit)
            //     return 0;  // Don't count heavily timed-out nodes

            return 1 + count_unsolved_nodes(cur->left()) + count_unsolved_nodes(cur->right());
        }

        bool has_unvisited_open_node(node<Config>* cur) const {
            if (!cur || cur->get_status() == status::closed)
                return false;
            if (cur->get_status() == status::open && cur->num_activations() == 0)
                return true;
            return has_unvisited_open_node(cur->left()) || has_unvisited_open_node(cur->right());
        }

        // Compute the minimum depth among all leaf nodes that have timed out (effort_spent > 0).
        // This corresponds to Algorithm 4's SelectShallowestLeaf(tree),
        // but instead of selecting one node, we compute the shallowest depth
        // so that ANY node at that depth is eligible for expansion.
        //
        // IMPORTANT:
        // - Only considers leaves with effort_spent() > 0 (i.e., timed-out nodes)
        // - Assumes caller already checked: no NEW nodes exist (SMTS Gate 4)
        void find_shallowest_timed_out_leaf_depth(node<Config>* cur, unsigned& best_depth) const {
            if (!cur || cur->get_status() == status::closed)
                return;
            
            if (cur->is_leaf() && cur->effort_spent() > 0)
                best_depth = std::min(best_depth, cur->depth());
            
            find_shallowest_timed_out_leaf_depth(cur->left(), best_depth);
            find_shallowest_timed_out_leaf_depth(cur->right(), best_depth);
        }

        // Decide whether to expand the tree when node `n` has timed out.
        //
        // This implements the SMTS tree expansion policy (paper's Algorithm 4: TryExpandTree).
        //
        // CRITICAL differences from paper's pure semantics:
        //   - Paper: TryExpandTree globally selects ANY shallowest leaf to expand
        //   - Z3: We can only expand `n` (because we only have split literals for it)
        //   - Compromise: Use paper's gates, but add check that `n` IS the shallowest
        //
        // CRITICAL timing semantics:
        //   - Paper: node.time updated BEFORE TryExpandTree is called
        //   - Implementation: n->add_effort() called BEFORE this function
        //
        // Algorithm 4 gates (with correct semantics):
        //   Line 2-3:  if |tree| >= n then [if |tree| >= k*n then return]  // SEPARATE checks
        //   Line 5-6:  if ∃node with status=NEW then return
        //   Line 7-9:  r ← Random(); if r >= 1/p then return              // INDEPENDENT of size
        //   Line 10:   node ← SelectShallowestLeaf(tree)                   // GLOBAL selection
        //
        // Paper's optimization: |tree| excludes nodes with node.time >= 4·TS
        //
        // Returns true if node `n` should be expanded.
        bool should_split(node<Config>* n) {
            if (!n || !n->is_leaf())
                return false;

            // Use optimized tree size computation (excludes heavily timed-out nodes)
            // Paper's optimization after Algorithm 4: exclude nodes where node.time >= 4·TS
            unsigned tree_size = count_unsolved_nodes(m_root.get());
            unsigned k = m_expand_factor;

            // Gate 2-3: Size constraints (Algorithm 4, lines 2-4)
            if (tree_size >= k * m_num_workers)
                return false;

            // ONLY throttle when tree is "large enough"
            // Between n and k*n - continue to other gates
            if (tree_size >= m_num_workers) {
                // Gate 4: NEW node check (Algorithm 4, line 5)
                if (has_unvisited_open_node(m_root.get()))
                    return false;

                // Gate 5: Random throttling (Algorithm 4, lines 7-9)
                // r ← Random() ∈ ]0,1[; if r >= 1/p then abort
                // With p=2, this gives 50% rejection
                if (m_rand(2) != 0)
                    return false;
            }

            // Gate 6: Select shallowest timed-out leaf (Algorithm 4, line 10)
            // Paper: globally select shallowest leaf
            // Z3 limitation: check if `n` IS the shallowest (we can only expand it)
            unsigned shallowest_timed_out_leaf_depth = UINT_MAX;
            find_shallowest_timed_out_leaf_depth(m_root.get(), shallowest_timed_out_leaf_depth);
            
            // Only expand if `n` is a shallowest timed-out leaf
            bool is_timed_out_leaf = n->is_leaf() && n->effort_spent() > 0;
            return is_timed_out_leaf && 
                   n->depth() == shallowest_timed_out_leaf_depth;
        }

        unsigned count_active_nodes(node<Config>* cur) const {
            if (!cur || cur->get_status() == status::closed)
                return 0;
            return (cur->get_status() == status::active ? 1 : 0) +
                   count_active_nodes(cur->left()) +
                   count_active_nodes(cur->right());
        }

        // Bubble to the highest ancestor where ALL literals in the resolvent
        // are present somewhere on the path from that ancestor to root
        node<Config>* find_highest_attach(node<Config>* p, vector<literal> const& resolvent) {
            node<Config>* candidate = p;
            node<Config>* attach_here = p;

            while (candidate) {
                bool all_found = true;

                for (auto const& r : resolvent) {
                    bool found = false;
                    for (node<Config>* q = candidate; q; q = q->parent()) {
                        if (q->get_literal() == r) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        all_found = false;
                        break;
                    }
                }

                if (all_found) {
                    attach_here = candidate;  // bubble up to this node
                }

                candidate = candidate->parent();
            }

            return attach_here;
        }

        // Propagate closure upward via sibling resolution starting at node `cur`.
        // Returns true iff global UNSAT was detected.
        bool propagate_closure_upward(node<Config>* cur) {
            while (true) {
                node<Config>* parent = cur->parent();
                if (!parent)
                    return false;

                auto left  = parent->left();
                auto right = parent->right();
                if (!left || !right)
                    return false;

                if (left->get_status() != status::closed ||
                    right->get_status() != status::closed)
                    return false;

                if (left->get_core().empty() ||
                    right->get_core().empty())
                    return false;

                auto res = compute_sibling_resolvent(left, right);

                if (res.empty()) {
                    close(m_root.get(), res);   // global UNSAT
                    return true;
                }

                close(parent, res);
                cur = parent;  // keep bubbling
            }
        }

        void close(node<Config> *n, vector<literal> const &C) {
            if (!n || n->get_status() == status::closed)
                return;
            n->set_status(status::closed);
            n->set_core(C);
            close(n->left(), C);
            close(n->right(), C);
        }

        // Invariants:
        // Cores labeling nodes are subsets of the literals on the path to the node and the (external) assumption
        // literals. If a parent is open, then the one of the children is open.
        void close_with_core(node<Config> *n, vector<literal> const &C) {
            if (!n)
                return;

            // If the node is closed AND has a stronger or equal core, we are done. 
            // Otherwise, closed nodes may still accept a different (stronger) core to enable pruning/resolution higher in the tree.
            auto subseteq = [](vector<literal> const& A, vector<literal> const& B) {
                return all_of(A, [&](auto const &a) { return B.contains(a); });
            };
            if (n->get_status() == status::closed && subseteq(n->get_core(), C))
                return;

            node<Config> *p = n->parent();

            // The conflict does NOT depend on the decision literal at node n, so n’s split literal is irrelevant to this conflict
            // thus the entire subtree under n is closed regardless of the split, so the conflict should be attached higher, at the nearest ancestor that does participate
            if (p && all_of(C, [n](auto const &l) { return l != n->get_literal(); })) {
                close_with_core(p, C);
                return;
            }
            
            // Close descendants WITHOUT resolving
            close(n, C);

            if (!p)
                return;
            auto left = p->left();
            auto right = p->right();
            if (!left || !right)
                return;

            // only attempt when both children are closed and each has a *non-empty* core
            if (left->get_status() != status::closed || right->get_status() != status::closed) return;
            if (left->get_core().empty() || right->get_core().empty()) return;

            auto resolvent = compute_sibling_resolvent(left, right);
            if (resolvent.empty()) { // empty resolvent => global UNSAT
                close(m_root.get(), resolvent);
                return;
            }

            auto attach = find_highest_attach(p, resolvent);
            close(attach, resolvent);

            // try to propagate the highest attach node upward *with sibling resolution*
            // this handles the case when non-chronological backjumping takes us to a node whose sibling was closed by another thread
            node<Config>* cur = attach;
            propagate_closure_upward(cur);
        }

        // Given complementary sibling nodes for literals x and ¬x, sibling resolvent = (core_left ∪ core_right) \ {x,
        // ¬x}
        vector<literal> compute_sibling_resolvent(node<Config> *left, node<Config> *right) {
            vector<literal> res;

            auto &core_l = left->get_core();
            auto &core_r = right->get_core();

            if (core_l.empty() || core_r.empty() || left->parent() != right->parent())
                return res;

            auto lit_l = left->get_literal();
            auto lit_r = right->get_literal();

            for (auto const &lit : core_l)
                if (lit != lit_l && !res.contains(lit))
                    res.push_back(lit);
            for (auto const &lit : core_r)
                if (lit != lit_r && !res.contains(lit))
                    res.push_back(lit);
            return res;
        }

    public:
        tree(literal const &null_literal) : m_null_literal(null_literal) {
            reset();
        }

        void set_seed(unsigned seed) {
            m_rand.set_seed(seed);
        }

        void set_effort_unit(unsigned effort_unit) {
            m_effort_unit = std::max<unsigned>(1, effort_unit);
        }

        void set_num_workers(unsigned num_workers) {
            m_num_workers = std::max<unsigned>(1, num_workers);
        }

        void reset() {
            m_root = alloc(node<Config>, m_null_literal, nullptr);
            m_root->mark_new_activation();
        }

        // On timeout, update effort and decide whether to expand the tree.
        //
        // Paper's semantics (Algorithm 1, line 6 & 16):
        //   1. node.time ← node.time + t  (BEFORE calling TryExpandTree)
        //   2. TryExpandTree(tree, 1)     (operates on tree globally)
        //
        // Z3's constraint:
        //   We only have split literals for the node that just timed out.
        //   So we can only expand `n`, but we still use TryExpandTree's logic
        //   to decide WHETHER to expand based on global tree state.
        //
        // Parameters:
        //   n - the node that just timed out
        //   a, b - the split literals for node n
        //   effort - time/conflicts spent (added to node.time)
        // bool try_split(node<Config> *n, literal const &a, literal const &b) {
        //     if (!n || n->get_status() != status::active)
        //         return false;
            
        //     // Decide whether to expand the tree (paper's Algorithm 4 logic)
        //     // Note: Paper would globally select shallowest leaf, but we can only expand `n`
        //     // because we only have split literals for it. However, we still check:
        //     //   1. If n is a valid expansion candidate (is it shallowest?)
        //     //   2. If tree-wide expansion conditions are met
        //     bool should_expand = should_split(n);
        //     if (should_expand) {
        //         n->split(a, b);
        //     } 
        //     if (n->active_workers() == 0)
        //         n->set_status(status::open);
            
        //     return should_expand;
        // }

        bool try_split(node<Config> *n, literal const &a, literal const &b) {
            if (!n || n->get_status() != status::active)
                return false;
            if (should_split(n)) {
                n->split(a, b);
                return true;
            } else {
                n->set_status(status::open);
            }
            return false;
        }

        // conflict is given by a set of literals.
        // they are subsets of the literals on the path from root to n AND the external assumption literals
        void backtrack(node<Config> *n, vector<literal> const &conflict) {
            if (conflict.empty()) {
                close_with_core(m_root.get(), conflict);
                return;
            }
            SASSERT(n != m_root.get());
            // all literals in conflict are on the path from root to n
            // remove assumptions from conflict to ensure this.
            DEBUG_CODE(auto on_path =
                           [&](literal const &a) {
                               node<Config> *p = n;
                               while (p) {
                                   if (p->get_literal() == a)
                                       return true;
                                   p = p->parent();
                               }
                               return false;
                           };
                       SASSERT(all_of(conflict, [&](auto const &a) { return on_path(a); })););

            // Walk upward to find the nearest ancestor whose decision participates in the conflict
            while (n) {
                if (any_of(conflict, [&](auto const &a) { return a == n->get_literal(); })) {
                    // close the subtree under n (preserves core attached to n), and attempt to resolve upwards
                    close_with_core(n, conflict);
                    return;
                }

                n = n->parent();
            }
            UNREACHABLE();
        }

        // return an active node in the tree, or nullptr if there is none
        // first check if there is a node to activate under n,
        // if not, go up the tree and try to activate a sibling subtree
        node<Config> *activate_node(node<Config> *n) {
            if (!n) {
                if (m_root->get_status() == status::active) {
                    m_root->mark_new_activation();
                    return m_root.get();
                }
            }
            return activate_best_node();
        }

        vector<literal> const &get_core_from_root() const {
            return m_root->get_core();
        }

        bool is_closed() const {
            return m_root->get_status() == status::closed;
        }

        std::ostream &display(std::ostream &out) const {
            m_root->display(out, 0);
            return out;
        }
    };
}  // namespace search_tree
