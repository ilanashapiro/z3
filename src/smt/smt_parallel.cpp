/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_parallel.cpp

Abstract:

    Parallel SMT, portfolio loop specialized to SMT core.

Author:

    nbjorner 2020-01-31
    Ilana Shapiro 2025

--*/

#include "util/scoped_ptr_vector.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_translation.h"
#include "ast/for_each_expr.h"
#include "ast/simplifiers/then_simplifier.h"
#include "smt/smt_parallel.h"
#include "smt/smt_lookahead.h"
#include "solver/solver_preprocess.h"
#include "params/smt_parallel_params.hpp"

#include <cmath>
#include <mutex>

class bounded_pp_exprs {
    expr_ref_vector const &es;

public:
    bounded_pp_exprs(expr_ref_vector const &es) : es(es) {}

    std::ostream &display(std::ostream &out) const {
        for (auto e : es)
            out << mk_bounded_pp(e, es.get_manager()) << "\n";
        return out;
    }
};

inline std::ostream &operator<<(std::ostream &out, bounded_pp_exprs const &pp) {
    return pp.display(out);
}

#ifdef SINGLE_THREAD

namespace smt {

    lbool parallel::operator()(expr_ref_vector const &asms) {
        return l_undef;
    }
}  // namespace smt

#else

#include <thread>

#define LOG_WORKER(lvl, s) IF_VERBOSE(lvl, verbose_stream() << "Worker " << id << s)

namespace smt {

    static unsigned clause_num_literals(ast_manager& m, expr* e) {
        if (m.is_or(e))
            return to_app(e)->get_num_args();
        return 1;
    }

    void parallel::sls_worker::run() {
        ptr_vector<expr> assertions;
        p.ctx.get_assertions(assertions);
        for (expr* e : assertions)
            m_sls->assert_expr(m_g2l(e));

        lbool res = l_undef;
        try {
            if (!m.inc())
                return;
            res = m_sls->check();
        } 
        catch (z3_exception& ex) {
            // Cancellation is normal in portfolio mode
            if (m.limit().is_canceled()) {
                IF_VERBOSE(1, verbose_stream() << "SLS worker canceled\n");
                return;
            }

            if (strstr(ex.what(), "unsupported for sls") != nullptr) {
                IF_VERBOSE(1, verbose_stream() << "SLS opted out: " << ex.what() << "\n");
                return;
            }

            // Anything else is a real error
            IF_VERBOSE(1, verbose_stream() << "SLS threw exception: " << ex.what() << "\n");
            b.set_exception(ex.what());
            return;
        }

        if (res == l_true) {         
            IF_VERBOSE(2, verbose_stream() << "SLS worker found SAT\n");
            model_ref mdl = m_sls->get_model();
            b.set_sat(m_l2g, *mdl);
        }
    }

    void parallel::sls_worker::cancel() {
        IF_VERBOSE(1, verbose_stream() << " SLS WORKER cancelling\n");
        m.limit().cancel();
    }

    void parallel::sls_worker::collect_statistics(::statistics &st) const {
        m_sls->collect_statistics(st);
    }

    void parallel::worker::run() {
        search_tree::node<cube_config> *node = nullptr;
        expr_ref_vector cube(m);
        while (true) {

            if (!b.get_cube(m_g2l, id, cube, node)) {
                LOG_WORKER(1, " no more cubes\n");
                return;
            }
            collect_shared_clauses(node);

        check_cube_start:
            LOG_WORKER(1, " CUBE SIZE IN MAIN LOOP: " << cube.size() << "\n");
            lbool r = check_cube(cube, node);

            if (!m.inc()) {
                b.set_exception("context cancelled");
                return;
            }

            switch (r) {
            case l_undef: {
                update_max_thread_conflicts();
                LOG_WORKER(1, " found undef cube\n");
                if (m_config.m_max_cube_depth <= cube.size())
                    goto check_cube_start;

                auto atom = get_split_atom();
                if (!atom)
                    goto check_cube_start;
                b.try_split(m_l2g, id, node, atom, m_config.m_threads_max_conflicts);
                simplify();
                break;
            }
            case l_true: {
                LOG_WORKER(1, " found sat cube\n");
                model_ref mdl;
                ctx->get_model(mdl);
                b.set_sat(m_l2g, *mdl);
                return;
            }
            case l_false: {
                expr_ref_vector const &unsat_core = ctx->unsat_core();
                LOG_WORKER(2, " unsat core:\n";
                           for (auto c : unsat_core) verbose_stream() << mk_bounded_pp(c, m, 3) << "\n");
                // If the unsat core only contains original (external) assumptions,
                // then UNSAT does not depend on the cube → global UNSAT.
                //
                // If the UNSAT core contains:
                //   - cube literals → conflict depends on the cube
                //   - guards        → conflict depends on subtree-scoped clauses → also cube-dependent
                //
                // check_asms = [ original assumptions | cube literals | guard switches ]
                //
                // For global UNSAT, the core must contain ONLY original assumptions.
                bool is_global_unsat = all_of(unsat_core, [&](expr* e) {
                    // must be an original assumption (not cube literal, not guard)
                    if (!asms.contains(e))
                        return false;

                    // must NOT be a guard (guards are control variables, not logical assumptions)
                    search_tree::node<cube_config>* tmp = nullptr;
                    if (is_guard(e, tmp))
                        return false;

                    return true;
                });

                if (is_global_unsat) {
                    LOG_WORKER(1, " determined formula unsat\n");
                    b.set_unsat(m_l2g, unsat_core);
                    return;
                }

                expr_ref_vector tree_core(m);
                extract_tree_core(unsat_core, tree_core);
                LOG_WORKER(1, " found unsat cube\n");
                b.backtrack(m_l2g, tree_core, node);

                auto* conflict_scope = b.current_scope(m_l2g, node, tree_core);

                if (m_config.m_share_conflicts)
                    b.collect_clause(m_l2g, id, conflict_scope, mk_not(mk_and(tree_core)));

                share_lemmas(conflict_scope);

                break;
            }
            }
            if (m_config.m_share_units)
                share_units(node);
        }
    }

    parallel::worker::worker(unsigned id, parallel &p, expr_ref_vector const &_asms)
        : id(id), p(p), b(p.m_batch_manager), asms(m), m_active_clause_guards(m),
          m_emitted_learned_clause_roots(m), m_smt_params(p.ctx.get_fparams()), m_g2l(p.ctx.m, m),
          m_l2g(m, p.ctx.m) {
        for (auto e : _asms)
            asms.push_back(m_g2l(e));
        LOG_WORKER(1, " created with " << asms.size() << " assumptions\n");
        m_smt_params.m_random_seed += id;  // ensure different random seed for each worker
        ctx = alloc(context, m, m_smt_params, p.ctx.get_params());
        ctx->set_logic(p.ctx.m_setup.get_logic());
        context::copy(p.ctx, *ctx, true);
        // don't share initial units
        ctx->pop_to_base_lvl();
        m_num_shared_units = ctx->assigned_literals().size();
        m_num_initial_atoms = ctx->get_num_bool_vars();
        ctx->get_fparams().m_preprocess = false;  // avoid preprocessing lemmas that are exchanged

        smt_parallel_params pp(p.ctx.m_params);
        m_config.m_inprocessing = pp.inprocessing();
    }

    // Return a Boolean "guard" literal associated with a search-tree node.
    // Guards are fresh Boolean constants used to *label* clauses coming from a node,
    // so that if such a clause participates in an UNSAT core, we can map it back
    // to the originating node (scope) in the search tree.
    expr_ref parallel::worker::get_or_create_guard(node* n) {
        // Check if we already created a guard for this node.
        auto it = m_node_guards.find(n);
        if (it != m_node_guards.end())
            return it->second;

        // Otherwise create a fresh Boolean constant named "pshare".
        // (mk_fresh_const ensures uniqueness even with same base name)
        symbol name(symbol("pshare"));
        expr_ref g(m.mk_fresh_const(name, m.mk_bool_sort()), m);

        // Store bidirectional mappings:
        // node -> guard
        m_node_guards.emplace(n, g);
        // guard -> node
        m_guard_to_node.insert(g, n);

        return g;
    }

    // Check whether expression `e` is a guard literal.
    // If yes, return true and output the associated node in `n`.
    bool parallel::worker::is_guard(expr* e, node*& n) const {
        return m_guard_to_node.find(e, n);
    }

    // Extract a "tree core" from the solver's UNSAT core.
    // The goal is to translate the UNSAT core (which may include guards)
    // into a set of literals that correspond to the search tree,
    // so batch_manager::backtrack can operate correctly.
    void parallel::worker::extract_tree_core(expr_ref_vector const& unsat_core,
                                            expr_ref_vector& tree_core) {
        tree_core.reset();

        for (expr* e : unsat_core) {

            // Skip original assumptions.
            // These indicate global UNSAT and should not contribute to tree backtracking.
            if (asms.contains(e))
                continue;

            node* scope = nullptr;

            // Case 1: e is a guard literal.
            if (is_guard(e, scope)) {

                // Guards encode "this clause came from node `scope`".
                // So we translate the guard back into the node's branching literal.
                if (scope && !cube_config::literal_is_null(scope->get_literal())) {

                    // Convert the node's literal from global → local context.
                    expr_ref lit(m_g2l(scope->get_literal().get()), m);

                    // Add it to the tree core if not already present.
                    if (!tree_core.contains(lit))
                        tree_core.push_back(lit);
                }

                // Do NOT include the guard itself in the core.
                continue;
            }

            // Case 2: e is a regular literal (not an assumption, not a guard).
            // This can happen if the solver returns theory literals or derived atoms.
            // We include them directly in the tree core.
            if (!tree_core.contains(e))
                tree_core.push_back(e);
        }
    }

    expr_ref parallel::worker::mk_clause_expr(clause const& cls) {
        expr_ref result(m);
        expr_ref_vector lits(m);
        for (unsigned i = 0; i < cls.get_num_literals(); ++i)
            lits.push_back(ctx->literal2expr(cls.get_literal(i)));
        if (lits.empty())
            return result;
        result = lits.size() == 1 ? lits[0].get() : m.mk_or(lits);
        return result;
    }

    parallel::sls_worker::sls_worker(parallel& p)
        : p(p), b(p.m_batch_manager), m(), m_g2l(p.ctx.m, m), m_l2g(m, p.ctx.m) {
        IF_VERBOSE(1, verbose_stream() << "Initialized SLS portfolio thread\n");
        m_params.append(p.ctx.m_params);
        m_sls = alloc(sls::smt_solver, m, m_params);
    }

    void parallel::worker::share_units(node* current_node) {
        // Collect new units learned locally by this worker and send to batch manager
        
        unsigned sz = ctx->assigned_literals().size();
        for (unsigned j = m_num_shared_units; j < sz; ++j) {  // iterate only over new literals since last sync
            literal lit = ctx->assigned_literals()[j];

            // filter by assign level: do not pop to base level as this destroys the current search state
            if (ctx->get_assign_level(lit) > ctx->m_base_lvl)
                continue;

            if (!ctx->is_relevant(lit.var()) && m_config.m_share_units_relevant_only)
                continue;

            if (m_config.m_share_units_initial_only && lit.var() >= m_num_initial_atoms) {
                LOG_WORKER(4, " Skipping non-initial unit: " << lit.var() << "\n");
                continue;  // skip non-initial atoms if configured to do so
            }

            expr_ref e(ctx->bool_var2expr(lit.var()), ctx->m);  // turn literal into a Boolean expression
            if (m.is_and(e) || m.is_or(e))
                continue;

            if (lit.sign())
                e = m.mk_not(e);  // negate if literal is negative
            
            // Use current_node instead of nullptr to properly scope the unit
            b.collect_clause(m_l2g, id, current_node, e);
        }
        m_num_shared_units = sz;
    }

    void parallel::worker::share_lemmas(node* conflict_scope) {
        unsigned min_activity = std::max(2u, ctx->get_lemma_avg_activity());
        for (clause* cls : ctx->get_lemmas()) {
            if (!cls || !cls->is_learned())
                continue;
            if (cls->get_activity() < min_activity)
                continue;

            expr_ref_vector payload(m);
            node* valid_at = nullptr;
            bool original_atoms_only = true;
            for (unsigned i = 0; i < cls->get_num_literals(); ++i) {
                literal lit = cls->get_literal(i);
                expr* atom = ctx->bool_var2expr(lit.var());
                if (!atom) {
                    original_atoms_only = false;
                    break;
                }

                node* scope = nullptr;
                if (is_guard(atom, scope)) {
                    if (!lit.sign() || !scope) {
                        original_atoms_only = false;
                        break;
                    }
                    if (!valid_at || search_tree::tree<cube_config>::is_ancestor(valid_at, scope)) {
                        valid_at = scope;
                    }
                    else if (!search_tree::tree<cube_config>::is_ancestor(scope, valid_at)) {
                        original_atoms_only = false;
                        break;
                    }
                    continue;
                }

                if (lit.var() >= m_num_initial_atoms) {
                    original_atoms_only = false;
                    break;
                }
                payload.push_back(ctx->literal2expr(lit));
            }
            if (!original_atoms_only || payload.empty() || payload.size() > 3)
                continue;

            if (conflict_scope) {
                if (!valid_at) {
                    valid_at = conflict_scope;
                }
                else if (search_tree::tree<cube_config>::is_ancestor(valid_at, conflict_scope)) {
                    valid_at = conflict_scope;
                }
                else if (!search_tree::tree<cube_config>::is_ancestor(conflict_scope, valid_at)) {
                    continue;
                }
            }

            expr_ref clause_expr(payload.size() == 1 ? payload[0].get() : m.mk_or(payload), m);
            if (!clause_expr)
                continue;

            node* old_scope = nullptr;
            if (m_emitted_learned_clause_scope.find(clause_expr.get(), old_scope) &&
                (old_scope == valid_at || (old_scope && valid_at && search_tree::tree<cube_config>::is_ancestor(old_scope, valid_at))))
                continue;

            m_emitted_learned_clause_roots.push_back(clause_expr);
            m_emitted_learned_clause_scope.insert(clause_expr.get(), valid_at);
            b.collect_clause(m_l2g, id, valid_at, clause_expr);
        }
    }

    void parallel::worker::simplify() {
        if (!m.inc())
            return;
        // first attempt: one-shot simplification of the context.
        // a precise schedule of repeated simplification is TBD.
        // also, the in-processing simplifier should be applied to
        // a current set of irredundant clauses that may be reduced by
        // unit propagation. By including the units we are effectively
        // repeating unit propagation, but potentially not subsumption or
        // Boolean simplifications that a solver could perform (smt_context doesnt really)
        // Integration of inprocssing simplifcation here or in sat/smt solver could
        // be based on taking the current clause set instead of the asserted formulas.
        if (!m_config.m_inprocessing)
            return;
        if (m_config.m_inprocessing_delay > 0) {
            --m_config.m_inprocessing_delay;
            return;
        }
        ctx->pop_to_base_lvl();
        if (ctx->m_base_lvl > 0)
            return;                       // simplification only at base level
        m_config.m_inprocessing = false;  // initial strategy is to immediately disable inprocessing for future calls.
        dependent_expr_simplifier *s = ctx->m_simplifier.get();
        if (!s) {
            // create a simplifier if none exists
            // initialize it to a default pre-processing simplifier.
            ctx->m_fmls = alloc(base_dependent_expr_state, m);
            auto then_s = alloc(then_simplifier, m, ctx->get_params(), *ctx->m_fmls);
            s = then_s;
            ctx->m_simplifier = s;
            init_preprocess(m, ctx->get_params(), *then_s, *ctx->m_fmls);
        }

        dependent_expr_state &fmls = *ctx->m_fmls.get();
        // extract assertions from ctx.
        // it is possible to track proof objects here if wanted.
        // feed them to the simplifier
        ptr_vector<expr> assertions;
        expr_ref_vector units(m);
        ctx->get_assertions(assertions);
        ctx->get_units(units);
        for (expr *e : assertions)
            fmls.add(dependent_expr(m, e, nullptr, nullptr));
        for (expr *e : units)
            fmls.add(dependent_expr(m, e, nullptr, nullptr));

        // run in-processing on the assertions
        s->reduce();

        scoped_ptr<context> new_ctx = alloc(context, m, m_smt_params, p.ctx.get_params());
        // extract simplified assertions from the simplifier
        // create a new context with the simplified assertions
        // update ctx with the new context.
        for (unsigned i = 0; i < fmls.qtail(); ++i) {
            auto const &de = fmls[i];
            new_ctx->assert_expr(de.fml());
        }

        asserted_formulas &src_af = ctx->m_asserted_formulas;
        asserted_formulas &dst_af = new_ctx->m_asserted_formulas;
        src_af.get_macro_manager().copy_to(dst_af.get_macro_manager());
        new_ctx->copy_user_propagator(*ctx, true);
        ctx = new_ctx.detach();
        ctx->setup_context(true);
        ctx->internalize_assertions();
        auto old_atoms = m_num_initial_atoms;
        m_num_shared_units = ctx->assigned_literals().size();
        m_num_initial_atoms = ctx->get_num_bool_vars();
        LOG_WORKER(1, " inprocess " << old_atoms << " -> " << m_num_initial_atoms << "\n");
    }

    void parallel::worker::collect_statistics(::statistics &st) const {
        ctx->collect_statistics(st);
    }

    void parallel::worker::cancel() {
        LOG_WORKER(1, " canceling\n");
        m.limit().cancel();
    }

    void parallel::batch_manager::backtrack(ast_translation &l2g, expr_ref_vector const &core,
                                            search_tree::node<cube_config> *node) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager backtracking.\n");
        if (m_state != state::is_running)
            return;
        vector<cube_config::literal> g_core;
        for (auto c : core) {
            expr_ref g_c(l2g(c), m);
            g_core.push_back(expr_ref(l2g(c), m));
        }
        m_search_tree.backtrack(node, g_core);

        IF_VERBOSE(1, m_search_tree.display(verbose_stream() << bounded_pp_exprs(core) << "\n"););
        if (m_search_tree.is_closed()) {
            IF_VERBOSE(1, verbose_stream() << "Search tree closed, setting UNSAT\n");
            m_state = state::is_unsat;
            SASSERT(p.ctx.m_unsat_core.empty());
            for (auto e : m_search_tree.get_core_from_root())
               p.ctx.m_unsat_core.push_back(e);
            cancel_background_threads();
        }
    }

    void parallel::batch_manager::try_split(ast_translation &l2g, unsigned source_worker_id,
                                        search_tree::node<cube_config> *node, expr *atom, unsigned effort) {
        std::scoped_lock lock(mux);
        expr_ref lit(m), nlit(m);
        lit = l2g(atom);
        nlit = mk_not(m, lit);
        
        if (m_state != state::is_running)
            return;

        bool did_split = m_search_tree.try_split(node, lit, nlit, effort);

        if (did_split) {
            ++m_stats.m_num_cubes;
            m_stats.m_max_cube_depth = std::max(m_stats.m_max_cube_depth, node->depth() + 1);
            IF_VERBOSE(1, verbose_stream() << "Batch manager splitting on literal: " << mk_bounded_pp(lit, m, 3) << "\n");
        }
    }

    parallel::batch_manager::node* parallel::batch_manager::current_scope(ast_translation& l2g, node* n, expr_ref_vector const& core) const {
        if (!n || core.empty())
            return nullptr;
        vector<cube_config::literal> g_core;
        for (auto* c : core)
            g_core.push_back(expr_ref(l2g(c), m));
        return m_search_tree.deepest_cover(n, g_core);
    }

    void parallel::batch_manager::collect_clause(ast_translation &l2g, unsigned source_worker_id, node* valid_at, expr *clause) {
        std::scoped_lock lock(mux);
        expr *g_clause = l2g(clause);
        if (!g_clause)
            return;

        unsigned clause_size = clause_num_literals(m, g_clause);
        unsigned term_size = get_num_exprs(g_clause);
        bool is_unit = clause_size == 1;

        if (!is_unit && clause_size > 8)
            return;
        if (term_size > 64)
            return;

        unsigned idx = 0;
        if (shared_clause_index.find(g_clause, idx)) {
            auto& sc = shared_clause_db[idx];
            ++sc.score;
            if (!valid_at || (sc.valid_at && search_tree::tree<cube_config>::is_ancestor(valid_at, sc.valid_at)))
                sc.valid_at = valid_at;
            sc.root_valid = sc.valid_at == nullptr;
            return;
        }
        idx = shared_clause_db.size();
        shared_clause_index.insert(g_clause, idx);
        shared_clause sc(m);
        sc.id = idx;
        sc.source_worker_id = source_worker_id;
        sc.clause = expr_ref(g_clause, m);
        sc.valid_at = valid_at;
        sc.score = 1;
        sc.clause_size = clause_size;
        sc.term_size = term_size;
        sc.is_unit = is_unit;
        sc.root_valid = valid_at == nullptr;
        shared_clause_db.push_back(sc);
    }

    void parallel::worker::collect_shared_clauses(node* current_node) {
        vector<local_shared_clause> fresh;
        b.return_shared_clauses(m_g2l, id, current_node, m_known_shared_clause_ids, fresh);
        for (auto& sc : fresh) {
            if (m_known_shared_clause_ids.contains(sc.id))
                continue;
            m_known_shared_clause_ids.insert(sc.id);
            if (sc.root_valid) {
                ctx->assert_expr(sc.clause);
            }
            else {
                sc.guard = get_or_create_guard(sc.valid_at);
                expr_ref guarded(m.mk_or(m.mk_not(sc.guard), sc.clause), m);
                ctx->assert_expr(guarded);
            }
            m_shared_clauses.push_back(sc);
            LOG_WORKER(4, " caching shared clause: " << mk_bounded_pp(sc.clause, m, 3) << "\n");
        }
    }

    void parallel::worker::append_active_clause_guards(node* current_node, expr_ref_vector& target) {
        for (auto const& sc : m_shared_clauses) {
            if (sc.root_valid)
                continue;
            if (!search_tree::tree<cube_config>::is_ancestor(sc.valid_at, current_node))
                continue;
            if (!target.contains(sc.guard))
                target.push_back(sc.guard);
        }
    }

    void parallel::batch_manager::return_shared_clauses(ast_translation &g2l, unsigned worker_id, node* current_node,
                                                        uint_set const& known_ids, vector<local_shared_clause>& result) {
        std::scoped_lock lock(mux);
        svector<unsigned> candidates;
        for (unsigned i = 0; i < shared_clause_db.size(); ++i) {
            auto const& sc = shared_clause_db[i];
            if (sc.source_worker_id == worker_id || known_ids.contains(sc.id))
                continue;
            if (!sc.root_valid && !search_tree::tree<cube_config>::is_ancestor(sc.valid_at, current_node))
                continue;
            candidates.push_back(i);
        }
        std::stable_sort(candidates.begin(), candidates.end(), [&](unsigned i, unsigned j) {
            auto const& a = shared_clause_db[i];
            auto const& b = shared_clause_db[j];
            if (a.is_unit != b.is_unit)
                return a.is_unit;
            if (a.score != b.score)
                return a.score > b.score;
            if (a.clause_size != b.clause_size)
                return a.clause_size < b.clause_size;
            if (a.term_size != b.term_size)
                return a.term_size < b.term_size;
            unsigned da = a.valid_at ? a.valid_at->depth() : 0;
            unsigned db = b.valid_at ? b.valid_at->depth() : 0;
            return da > db;
        });
        unsigned limit = 32;
        for (unsigned i = 0; i < candidates.size() && i < limit; ++i) {
            auto const& sc = shared_clause_db[candidates[i]];
            local_shared_clause lc(g2l.to());
            lc.id = sc.id;
            lc.clause = expr_ref(g2l(sc.clause.get()), g2l.to());
            lc.valid_at = sc.valid_at;
            lc.score = sc.score;
            lc.root_valid = sc.root_valid;
            result.push_back(lc);
        }
    }

    lbool parallel::worker::check_cube(expr_ref_vector const &cube, node* current_node) {
        expr_ref_vector check_asms(m);
        check_asms.append(asms);
        for (auto &atom : cube)
            check_asms.push_back(atom);

        m_active_clause_guards.reset();
        append_active_clause_guards(current_node, m_active_clause_guards);
        check_asms.append(m_active_clause_guards);
        lbool r = l_undef;

        ctx->get_fparams().m_max_conflicts = std::min(m_config.m_threads_max_conflicts, m_config.m_max_conflicts);
        IF_VERBOSE(1, verbose_stream() << " Checking cube\n"
                                       << bounded_pp_exprs(cube)
                                       << "with max_conflicts: " << ctx->get_fparams().m_max_conflicts << "\n";);
        try {
            r = ctx->check(check_asms.size(), check_asms.data());
        } catch (z3_error &err) {
            b.set_exception(err.error_code());
        } catch (z3_exception &ex) {
            b.set_exception(ex.what());
        } catch (...) {
            b.set_exception("unknown exception");
        }
        LOG_WORKER(1, " DONE checking cube " << r << "\n";);
        return r;
    }

    expr_ref parallel::worker::get_split_atom() {
        expr_ref result(m);
        double score = 0;
        unsigned n = 0;
        ctx->pop_to_search_lvl();
        for (bool_var v = 0; v < ctx->get_num_bool_vars(); ++v) {
            if (ctx->get_assignment(v) != l_undef)
                continue;
            expr *e = ctx->bool_var2expr(v);
            if (!e)
                continue;

            double new_score = ctx->m_lit_scores[0][v] * ctx->m_lit_scores[1][v];

            ctx->m_lit_scores[0][v] /= 2;
            ctx->m_lit_scores[1][v] /= 2;

            if (new_score > score || !result || (new_score == score && m_rand(++n) == 0)) {
                score = new_score;
                result = e;
            }
        }
        return result;
    }

    void parallel::batch_manager::set_sat(ast_translation &l2g, model &m) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager setting SAT.\n");
        if (m_state != state::is_running)
            return;
        m_state = state::is_sat;
        p.ctx.set_model(m.translate(l2g));
        cancel_background_threads();
    }

    void parallel::batch_manager::set_unsat(ast_translation &l2g, expr_ref_vector const &unsat_core) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager setting UNSAT.\n");
        if (m_state != state::is_running)
            return;
        m_state = state::is_unsat;

        // each call to check_sat needs to have a fresh unsat core
        SASSERT(p.ctx.m_unsat_core.empty());
        for (expr *e : unsat_core)
            p.ctx.m_unsat_core.push_back(l2g(e));
        cancel_background_threads();
    }

    void parallel::batch_manager::set_exception(unsigned error_code) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager setting exception code: " << error_code << ".\n");
        if (m_state != state::is_running)
            return;
        m_state = state::is_exception_code;
        m_exception_code = error_code;
        cancel_background_threads();
    }

    void parallel::batch_manager::set_exception(std::string const &msg) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager setting exception msg: " << msg << ".\n");
        if (m_state != state::is_running)
            return;
        m_state = state::is_exception_msg;
        m_exception_msg = msg;
        cancel_background_threads();
    }

    lbool parallel::batch_manager::get_result() const {
        if (m.limit().is_canceled())
            return l_undef;  // the main context was cancelled, so we return undef.
        switch (m_state) {
        case state::is_running:  // batch manager is still running, but all threads have processed their cubes, which
                                 // means all cubes were unsat
            throw default_exception("inconsistent end state");
        case state::is_unsat:
            return l_false;
        case state::is_sat:
            return l_true;
        case state::is_exception_msg:
            throw default_exception(m_exception_msg.c_str());
        case state::is_exception_code:
            throw z3_error(m_exception_code);
        default:
            UNREACHABLE();
            return l_undef;
        }
    }

    bool parallel::batch_manager::get_cube(ast_translation &g2l, unsigned id, expr_ref_vector &cube, node *&n) {
        cube.reset();
        std::unique_lock<std::mutex> lock(mux);
        if (m_search_tree.is_closed()) {
            IF_VERBOSE(1, verbose_stream() << "all done\n";);
            return false;
        }
        if (m_state != state::is_running) {
            IF_VERBOSE(1, verbose_stream() << "aborting get_cube\n";);
            return false;
        }
        node *t = m_search_tree.activate_node(n);
        if (!t)
            return false;
        IF_VERBOSE(1, m_search_tree.display(verbose_stream()); verbose_stream() << "\n";);
        n = t;
        while (t) {
            if (cube_config::literal_is_null(t->get_literal()))
                break;
            expr_ref lit(g2l.to());
            lit = g2l(t->get_literal().get());
            cube.push_back(std::move(lit));
            t = t->parent();
        }
        return true;
    }

    void parallel::batch_manager::initialize(unsigned initial_max_thread_conflicts) {
        m_state = state::is_running;
        m_search_tree.reset();
        m_search_tree.set_effort_unit(initial_max_thread_conflicts);
    }

    void parallel::batch_manager::collect_statistics(::statistics &st) const {
        st.update("parallel-num_cubes", m_stats.m_num_cubes);
        st.update("parallel-max-cube-size", m_stats.m_max_cube_depth);
    }

    lbool parallel::operator()(expr_ref_vector const &asms) {
        IF_VERBOSE(1, verbose_stream() << "Parallel SMT with " << num_threads << " threads\n";);
        ast_manager &m = ctx.m;

        if (m.has_trace_stream())
            throw default_exception("trace streams have to be off in parallel mode");

        struct scoped_clear {
            parallel &p;
            scoped_clear(parallel &p) : p(p) {}
            ~scoped_clear() {
                p.m_workers.reset();
                p.m_sls_worker = nullptr;
            }
        };
        scoped_clear clear(*this);

        m_batch_manager.initialize();
        m_workers.reset();

        smt_parallel_params pp(ctx.m_params);
        m_should_run_sls = pp.sls();
        
        scoped_limits sl(m.limit());
        flet<unsigned> _nt(ctx.m_fparams.m_threads, 1);
        SASSERT(num_threads > 1);
        for (unsigned i = 0; i < num_threads; ++i)
            m_workers.push_back(alloc(worker, i, *this, asms));
        for (auto w : m_workers)
            sl.push_child(&(w->limit()));
        if (m_should_run_sls) {
            m_sls_worker = alloc(sls_worker, *this);
            sl.push_child(&(m_sls_worker->limit()));
        }

        // Launch threads
        vector<std::thread> threads;
        threads.resize(m_should_run_sls ? num_threads + 1 : num_threads); // +1 for sls worker
        for (unsigned i = 0; i < num_threads; ++i)
            threads[i] = std::thread([&, i]() { m_workers[i]->run(); });
        
        // the final thread runs the sls worker
        if (m_should_run_sls)
            threads[num_threads] = std::thread([&]() { m_sls_worker->run(); });

        // Wait for all threads to finish
        for (auto &th : threads)
            th.join();

        for (auto w : m_workers)
            w->collect_statistics(ctx.m_aux_stats);
        m_batch_manager.collect_statistics(ctx.m_aux_stats);
        if (m_should_run_sls)
            m_sls_worker->collect_statistics(ctx.m_aux_stats);

        return m_batch_manager.get_result();
    }

}  // namespace smt
#endif
