/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_egraph.cpp

Abstract:

    E-graph layer

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-23

Notes:
--*/


#include "ast/euf/euf_egraph.h"
#include "ast/ast_pp.h"
#include "ast/ast_translation.h"

namespace euf {

    enode* egraph::mk_enode(expr* f, unsigned generation, unsigned num_args, enode * const* args) {
        enode* n = enode::mk(m_region, f, generation, num_args, args);
        if (m_default_relevant)
            n->set_relevant(true);
        m_nodes.push_back(n);
        m_exprs.push_back(f);
        if (is_app(f) && num_args > 0) {
           unsigned id = to_app(f)->get_decl()->get_small_id();
           m_decl2enodes.reserve(id+1);
           m_decl2enodes[id].push_back(n);
        }
        m_expr2enode.setx(f->get_id(), n, nullptr);
        push_node(n);
        for (unsigned i = 0; i < num_args; ++i) {
            set_cgc_enabled(args[i], true);      
            args[i]->get_root()->set_is_shared(l_undef);
        }                       
        return n;
    }

    enode* egraph::find(expr* e, unsigned n, enode* const* args) {
        if (m_tmp_node && m_tmp_node_capacity < n) {
            memory::deallocate(m_tmp_node);
            m_tmp_node = nullptr;
        }
        if (!m_tmp_node) {
            m_tmp_node = enode::mk_tmp(n);
            m_tmp_node_capacity = n;
        }
        for (unsigned i = 0; i < n; ++i) 
            m_tmp_node->m_args[i] = args[i];
        m_tmp_node->m_num_args = n;
        m_tmp_node->m_expr = e;
        m_tmp_node->m_table_id = UINT_MAX;
        return m_table.find(m_tmp_node);
    }


    enode_vector const& egraph::enodes_of(func_decl* f) {
        unsigned id = f->get_small_id();
        if (id < m_decl2enodes.size())
            return m_decl2enodes[id];
        return m_empty_enodes;
    }

    enode_bool_pair egraph::insert_table(enode* p) {
        TRACE(euf_verbose, tout << "insert_table " << bpp(p) << "\n");
        //SASSERT(!m_table.contains_ptr(p));
        auto rc = m_table.insert(p);
        p->m_cg = rc.first;
        return rc;
    }

    void egraph::erase_from_table(enode* p) {
        m_table.erase(p);
    }

    void egraph::reinsert_equality(enode* p) {
        SASSERT(p->is_equality());        
        if (p->value() != l_true && p->get_arg(0)->get_root() == p->get_arg(1)->get_root()) {
            queue_literal(p, nullptr);
            if (p->value() == l_false && !m_on_propagate_literal) 
                set_conflict(p->get_arg(0), p->get_arg(1), p->m_lit_justification);
        }
    }

    void egraph::queue_literal(enode* p, enode* ante) {        
        if (m_on_propagate_literal)
            m_to_merge.push_back(to_merge(p, ante));
    }

    void egraph::force_push() {
        if (m_num_scopes == 0)
            return;
        // DEBUG_CODE(invariant(););

        for (; m_num_scopes > 0; --m_num_scopes) {
            m_scopes.push_back(m_updates.size());
            m_region.push_scope();
            m_updates.push_back(update_record(m_new_th_eqs_qhead, update_record::new_th_eq_qhead()));
            for (auto p : m_plugins)
                if (p)
                    p->push_scope_eh();
        }
        SASSERT(m_new_th_eqs_qhead <= m_new_th_eqs.size());
    }

    void egraph::update_children(enode* n) {
        for (enode* child : enode_args(n)) 
            child->get_root()->add_parent(n);
        DEBUG_CODE(for (enode* child : enode_args(n))  
                       SASSERT(child->get_root()->m_parents.back() == n););
        m_updates.push_back(update_record(n, update_record::update_children()));
    }

    enode* egraph::mk(expr* f, unsigned generation, unsigned num_args, enode *const* args) {
        SASSERT(!find(f));
        TRACE(euf, tout << "mk: " << mk_bounded_pp(f, m) << " generation: " << generation << " num_args: " << num_args << "\n";);
        force_push();
        enode *n = mk_enode(f, generation, num_args, args);
        
        SASSERT(n->class_size() == 1);        
        if (num_args == 0 && m.is_unique_value(f))
            n->mark_interpreted();
        if (m_on_make)
            m_on_make(n);
        if (num_args == 0)             
            return n;
        if (m.is_eq(f) && !m.is_iff(f)) {
            n->set_is_equality();
            reinsert_equality(n);
        }
        auto [n2, comm] = insert_table(n);
        if (n2 == n) 
            update_children(n);        
        else 
            push_merge(n, n2, comm);
    
        return n;
    }

    egraph::egraph(ast_manager& m) : m(m), m_table(m), m_tmp_app(2), m_exprs(m), m_eq_decls(m) {
        m_tmp_eq = enode::mk_tmp(m_region, 2);
    }

    egraph::~egraph() {
        for (enode* n : m_nodes) 
            n->m_parents.finalize();
        if (m_tmp_node)
            memory::deallocate(m_tmp_node);
    }

    void egraph::add_plugin(plugin* p) {
        m_plugins.reserve(p->get_id() + 1);
        m_plugins.set(p->get_id(), p);       
    }

    void egraph::propagate_plugins() {
        if (m_plugins.empty())
            return;
        if (m_plugin_qhead < m_new_th_eqs.size())
            m_updates.push_back(update_record(m_plugin_qhead, update_record::plugin_qhead()));

        for (; m_plugin_qhead < m_new_th_eqs.size(); ++m_plugin_qhead) {
            auto const& eq = m_new_th_eqs[m_plugin_qhead];
            auto* p = get_plugin(eq.id());
            if (!p)
                continue;
            if (eq.is_eq()) 
                p->merge_eh(eq.child(), eq.root());            
            else 
                p->diseq_eh(eq.eq());
        }
        for (auto* p : m_plugins)
            if (p)
                p->propagate();        
    }

    void egraph::add_th_eq(theory_id id, theory_var v1, theory_var v2, enode* c, enode* r) {
        TRACE(euf, tout << "eq: " << v1 << " == " << v2 << " - " << bpp(c) << " == " << bpp(r) << "\n";);
        m_new_th_eqs.push_back(th_eq(id, v1, v2, c, r));
        m_updates.push_back(update_record(update_record::new_th_eq()));
        ++m_stats.m_num_th_eqs;
    }

    void egraph::add_th_diseq(theory_id id, theory_var v1, theory_var v2, enode* eq) {
        if (!th_propagates_diseqs(id))
            return;
        TRACE(euf_verbose, tout << "eq: " << v1 << " != " << v2 << "\n";);
        m_new_th_eqs.push_back(th_eq(id, v1, v2, eq));
        m_updates.push_back(update_record(update_record::new_th_eq()));

        ++m_stats.m_num_th_diseqs;
    }
    
    void egraph::add_literal(enode* n, enode* ante) {
        TRACE(euf, tout << "propagate " << bpp(n) << " " << bpp(ante) << "\n");
        if (!m_on_propagate_literal)
            return;
        if (!ante) ++m_stats.m_num_eqs; else ++m_stats.m_num_lits;
        if (!ante)
            m_on_propagate_literal(n, ante);
        else if (m.is_true(ante->get_expr()) || m.is_false(ante->get_expr())) {
            for (enode* k : enode_class(n)) 
                if (k != ante) 
                    m_on_propagate_literal(k, ante);           
        }
        else {
            for (enode* k : enode_class(n)) {
                if (k->value() != ante->value()) 
                    m_on_propagate_literal(k, ante);                
            }
        }
    }

    void egraph::new_diseq(enode* n, void* reason) {
        force_push();
        SASSERT(m.is_eq(n->get_expr()));
        auto j = justification::external(reason);
        auto a = n->get_arg(0), b = n->get_arg(1);
        auto r1 = a->get_root(), r2 = b->get_root();
        if (r1 == r2)
            set_conflict(a, b, j);
        else 
            set_value(n, l_false, j);                
    }

    void egraph::new_diseq(enode* n) {
        SASSERT(n->is_equality());
        SASSERT(n->value() == l_false);
        enode* arg1 = n->get_arg(0), * arg2 = n->get_arg(1);
        enode* r1 = arg1->get_root();
        enode* r2 = arg2->get_root();
        TRACE(euf, tout << "new-diseq:  " << bpp(r1) << " " << bpp(r2) << ": " << r1->has_th_vars() << " " << r2->has_th_vars() << "\n";);
        if (r1 == r2) {
            add_literal(n, nullptr);
            return;
        }
        if (!r1->has_th_vars())
            return;
        if (!r2->has_th_vars())
            return;
        if (r1->has_one_th_var() && r2->has_one_th_var() && r1->get_first_th_id() == r2->get_first_th_id()) {
            theory_id id = r1->get_first_th_id();
            if (!th_propagates_diseqs(id))
                return;
            theory_var v1 = arg1->get_closest_th_var(id);
            theory_var v2 = arg2->get_closest_th_var(id);
            add_th_diseq(id, v1, v2, n);
            return;
        }
        for (auto const& p : euf::enode_th_vars(r1)) {
            if (!th_propagates_diseqs(p.get_id()))
                continue;
            for (auto const& q : euf::enode_th_vars(r2))
                if (p.get_id() == q.get_id()) 
                    add_th_diseq(p.get_id(), p.get_var(), q.get_var(), n);
        }
    }


    /*
    * Propagate disequalities over equality atoms that are assigned to false.
    */

    void egraph::add_th_diseqs(theory_id id, theory_var v1, enode* r) {
        SASSERT(r->is_root());
        if (!th_propagates_diseqs(id))
            return;
        for (enode* p : enode_parents(r)) {
            if (p->is_equality() && p->value() == l_false) {
                enode* n = nullptr;
                n = (r == p->get_arg(0)->get_root()) ? p->get_arg(1) : p->get_arg(0);
                n = n->get_root();
                theory_var v2 = n->get_closest_th_var(id);
                if (v2 != null_theory_var)
                    add_th_diseq(id, v1, v2, p);                        
            }
        }
    }

    void egraph::set_th_propagates_diseqs(theory_id id) {
        m_th_propagates_diseqs.reserve(id + 1, false);
        m_th_propagates_diseqs[id] = true;
    }

    bool egraph::th_propagates_diseqs(theory_id id) const {
        return m_th_propagates_diseqs.get(id, false);
    }

    void egraph::add_th_var(enode* n, theory_var v, theory_id id) {
        force_push();
        theory_var w = n->get_th_var(id);
        enode* r = n->get_root();

        auto* p = get_plugin(id);
        if (p)
            p->register_node(n);

        if (w == null_theory_var) {
            n->add_th_var(v, id, m_region);
            m_updates.push_back(update_record(n, id, update_record::add_th_var()));
            if (r != n) {
                theory_var u = r->get_th_var(id);
                if (u == null_theory_var) {
                    r->add_th_var(v, id, m_region);
                    add_th_diseqs(id, v, r);
                }
                else 
                    add_th_eq(id, v, u, n, r);                
            }
        }
        else {
            theory_var u = r->get_th_var(id);
            SASSERT(u != v && u != null_theory_var);
            n->replace_th_var(v, id);
            m_updates.push_back(update_record(n, id, u, update_record::replace_th_var()));
            add_th_eq(id, v, u, n, r);
        }
    }

    void egraph::register_shared(enode* n, theory_id id) {
        force_push();
        auto* p = get_plugin(id);
        if (p)
            p->register_node(n);
    }

    void egraph::undo_add_th_var(enode* n, theory_id tid) {
        theory_var v = n->get_th_var(tid);
        SASSERT(v != null_theory_var);
        n->del_th_var(tid);
        enode* root = n->get_root();
        if (root != n && root->get_th_var(tid) == v)
            root->del_th_var(tid);
    }

    void egraph::set_merge_tf_enabled(enode* n, bool enable_merge_tf) {
        if (!m.is_bool(n->get_sort()))
            return;
        if (enable_merge_tf != n->merge_tf()) {
            TRACE(euf, tout << "set tf " << enable_merge_tf << " " << bpp(n) << "\n");
            n->set_merge_tf(enable_merge_tf);
            m_updates.push_back(update_record(n, update_record::toggle_merge_tf()));
        }
    }

    void egraph::set_cgc_enabled(enode* n, bool enable_merge) {
        if (enable_merge != n->cgc_enabled()) {
            toggle_cgc_enabled(n, false);
            m_updates.push_back(update_record(n, update_record::toggle_cgc()));
        }
    }

    void egraph::set_relevant(enode* n) {
        if (n->is_relevant())
            return;
        n->set_relevant(true);
        m_updates.push_back(update_record(n, update_record::set_relevant()));
    }

    void egraph::toggle_cgc_enabled(enode* n, bool backtracking) {
       bool enable_merge = !n->cgc_enabled();
       n->set_cgc_enabled(enable_merge);         
       if (n->num_args() > 0) {
           if (enable_merge) {
               auto [n2, comm] = insert_table(n);
               if (n2 != n && !backtracking)
                   m_to_merge.push_back(to_merge(n, n2, comm));
           }
           else if (n->is_cgr())
               erase_from_table(n);
       }
       VERIFY(n->num_args() == 0 || !n->cgc_enabled() || m_table.contains(n));
    }

    void egraph::set_value(enode* n, lbool value, justification j) {  
        if (n->value() == l_undef) {
            force_push();
            TRACE(euf, tout << bpp(n) << " := " << value << "\n";);
            n->set_value(value);
            n->m_lit_justification = j;
            m_updates.push_back(update_record(n, update_record::value_assignment()));
            if (n->is_equality() && n->value() == l_false) 
                new_diseq(n);
        }
    }

    void egraph::set_lbl_hash(enode* n) {
        SASSERT(n->m_lbl_hash == -1);
        // m_lbl_hash should be different from -1, if and only if,
        // there is a pattern that contains the enode. So,
        // I use a trail to restore the value of m_lbl_hash to -1.
        m_updates.push_back(update_record(n, update_record::lbl_hash()));
        unsigned h = hash_u(n->get_expr_id());
        n->m_lbl_hash = h & (APPROX_SET_CAPACITY - 1);
        // propagate modification to the root m_lbls set.
        enode* r = n->get_root();
        approx_set & r_lbls = r->m_lbls;
        if (!r_lbls.may_contain(n->m_lbl_hash)) {
            m_updates.push_back(update_record(r, update_record::lbl_set()));
            r_lbls.insert(n->m_lbl_hash);
        }
    }

    void egraph::pop(unsigned num_scopes) {
        if (num_scopes <= m_num_scopes) {
            m_num_scopes -= num_scopes;
            m_to_merge.reset();
            return;
        }
        num_scopes -= m_num_scopes;
        m_num_scopes = 0;

        unsigned old_lim = m_scopes.size() - num_scopes;
        unsigned num_updates = m_scopes[old_lim];
        auto undo_node = [&]() {
            enode* n = m_nodes.back();
            expr* e = m_exprs.back();
            if (n->num_args() > 0 && n->is_cgr()) 
                erase_from_table(n);
            
            m_expr2enode[e->get_id()] = nullptr;
            n->~enode();
            if (is_app(e) && n->num_args() > 0)
               m_decl2enodes[to_app(e)->get_decl()->get_small_id()].pop_back();
            m_nodes.pop_back();
            m_exprs.pop_back();
        };
        unsigned sz = m_updates.size();
        for (unsigned i = sz; i-- > num_updates; ) {
            auto const& p = m_updates[i];
            switch (p.tag) {
            case update_record::tag_t::is_add_node:
                undo_node();
                break;
            case update_record::tag_t::is_toggle_cgc:
                toggle_cgc_enabled(p.r1, true);
                break;
            case update_record::tag_t::is_toggle_merge_tf:
                p.r1->set_merge_tf(!p.r1->merge_tf());
                break;
            case update_record::tag_t::is_set_parent:
                undo_eq(p.r1, p.n1, p.r2_num_parents);
                break;
            case update_record::tag_t::is_add_th_var:
                undo_add_th_var(p.r1, p.r2_num_parents);
                break;
            case update_record::tag_t::is_replace_th_var:
                SASSERT(p.r1->get_th_var(p.m_th_id) != null_theory_var);
                p.r1->replace_th_var(p.m_old_th_var, p.m_th_id);
                break;
            case update_record::tag_t::is_new_th_eq:
                m_new_th_eqs.pop_back();
                break;
            case update_record::tag_t::is_new_th_eq_qhead:
                m_new_th_eqs_qhead = p.qhead;
                break;
            case update_record::tag_t::is_plugin_qhead:
                m_plugin_qhead = p.qhead;
                break;
            case update_record::tag_t::is_inconsistent:
                m_inconsistent = p.m_inconsistent;
                break;
            case update_record::tag_t::is_value_assignment:
                VERIFY(p.r1->value() != l_undef);
                p.r1->set_value(l_undef);
                break;
            case update_record::tag_t::is_lbl_hash:
                p.r1->m_lbl_hash = p.m_lbl_hash;
                break;
            case update_record::tag_t::is_lbl_set:
                p.r1->m_lbls.set(p.m_lbls);
                break;
            case update_record::tag_t::is_set_relevant:
                SASSERT(p.r1->is_relevant());
                p.r1->set_relevant(false);
                break;
            case update_record::tag_t::is_update_children:
                for (unsigned i = 0; i < p.r1->num_args(); ++i) {
                    CTRACE(euf, (p.r1->m_args[i]->get_root()->m_parents.back() != p.r1),
                           display(tout << bpp(p.r1->m_args[i]) << " " << bpp(p.r1->m_args[i]->get_root()) << " "););
                    SASSERT(p.r1->m_args[i]->get_root()->m_parents.back() == p.r1);
                    p.r1->m_args[i]->get_root()->m_parents.pop_back();
                }
                break;
            case update_record::tag_t::is_plugin_undo:
                m_plugins[p.m_th_id]->undo();
                break;
            default:
                UNREACHABLE();
                break;
            }                    
        }        
        SASSERT(m_updates.size() == sz);
        m_updates.shrink(num_updates);
        m_scopes.shrink(old_lim);        
        m_region.pop_scope(num_scopes);  
        m_to_merge.reset();

        SASSERT(m_new_th_eqs_qhead <= m_new_th_eqs.size());

        // DEBUG_CODE(invariant(););
    }

    void egraph::merge(enode* n1, enode* n2, justification j) {

        if (!n1->cgc_enabled() && !n2->cgc_enabled())
            return;
        SASSERT(n1->get_sort() == n2->get_sort());
        enode* r1 = n1->get_root();
        enode* r2 = n2->get_root();
        if (r1 == r2)
            return;

        TRACE(euf, j.display(tout << "merge: " << bpp(n1) << " == " << bpp(n2) << " ", m_display_justification) << "\n" << bpp(r1) << " " << bpp(r2) << "\n";);
        IF_VERBOSE(20, j.display(verbose_stream() << "merge: " << bpp(n1) << " == " << bpp(n2) << " ", m_display_justification) << "\n";);
        force_push();
        SASSERT(m_num_scopes == 0);
        ++m_stats.m_num_merge;
        if (r1->interpreted() && r2->interpreted()) {
            set_conflict(n1, n2, j);
            return;
        }
        
        if (r1->value() != r2->value() && r1->value() != l_undef && r2->value() != l_undef) {
            SASSERT(m.is_bool(r1->get_expr()));
            set_conflict(n1, n2, j);
            return;
        }
        if (!r2->interpreted() && 
             (r1->class_size() > r2->class_size() || r1->interpreted() || r1->value() != l_undef)) {
            std::swap(r1, r2);
            std::swap(n1, n2);
        }

        remove_parents(r1);
        push_eq(r1, n1, r2->num_parents());
        merge_justification(n1, n2, j);
        for (enode* c : enode_class(n1)) 
            c->m_root = r2;
        std::swap(r1->m_next, r2->m_next);
        r2->inc_class_size(r1->class_size());   
        r2->set_is_shared(l_undef);
        merge_th_eq(r1, r2);
        reinsert_parents(r1, r2);
        if (j.is_congruence() && (m.is_false(r2->get_expr()) || m.is_true(r2->get_expr())))
            add_literal(n1, r2);
        else if (n2->value() != l_undef && n1->value() != n2->value()) 
            add_literal(n1, n2);
        else if (n1->value() != l_undef && n2->value() != n1->value()) 
            add_literal(n2, n1);

        for (auto& cb : m_on_merge)
            cb(r2, r1);
    }

    void egraph::remove_parents(enode* r) {
        TRACE(euf_verbose, tout << bpp(r) << "\n");
        SASSERT(all_of(enode_parents(r), [&](enode* p) { return !p->is_marked1(); }));
        TRACE(euf, tout << "remove_parents " << bpp(r) << "\n");
        for (enode* p : enode_parents(r)) {
            if (p->is_marked1())
                continue;
            if (p->cgc_enabled()) {
                if (!p->is_cgr())
                    continue;
                TRACE(euf, tout << "removing " << m_table.contains_ptr(p) << " " << bpp(p) << "\n");
                SASSERT(m_table.contains_ptr(p));
                p->mark1();
                erase_from_table(p);
                CTRACE(euf, m_table.contains_ptr(p), tout << bpp(p) << "\n"; display(tout));
                SASSERT(!m_table.contains_ptr(p));
            }
            else if (p->is_equality())
                p->mark1();
        }
    }

    void egraph::reinsert_parents(enode* r1, enode* r2) {
        TRACE(euf, tout << "reinsert_parents " << bpp(r1) << " " << bpp(r2) << "\n";);
        for (enode* p : enode_parents(r1)) {
            if (!p->is_marked1())
                continue;
            p->unmark1();
            TRACE(euf, tout << "reinsert " << bpp(r1) << " " << bpp(r2) << " " << bpp(p) << " " << p->cgc_enabled() << "\n";);
            if (p->cgc_enabled()) {
                auto [p_other, comm] = insert_table(p);
                SASSERT(m_table.contains_ptr(p) == (p_other == p));
                CTRACE(euf, p_other != p, tout << "reinsert " << bpp(p) << " == " << bpp(p_other) << " " << p->value() << " " << p_other->value() << "\n");
                if (p_other != p) 
                    m_to_merge.push_back(to_merge(p_other, p, comm));                
                else
                    r2->m_parents.push_back(p);
                if (p->is_equality())
                    reinsert_equality(p);
            }
            else if (p->is_equality()) {
                r2->m_parents.push_back(p);
                reinsert_equality(p);
            }
        }
    }

    void egraph::merge_th_eq(enode* n, enode* root) {
        SASSERT(n != root);
        for (auto const& iv : enode_th_vars(n)) {
            theory_id id = iv.get_id();
            theory_var v = root->get_th_var(id);
            if (v == null_theory_var) {                
                root->add_th_var(iv.get_var(), id, m_region);   
                m_updates.push_back(update_record(root, id, update_record::add_th_var()));
                add_th_diseqs(id, iv.get_var(), root);
            }
            else {
                SASSERT(v != iv.get_var());
                add_th_eq(id, v, iv.get_var(), n, root);
            }
        }
    }

    void egraph::undo_eq(enode* r1, enode* n1, unsigned r2_num_parents) {
        enode* r2 = r1->get_root();
        TRACE(euf_verbose, tout << "undo-eq old-root: " << bpp(r1) << " current-root " << bpp(r2) << " node: " << bpp(n1) << "\n";);
        r2->dec_class_size(r1->class_size());
        r2->set_is_shared(l_undef);
        std::swap(r1->m_next, r2->m_next);
        auto begin = r2->begin_parents() + r2_num_parents, end = r2->end_parents();
        for (auto it = begin; it != end; ++it) {
            enode* p = *it;
            TRACE(euf_verbose, tout << "erase " << bpp(p) << "\n";);
            SASSERT(!p->cgc_enabled() || m_table.contains_ptr(p));
            SASSERT(!p->cgc_enabled() || p->is_cgr());
            if (p->cgc_enabled())
                erase_from_table(p);
        }

        for (enode* c : enode_class(r1))
            c->m_root = r1;

        for (enode* p : enode_parents(r1)) 
            if (p->cgc_enabled() && (p->is_cgr() || !p->congruent(p->m_cg))) 
                insert_table(p);                    
        r2->m_parents.shrink(r2_num_parents);
        unmerge_justification(n1);
    }


    bool egraph::propagate() {
        force_push();
        unsigned i = 0;
        bool change = true;
        while (change) {
            change = false;
            propagate_plugins();
            for (; i < m_to_merge.size() && m.limit().inc() && !inconsistent(); ++i) {
                auto const& w = m_to_merge[i];
                switch (w.t) {
                case to_merge_plain:
                case to_merge_comm:
                    merge(w.a, w.b, justification::congruence(w.commutativity(), m_congruence_timestamp++));
                    break;
                case to_justified:
                    merge(w.a, w.b, w.j);
                    break;
                case to_add_literal:
                    add_literal(w.a, w.b);
                    break;
                }                
            }
        }
        m_to_merge.reset();
        return 
            (m_new_th_eqs_qhead < m_new_th_eqs.size()) ||
            inconsistent();
    }

    void egraph::set_conflict(enode* n1, enode* n2, justification j) {
        ++m_stats.m_num_conflicts;
        if (m_inconsistent)
            return;
        m_inconsistent = true;
        m_updates.push_back(update_record(false, update_record::inconsistent()));
        m_n1 = n1;
        m_n2 = n2;
        TRACE(euf, tout << "conflict " << bpp(n1) << " " << bpp(n2) << " " << j << " " << n1->get_root()->value() << " " << n2->get_root()->value() << "\n");
        m_justification = j;
    }

    void egraph::merge_justification(enode* n1, enode* n2, justification j) {
        SASSERT(!n1->get_root()->m_target);
        SASSERT(!n2->get_root()->m_target);
        SASSERT(n1->reaches(n1->get_root()));
        SASSERT(!n2->reaches(n1->get_root()));
        SASSERT(!n2->reaches(n1));
        n1->reverse_justification();
        n1->m_target = n2;
        n1->m_justification = j;
        SASSERT(n1->acyclic());
        SASSERT(n2->acyclic());
        SASSERT(n1->get_root()->reaches(n1));
        SASSERT(!n2->get_root()->m_target);
        TRACE(euf_verbose, tout << "merge " << n1->get_expr_id() << " " << n2->get_expr_id() << " updates: " << m_updates.size() << "\n";);
    }

    void egraph::unmerge_justification(enode* n1) {
        TRACE(euf_verbose, tout << "unmerge " << n1->get_expr_id() << " " << n1->m_target->get_expr_id() << "\n";);
        // r1 -> ..  -> n1 -> n2 -> ... -> r2
        // where n2 = n1->m_target
        SASSERT(n1->get_root()->reaches(n1));
        SASSERT(n1->m_target);
        n1->m_target        = nullptr;
        n1->m_justification = justification::axiom(null_theory_id);
        n1->get_root()->reverse_justification();
        // ---------------
        // n1 -> ... -> r1
        // n2 -> ... -> r2
        SASSERT(n1->reaches(n1->get_root()));
        SASSERT(!n1->get_root()->m_target);
    }

    bool egraph::are_diseq(enode* a, enode* b) {
        enode* ra = a->get_root(), * rb = b->get_root();
        if (ra == rb)
            return false;
        if (ra->interpreted() && rb->interpreted())
            return true;
        if (ra->get_sort() != rb->get_sort())
            return true;
        enode* r = tmp_eq(ra, rb);
        if (r && r->get_root()->value() == l_false)
            return true;
        return false;
    }

    enode* egraph::get_enode_eq_to(func_decl* f, unsigned num_args, enode* const* args) {
        m_tmp_app.set_decl(f);
        m_tmp_app.set_num_args(num_args);
        return find(m_tmp_app.get_app(), num_args, args);
    }

    enode* egraph::tmp_eq(enode* a, enode* b) {
        SASSERT(a->is_root());
        SASSERT(b->is_root());
        if (a->num_parents() > b->num_parents())
            std::swap(a, b);
        for (enode* p : enode_parents(a))
            if (p->is_equality() && 
                (b == p->get_arg(0)->get_root() || b == p->get_arg(1)->get_root()))
                return p;
        return nullptr;
    }

    /**
       \brief generate an explanation for a congruence.
       Each pair of children under a congruence have the same roots
       and therefore have a least common ancestor. We only need
       explanations up to the least common ancestors.
     */
    void egraph::push_congruence(enode* n1, enode* n2, bool comm) {
        SASSERT(is_app(n1->get_expr()));
        SASSERT(n1->get_decl() == n2->get_decl());
        m_uses_congruence = true;
        if (m_used_cc && !comm) { 
            m_used_cc(n1->get_app(), n2->get_app());
        }
        if (comm && 
            n1->get_arg(0)->get_root() == n2->get_arg(1)->get_root() &&
            n1->get_arg(1)->get_root() == n2->get_arg(0)->get_root()) {
            push_lca(n1->get_arg(0), n2->get_arg(1));
            push_lca(n1->get_arg(1), n2->get_arg(0));
            return;
        }
        TRACE(euf_verbose, tout << bpp(n1) << " " << bpp(n2) << "\n");
            
        for (unsigned i = 0; i < n1->num_args(); ++i) 
            push_lca(n1->get_arg(i), n2->get_arg(i));
    }

    enode* egraph::find_lca(enode* a, enode* b) {
        SASSERT(a->get_root() == b->get_root());
        a->mark2_targets<true>();
        while (!b->is_marked2()) 
            b = b->m_target;
        a->mark2_targets<false>();
        return b;
    }
    
    void egraph::push_to_lca(enode* n, enode* lca) {
        while (n != lca) {
            m_todo.push_back(n);
            n = n->m_target;
        }
    }

    void egraph::push_lca(enode* a, enode* b) {
        enode* lca = find_lca(a, b);
        push_to_lca(a, lca);
        push_to_lca(b, lca);
    }

    void egraph::push_todo(enode* n) {
        while (n) {
            m_todo.push_back(n);
            n = n->m_target;
        }
    }

    void egraph::begin_explain() {
        SASSERT(m_todo.empty());
        m_uses_congruence = false;
        DEBUG_CODE(for (enode* n : m_nodes) SASSERT(!n->is_marked1()););
    }

    void egraph::end_explain() {
        for (enode* n : m_todo) 
            n->unmark1();
        DEBUG_CODE(for (enode* n : m_nodes) SASSERT(!n->is_marked1()););
        m_todo.reset();        
    }

    template <typename T>
    void egraph::explain(ptr_vector<T>& justifications, cc_justification* cc) {
        SASSERT(m_inconsistent);
        push_todo(m_n1);
        push_todo(m_n2);
        explain_eq(justifications, cc, m_n1, m_n2, m_justification);
        explain_todo(justifications, cc);
    }

    template <typename T>
    void egraph::explain_eq(ptr_vector<T>& justifications, cc_justification* cc, enode* a, enode* b, justification const& j) {
        TRACE(euf_verbose, tout << "explain-eq: " << bpp(a) << " == " << bpp(b) << " jst: " << j << "\n";);
        if (j.is_external())
            justifications.push_back(j.ext<T>());
        else if (j.is_congruence()) 
            push_congruence(a, b, j.is_commutative());
        else if (j.is_dependent()) {
            vector<justification, false> js;
            for (auto const& j2 : justification::dependency_manager::s_linearize(j.get_dependency(), js))
                explain_eq(justifications, cc, a, b, j2);
        }
        else if (j.is_equality()) 
            explain_eq(justifications, cc, j.lhs(), j.rhs());
        else if (j.is_axiom() && j.get_theory_id() != null_theory_id) {
            IF_VERBOSE(20, verbose_stream() << "TODO add theory axiom to justification\n");
        }
        if (cc && j.is_congruence()) 
            cc->push_back(std::tuple(a->get_app(), b->get_app(), j.timestamp(), j.is_commutative()));
    }


    template <typename T>
    void egraph::explain_eq(ptr_vector<T>& justifications, cc_justification* cc, enode* a, enode* b) {
        SASSERT(a->get_root() == b->get_root());
        
        enode* lca = find_lca(a, b);
        TRACE(euf_verbose, tout << "explain-eq: " << bpp(a) << " == " << bpp(b) << " lca: " << bpp(lca) << "\n";);
        push_to_lca(a, lca);
        push_to_lca(b, lca);
        if (m_used_eq)
            m_used_eq(a->get_expr(), b->get_expr(), lca->get_expr());
        explain_todo(justifications, cc);
    }

    template <typename T>
    unsigned egraph::explain_diseq(ptr_vector<T>& justifications, cc_justification* cc, enode* a, enode* b) {
        enode* ra = a->get_root(), * rb = b->get_root();
        SASSERT(ra != rb);
        if (ra->interpreted() && rb->interpreted()) {
            explain_eq(justifications, cc, a, ra);
            explain_eq(justifications, cc, b, rb);
            return sat::null_bool_var;
        }
        enode* r = tmp_eq(ra, rb);
        SASSERT(r && r->get_root()->value() == l_false);
        explain_eq(justifications, cc, r, r->get_root());
        return r->get_root()->bool_var();
    }


    template <typename T>
    void egraph::explain_todo(ptr_vector<T>& justifications, cc_justification* cc) {
        for (unsigned i = 0; i < m_todo.size(); ++i) {
            enode* n = m_todo[i];
            if (n->is_marked1())
                continue;
            if (n->m_target) {
                n->mark1();
                CTRACE(euf_verbose, m_display_justification, n->m_justification.display(tout << n->get_expr_id() << " = " << n->m_target->get_expr_id() << " ", m_display_justification) << "\n";);
                explain_eq(justifications, cc, n, n->m_target, n->m_justification);
            }
            else if (!n->is_marked1() && n->value() != l_undef) {
                n->mark1();
                if (m.is_true(n->get_expr()) || m.is_false(n->get_expr()))
                    continue;
                justification j = n->m_lit_justification;
                SASSERT(j.is_external());
                justifications.push_back(j.ext<T>());
            }
        }
    }

    void egraph::invariant() {
        for (enode* n : m_nodes)
            n->invariant(*this);
        for (enode* n : m_nodes)
            if (n->cgc_enabled() && n->num_args() > 0 && (!m_table.find(n) || n->get_root() != m_table.find(n)->get_root())) {
                CTRACE(euf, !m_table.find(n), tout << "node is not in table\n";);
                CTRACE(euf, m_table.find(n), tout << "root " << bpp(n->get_root()) << " table root " << bpp(m_table.find(n)->get_root()) << "\n";);
                TRACE(euf, display(tout << bpp(n) << " is not closed under congruence\n"););
                UNREACHABLE();
            }
    }

    std::ostream& egraph::display(std::ostream& out, unsigned max_args, enode* n) const {
        if (!n->is_relevant())
            out << "n";
        out << "#" << n->get_expr_id() << " := ";
        expr* f = n->get_expr();
        out << mk_bounded_pp(f, m, 1) << " ";
        if (!n->is_root()) 
            out << "[r " << n->get_root()->get_expr_id() << "] ";
        if (!n->m_parents.empty()) {
            out << "[p";
            for (enode* p : enode_parents(n))
                out << " " << p->get_expr_id();
            out << "] ";
        }
        auto value_of = [&]() {
            switch (n->value()) {
            case l_true: return "T";
            case l_false: return "F";
            default: return "?";
            }
        };
        if (n->bool_var() != sat::null_bool_var) 
            out << "[b" << n->bool_var() << " := " << value_of() << (n->cgc_enabled() ? "" : " no-cgc") << (n->merge_tf()? " merge-tf" : "") << "] ";
        if (n->has_th_vars()) {
            out << "[t";
            for (auto const& v : enode_th_vars(n))
                out << " " << v.get_id() << ":" << v.get_var();
            out << "] ";
        }
        if (n->generation() > 0)
            out << "[g " << n->generation() << "] ";
        if (n->m_target && m_display_justification)
            n->m_justification.display(out << "[j " << n->m_target->get_expr_id() << " ", m_display_justification) << "] ";
        out << "\n";
        return out;
    }

    std::ostream& egraph::display(std::ostream& out) const {
        out << "updates " << m_updates.size() << "\n";
        out << "neweqs  " << m_new_th_eqs.size() << " qhead: " << m_new_th_eqs_qhead << "\n";
        m_table.display(out);
        unsigned max_args = 0;
        for (enode* n : m_nodes)
            max_args = std::max(max_args, n->num_args());
        for (enode* n : m_nodes) 
            display(out, max_args, n);          
        for (auto* p : m_plugins)
            if (p)
                p->display(out);
        return out;
    }

    void egraph::collect_statistics(statistics& st) const {
        st.update("euf merge", m_stats.m_num_merge);
        st.update("euf conflicts", m_stats.m_num_conflicts);
        st.update("euf propagations eqs", m_stats.m_num_eqs);
        st.update("euf propagations theory eqs", m_stats.m_num_th_eqs);
        st.update("euf propagations theory diseqs", m_stats.m_num_th_diseqs);
        st.update("euf propagations literal", m_stats.m_num_lits);
        for (auto p : m_plugins) 
            if (p) 
                p->collect_statistics(st);                   
    }

    void egraph::copy_from(egraph const& src, std::function<void*(void*)>& copy_justification) {
        SASSERT(m_scopes.empty());
        SASSERT(m_nodes.empty());
        ptr_vector<enode> old_expr2new_enode, args;
        ast_translation tr(src.m, m);
        for (unsigned i = 0; i < src.m_nodes.size(); ++i) {
            enode* n1 = src.m_nodes[i];
            expr* e1 = src.m_exprs[i];
            args.reset();
            for (unsigned j = 0; j < n1->num_args(); ++j) 
                args.push_back(old_expr2new_enode[n1->get_arg(j)->get_expr_id()]);
            expr*  e2 = tr(e1);
            enode* n2 = mk(e2, n1->generation(), args.size(), args.data());
            
            old_expr2new_enode.setx(e1->get_id(), n2, nullptr);
            n2->set_value(n1->value());
            n2->m_bool_var = n1->m_bool_var;
            n2->m_commutative = n1->m_commutative;
            n2->m_cgc_enabled = n1->m_cgc_enabled;
            n2->m_merge_tf_enabled = n1->m_merge_tf_enabled;
            n2->m_is_equality = n1->m_is_equality;            
        }
        for (unsigned i = 0; i < src.m_nodes.size(); ++i) {             
            enode* n1 = src.m_nodes[i];
            enode* n1t = n1->m_target;      
            enode* n2 = m_nodes[i];
            enode* n2t = n1t ? old_expr2new_enode[n1->get_expr_id()] : nullptr;
            SASSERT(!n1t || n2t);
            SASSERT(!n1t || n1->get_sort() == n1t->get_sort());
            SASSERT(!n1t || n2->get_sort() == n2t->get_sort());
            if (n1t && n2->get_root() != n2t->get_root()) 
                merge(n2, n2t, n1->m_justification.copy(copy_justification));
        }
        propagate();
        for (unsigned i = 0; i < src.m_scopes.size(); ++i)
            push();
        force_push();
    }
}

template void euf::egraph::explain(ptr_vector<int>& justifications, cc_justification*);
template void euf::egraph::explain_todo(ptr_vector<int>& justifications, cc_justification*);
template void euf::egraph::explain_eq(ptr_vector<int>& justifications, cc_justification*, enode* a, enode* b);
template unsigned euf::egraph::explain_diseq(ptr_vector<int>& justifications, cc_justification*, enode* a, enode* b);

template void euf::egraph::explain(ptr_vector<size_t>& justifications, cc_justification*);
template void euf::egraph::explain_todo(ptr_vector<size_t>& justifications, cc_justification*);
template void euf::egraph::explain_eq(ptr_vector<size_t>& justifications, cc_justification*, enode* a, enode* b);
template unsigned euf::egraph::explain_diseq(ptr_vector<size_t>& justifications, cc_justification*, enode* a, enode* b);

template void euf::egraph::explain(ptr_vector<expr_dependency>& justifications, cc_justification*);
template void euf::egraph::explain_todo(ptr_vector<expr_dependency>& justifications, cc_justification*);
template void euf::egraph::explain_eq(ptr_vector<expr_dependency>& justifications, cc_justification*, enode* a, enode* b);
template unsigned euf::egraph::explain_diseq(ptr_vector<expr_dependency>& justifications, cc_justification*, enode* a, enode* b);


#if 0
Each node has a congruence closure root, cg.
cg is set to the representative in the cc table 
(first insertion of congruent node).
Each node n has a set of parents, denoted n.P.
The table maintains the invariant
 - p.cg = find(p)

Merge sets r2 to the root of r1 
(r2 and r1 are both considered roots before the merge).
The operation Unmerge reverses the effect of Merge.


Merge(r1, r2)
-------------

Erase:        for each p in r1.P such that p.cg == p:
                 erase from table        
Update root:  r1.root := r2
Insert:       for each p in r1.P:
                 p.cg = insert p in table
                 if p.cg == p:
                   append p to r2.P
                 else 
                   add (p.cg == p) to "to_merge" 

Unmerge(r1, r2)
---------------

Erase:        for each p in r2.P added from r1.P:
                 erase p from table 
Revert root:  r1.root := r1
Insert:       for each p in r1.P:
                 insert p if n was cc root before merge

condition for being cc root before merge:
  p.cg == p or !congruent(p, p.cg)

congruent(p,q) := roots of p.args = roots of q.args

The algorithm orients r1, r2 such that class_size(r1) <= class_size(r2).
With N nodes, there can be at most N calls to Merge.
Each of the calls traverse r1.P from the smaller class size.
Label a merge tree with nodes from the larger class size.
In other words, if Merge(r2,r1); Merge(r3,r1) is a sequence
of calls where r1 is selected root, then the merge tree is

    r1 
  /   \
 r1    r3  
   \
   r2

Note that parent lists are re-examined only for nodes that join
from right subtrees (with lesser class sizes).
Claim: a node participates in a path along right adjoining sub-trees at most O(log(N)) times.
Justification (very roughly): the size of a right adjoining subtree can at most 
be equal to the left adjoining sub-tree. This entails a logarithmic number of 
re-examinations from the right adjoining tree.

The parent lists are bounded by the maximal arity of functions.

Example:

Initially:
 n1 := f(a,b)  has root n1
 n2 := f(a1,b) has root n2
 table = [f(a,b) |-> n1, f(a1,b) |-> n2]

merge(a,a1) (a1 becomes root)
 table = [f(a1,b) |-> n2]
 n1.cg = n2
 a1.P = [n2]
 n1 is not added as parent because it is not a cc root after the assignment a.root := a1

unmerge(a,a1)
- nothing is erased
- n1 is reinserted. It used to be a root.

#endif
