/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_solver.cpp

Abstract:

    Nonlinear arithmetic satisfiability procedure. The procedure is
    complete for nonlinear real arithmetic, but it also has limited
    support for integers.

Author:

    Leonardo de Moura (leonardo) 2012-01-02.

Revision History:

--*/
#include <unordered_map>
#include <utility>
#include <string>
#include "util/z3_exception.h"
#include "util/chashtable.h"
#include "util/id_gen.h"
#include "util/map.h"
#include "util/dependency.h"
#include "util/permutation.h"
#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial_cache.h"
#include "nlsat/nlsat_solver.h"
#include "nlsat/nlsat_clause.h"
#include "nlsat/nlsat_assignment.h"
#include "nlsat/nlsat_justification.h"
#include "nlsat/nlsat_evaluator.h"
#include "nlsat/nlsat_explain.h"
#include "nlsat/nlsat_params.hpp"
#include "nlsat/nlsat_simplify.h"
#include "nlsat/nlsat_simple_checker.h"
#include "nlsat/nlsat_variable_ordering_strategy.h"

#define NLSAT_EXTRA_VERBOSE

#ifdef NLSAT_EXTRA_VERBOSE
#define NLSAT_VERBOSE(CODE) IF_VERBOSE(10, CODE)
#else
#define NLSAT_VERBOSE(CODE) ((void)0)
#endif

namespace nlsat {


    typedef chashtable<ineq_atom*, ineq_atom::hash_proc, ineq_atom::eq_proc> ineq_atom_table;
    typedef chashtable<root_atom*, root_atom::hash_proc, root_atom::eq_proc> root_atom_table;

    // for apply_permutation procedure
    void swap(clause * & c1, clause * & c2) noexcept {
        std::swap(c1, c2);
    }

    struct solver::ctx {
        params_ref             m_params;
        reslimit&              m_rlimit;
        small_object_allocator m_allocator;
        unsynch_mpq_manager    m_qm;
        pmanager               m_pm;
        anum_manager           m_am;
        bool                   m_incremental;
        ctx(reslimit& rlim, params_ref const & p, bool incremental):
            m_params(p),
            m_rlimit(rlim),
            m_allocator("nlsat"),
            m_pm(rlim, m_qm, &m_allocator),
            m_am(rlim, m_qm, p, &m_allocator),
            m_incremental(incremental)
        {}
    };

    struct solver::imp {

        struct dconfig {
            typedef imp                      value_manager;
            typedef small_object_allocator   allocator;
            typedef void* value;
            static const bool ref_count = false;
        };

        typedef dependency_manager<dconfig>  assumption_manager;
        typedef assumption_manager::dependency* _assumption_set;

        typedef obj_ref<assumption_manager::dependency, assumption_manager> assumption_set_ref;
        

        typedef polynomial::cache cache;
        typedef std_vector<interval_set*> interval_set_vector;
        
        ctx&                    m_ctx;
        solver&                 m_solver;
        reslimit&               m_rlimit;
        small_object_allocator& m_allocator;
        bool                    m_incremental;
        unsynch_mpq_manager&    m_qm;
        pmanager&               m_pm;
        cache                   m_cache;
        anum_manager&           m_am;
        mutable assumption_manager     m_asm;
        assignment              m_assignment, m_lo, m_hi; // partial interpretation
        mutable evaluator       m_evaluator;
        interval_set_manager & m_ism;
        ineq_atom_table        m_ineq_atoms;
        root_atom_table        m_root_atoms;


        vector<bound_constraint> m_bounds;
        
        id_gen                 m_cid_gen;
        clause_vector          m_clauses; // set of clauses
        clause_vector          m_learned; // set of learned clauses
        clause_vector          m_valids;

        unsigned               m_num_bool_vars;
        atom_vector            m_atoms;        // bool_var -> atom
        std_vector<lbool>      m_bvalues;      // boolean assignment
        std_vector<unsigned>   m_levels;       // bool_var -> level
        std_vector<justification> m_justifications;
        std_vector<clause_vector>  m_bwatches;     // bool_var (that are not attached to atoms) -> clauses where it is maximal
        std_vector<bool>            m_dead;         // mark dead boolean variables
        id_gen                 m_bid_gen;

        simplify               m_simplify;

        bool_vector            m_is_int;     // m_is_int[x] is true if variable is integer
        vector<clause_vector>  m_watches;    // var -> clauses where variable is maximal
        interval_set_vector    m_infeasible; // var -> to a set of interval where the variable cannot be assigned to.
        atom_vector            m_var2eq;     // var -> to asserted equality
        var_vector             m_perm;       // var -> var permutation of the variables
        var_vector             m_inv_perm;
        // m_perm:     internal -> external
        // m_inv_perm: external -> internal
        struct perm_display_var_proc : public display_var_proc {
            var_vector &             m_perm;
            display_var_proc         m_default_display_var;
            display_var_proc const * m_proc; // display external var ids
            perm_display_var_proc(var_vector & perm):
                m_perm(perm),
                m_proc(nullptr) {
            }
            std::ostream& operator()(std::ostream & out, var x) const override {
                if (m_proc == nullptr)
                    m_default_display_var(out, x);
                else
                    (*m_proc)(out, m_perm[x]);
                return out;
            }
        };
        perm_display_var_proc  m_display_var;

        display_assumption_proc const* m_display_assumption;
        struct display_literal_assumption : public display_assumption_proc {
            imp& i;
            literal_vector const& lits;
            display_literal_assumption(imp& i, literal_vector const& lits): i(i), lits(lits) {}
            std::ostream& operator()(std::ostream& out, assumption a) const override {
                if (lits.begin() <= a && a < lits.end()) {
                    out << *((literal const*)a);
                }
                else if (i.m_display_assumption) {
                    (*i.m_display_assumption)(out, a);
                }
                return out;
            }

        };
        struct scoped_display_assumptions {
            imp& i;
            display_assumption_proc const* m_save;
            scoped_display_assumptions(imp& i, display_assumption_proc const& p): i(i), m_save(i.m_display_assumption) {
                i.m_display_assumption = &p;
            }
            ~scoped_display_assumptions() {
                i.m_display_assumption = m_save;
            }
        };

        explain                m_explain;

        bool_var               m_bk;       // current Boolean variable we are processing
        var                    m_xk;       // current arith variable we are processing

        unsigned               m_scope_lvl;

        struct bvar_assignment {};
        struct stage {};
        struct trail {
            enum kind { BVAR_ASSIGNMENT, INFEASIBLE_UPDT, NEW_LEVEL, NEW_STAGE, UPDT_EQ };
            kind   m_kind;
            union {
                bool_var m_b;
                interval_set * m_old_set;
                atom         * m_old_eq;
            };
            trail(bool_var b, bvar_assignment):m_kind(BVAR_ASSIGNMENT), m_b(b) {}
            trail(interval_set * old_set):m_kind(INFEASIBLE_UPDT), m_old_set(old_set) {}
            trail(bool s, stage):m_kind(s ? NEW_STAGE : NEW_LEVEL) {}
            trail(atom * a):m_kind(UPDT_EQ), m_old_eq(a) {}
        };
        svector<trail>         m_trail;

        anum                   m_zero;

        // configuration
        unsigned long long     m_max_memory;
        unsigned               m_lazy;  // how lazy the solver is: 0 - satisfy all learned clauses, 1 - process only unit and empty learned clauses, 2 - use only conflict clauses for resolving conflicts
        bool                   m_simplify_cores;
        bool                   m_reorder;
        bool                   m_randomize;
        bool                   m_random_order;
        unsigned               m_random_seed;
        bool                   m_inline_vars;
        bool                   m_log_lemmas;
        bool                   m_dump_mathematica;
        bool                   m_check_lemmas;
        unsigned               m_max_conflicts;
        unsigned               m_lemma_count;
        unsigned m_variable_ordering_strategy;
        bool m_set_0_more;
        bool m_cell_sample;

        struct stats {
            unsigned               m_simplifications;
            unsigned               m_restarts;
            unsigned               m_conflicts;
            unsigned               m_propagations;
            unsigned               m_decisions;
            unsigned               m_stages;
            unsigned               m_irrational_assignments; // number of irrational witnesses
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };
        // statistics
        stats                  m_stats;
        std::string m_debug_known_solution_file_name;

        imp(solver& s, ctx& c):
            m_ctx(c),
            m_solver(s),
            m_rlimit(c.m_rlimit),
            m_allocator(c.m_allocator),
            m_incremental(c.m_incremental),
            m_qm(c.m_qm),
            m_pm(c.m_pm),
            m_cache(m_pm),
            m_am(c.m_am),
            m_asm(*this, m_allocator),
            m_assignment(m_am), m_lo(m_am), m_hi(m_am),
            m_evaluator(s, m_assignment, m_pm, m_allocator),
            m_ism(m_evaluator.ism()),
            m_num_bool_vars(0),
            m_simplify(s, m_atoms, m_clauses, m_learned, m_pm),
            m_display_var(m_perm),
            m_display_assumption(nullptr),
            m_explain(s, m_assignment, m_cache, m_atoms, m_var2eq, m_evaluator, nlsat_params(c.m_params).cell_sample()),
            m_scope_lvl(0),
            m_lemma(s),
            m_lazy_clause(s),
            m_lemma_assumptions(m_asm) {
            updt_params(c.m_params);
            reset_statistics();
            mk_true_bvar();
            m_lemma_count = 0;
        }
        
        ~imp() {
            clear();
        }

        void mk_true_bvar() {
            bool_var b = mk_bool_var();
            SASSERT(b == true_bool_var);
            literal true_lit(b, false);
            mk_clause(1, &true_lit, false, nullptr);
        }

        void updt_params(params_ref const & _p) {
            nlsat_params p(_p);
            m_max_memory     = p.max_memory();
            m_lazy           = p.lazy();
            m_simplify_cores = p.simplify_conflicts();
            bool min_cores   = p.minimize_conflicts();
            m_reorder        = p.reorder();
            m_randomize      = p.randomize();
            m_max_conflicts  = p.max_conflicts();
            m_random_order   = p.shuffle_vars();
            m_random_seed    = p.seed();
            m_inline_vars    = p.inline_vars();
            m_log_lemmas     = p.log_lemmas();
            m_dump_mathematica= p.dump_mathematica();
            m_check_lemmas   = p.check_lemmas();
            m_variable_ordering_strategy = p.variable_ordering_strategy();
            m_debug_known_solution_file_name = p.known_sat_assignment_file_name();
            m_check_lemmas |= !(m_debug_known_solution_file_name.empty());
            m_cell_sample = p.cell_sample();
  
            m_ism.set_seed(m_random_seed);
            m_explain.set_simplify_cores(m_simplify_cores);
            m_explain.set_minimize_cores(min_cores);
            m_explain.set_factor(p.factor());
            m_am.updt_params(p.p);
        }

        void reset() {
            m_explain.reset();
            m_lemma.reset();
            m_lazy_clause.reset();
            undo_until_size(0);
            del_clauses();
            del_unref_atoms();
            m_cache.reset();
            m_assignment.reset();
            m_lo.reset();
            m_hi.reset();
        }

        void clear() {
            m_explain.reset();
            m_lemma.reset();
            m_lazy_clause.reset();
            undo_until_size(0);
            del_clauses();
            del_unref_atoms();
        }

        void checkpoint() {
            if (!m_rlimit.inc()) throw solver_exception(m_rlimit.get_cancel_msg()); 
            if (memory::get_allocation_size() > m_max_memory) throw solver_exception(Z3_MAX_MEMORY_MSG);
        }

        // -----------------------
        //
        // Basic
        //
        // -----------------------

        unsigned num_bool_vars() const {
            return m_num_bool_vars;
        }
        
        unsigned num_vars() const {
            return m_is_int.size();
        }

        bool is_int(var x) const {
            return m_is_int[x];
        }

        void inc_ref(assumption) {}

        void dec_ref(assumption) {}

        void inc_ref(_assumption_set a) {            
            if (a != nullptr) m_asm.inc_ref(a);
        }
        
        void dec_ref(_assumption_set a) {
            if (a != nullptr) m_asm.dec_ref(a);
        }

        void inc_ref(bool_var b) {
            if (b == null_bool_var)
                return;
            atom * a = m_atoms[b];
            if (a == nullptr)
                return;
            TRACE(ref, display(tout << "inc: " << b << " " << a->ref_count() << " ", *a) << "\n";);
            a->inc_ref();
        }
        
        void inc_ref(literal l) {
            inc_ref(l.var());
        }

        void dec_ref(bool_var b) {
            if (b == null_bool_var)
                return;
            atom * a = m_atoms[b];
            if (a == nullptr)
                return;
            SASSERT(a->ref_count() > 0);
            a->dec_ref();
            TRACE(ref, display(tout << "dec: " << b << " " << a->ref_count() << " ", *a) << "\n";);
            if (a->ref_count() == 0)
                del(a);
        }

        void dec_ref(literal l) {
            dec_ref(l.var());
        }

        bool is_arith_atom(bool_var b) const { return m_atoms[b] != nullptr; }

        bool is_arith_literal(literal l) const { return is_arith_atom(l.var()); }

        var max_var(poly const * p) const {
            return m_pm.max_var(p);
        }

        var max_var(bool_var b) const {
            if (!is_arith_atom(b))
                return null_var;
            else
                return m_atoms[b]->max_var();
        }

        var max_var(literal l) const {
            return max_var(l.var());
        }
        
        /**
           \brief Return the maximum variable occurring in cls.
        */
        var max_var(unsigned sz, literal const * cls) const {
            var x      = null_var;
            for (unsigned i = 0; i < sz; i++) {
                literal l = cls[i];
                if (is_arith_literal(l)) {
                    var y = max_var(l);
                    if (x == null_var || y > x)
                        x = y;
                }
            }
            return x;
        }

        var max_var(clause const & cls) const {
            return max_var(cls.size(), cls.data());
        }

        /**
           \brief Return the maximum Boolean variable occurring in cls.
        */
        bool_var max_bvar(clause const & cls) const {
            bool_var b = null_bool_var;
            for (literal l : cls) {
                if (b == null_bool_var || l.var() > b)
                    b = l.var();
            }
            return b;
        }

        /**
           \brief Return the degree of the maximal variable of the given atom
        */
        unsigned degree(atom const * a) const {
            if (a->is_ineq_atom()) {
                unsigned max = 0;
                unsigned sz  = to_ineq_atom(a)->size();
                var x = a->max_var();
                for (unsigned i = 0; i < sz; i++) {
                    unsigned d = m_pm.degree(to_ineq_atom(a)->p(i), x);
                    if (d > max)
                        max = d;
                }
                return max;
            }
            else {
                return m_pm.degree(to_root_atom(a)->p(), a->max_var());

            }
        }

        /**
           \brief Return the degree of the maximal variable in c
        */
        unsigned degree(clause const & c) const {
            var x = max_var(c);
            if (x == null_var)
                return 0;
            unsigned max = 0;
            for (literal l : c) {
                atom const * a  = m_atoms[l.var()];
                if (a == nullptr)
                    continue;
                unsigned d = degree(a);
                if (d > max)
                    max = d;
            }
            return max;
        }

        // -----------------------
        //
        // Variable, Atoms, Clauses & Assumption creation
        //
        // -----------------------

        template <typename T, typename V> void setx(T& vector, unsigned b, const V& value, const V& default_value) {
            if (b >= vector.size()) 
                vector.resize(b + 1, default_value);
            vector[b] = value;
        }
        
        bool_var mk_bool_var_core() {
            bool_var b = m_bid_gen.mk();
            m_num_bool_vars++;
            setx(m_atoms, b, nullptr, nullptr);
            setx(m_bvalues, b, l_undef, l_undef);
            setx(m_levels, b, UINT_MAX, UINT_MAX);
            setx(m_justifications, b, null_justification, null_justification);
            setx(m_bwatches, b, clause_vector(), clause_vector());
            setx(m_dead, b, false, true);
            return b;
        }

        bool_var mk_bool_var() {
            return mk_bool_var_core();
        }

        var mk_var(bool is_int) {
            var x = m_pm.mk_var();
            register_var(x, is_int);
            return x;
        }
        void register_var(var x, bool is_int) {
            SASSERT(x == num_vars());
            m_is_int.    push_back(is_int);
            m_watches.   push_back(clause_vector());
            m_infeasible.push_back(nullptr);
            m_var2eq.    push_back(nullptr);
            m_perm.      push_back(x);
            m_inv_perm.  push_back(x);
            SASSERT(m_is_int.size() == m_watches.size());
            SASSERT(m_is_int.size() == m_infeasible.size());
            SASSERT(m_is_int.size() == m_var2eq.size());
            SASSERT(m_is_int.size() == m_perm.size());
            SASSERT(m_is_int.size() == m_inv_perm.size());
        }

        mutable bool_vector m_found_vars;
        void vars(literal l, var_vector& vs) const {                
            vs.reset();
            atom * a = m_atoms[l.var()];
            if (a == nullptr) {
                
            }
            else if (a->is_ineq_atom()) {
                unsigned sz = to_ineq_atom(a)->size();
                var_vector new_vs;
                for (unsigned j = 0; j < sz; j++) {
                    m_found_vars.reset();
                    m_pm.vars(to_ineq_atom(a)->p(j), new_vs);
                    for (unsigned i = 0; i < new_vs.size(); ++i) {
                        if (!m_found_vars.get(new_vs[i], false)) {
                            m_found_vars.setx(new_vs[i], true, false);
                            vs.push_back(new_vs[i]);
                        }
                    }
                }
            }
            else {
                m_pm.vars(to_root_atom(a)->p(), vs);
                //vs.erase(max_var(to_root_atom(a)->p()));
                vs.push_back(to_root_atom(a)->x());
            }
        }

        void deallocate(ineq_atom * a) {
            unsigned obj_sz = ineq_atom::get_obj_size(a->size());
            a->~ineq_atom();
            m_allocator.deallocate(obj_sz, a);
        }

        void deallocate(root_atom * a) {
            a->~root_atom();
            m_allocator.deallocate(sizeof(root_atom), a);
        }

        void del(bool_var b) {
            SASSERT(m_bwatches[b].empty());
            //SASSERT(m_bvalues[b] == l_undef);
            m_num_bool_vars--;
            m_dead[b]  = true;
            m_atoms[b] = nullptr;
            TRACE(nlsat_assign, tout << "undef bool value at index " << b << "\n";);
            m_bvalues[b] = l_undef;
            m_bid_gen.recycle(b);
        }

        void del(ineq_atom * a) {
            CTRACE(nlsat_solver, a->ref_count() > 0, display(tout, *a) << "\n";);
            // this triggers in too many benign cases:
            // SASSERT(a->ref_count() == 0);
            m_ineq_atoms.erase(a);
            del(a->bvar());
            unsigned sz = a->size();
            for (unsigned i = 0; i < sz; i++)
                m_pm.dec_ref(a->p(i));
            deallocate(a);
        }

        void del(root_atom * a) {
            SASSERT(a->ref_count() == 0);
            m_root_atoms.erase(a);
            del(a->bvar());
            m_pm.dec_ref(a->p());
            deallocate(a);
        }

        void del(atom * a) {
            if (a == nullptr)
                return;
            TRACE(nlsat_verbose, display(tout << "del: b" << a->m_bool_var << " " << a->ref_count() << " ", *a) << "\n";);
            if (a->is_ineq_atom())
                del(to_ineq_atom(a));
            else
                del(to_root_atom(a));
        }
        
        // Delete atoms with ref_count == 0
        void del_unref_atoms() {
            for (auto* a : m_atoms) {
                del(a);
            }
        }


        ineq_atom* mk_ineq_atom(atom::kind k, unsigned sz, poly * const * ps, bool const * is_even, bool& is_new, bool simplify) {
            SASSERT(sz >= 1);
            SASSERT(k == atom::LT || k == atom::GT || k == atom::EQ);
            int sign = 1;
            polynomial_ref p(m_pm);
            ptr_buffer<poly> uniq_ps;
            var max = null_var;
            for (unsigned i = 0; i < sz; i++) {
                p = m_pm.flip_sign_if_lm_neg(ps[i]);
                if (p.get() != ps[i] && !is_even[i]) {
                    sign = -sign;
                }
                var curr_max = max_var(p.get());
                if (curr_max > max || max == null_var)
                    max = curr_max;
                if (sz == 1 && simplify) {
                    if (sign < 0)
                        k = atom::flip(k);
                    sign = 1;
                    polynomial::manager::ineq_type t = polynomial::manager::ineq_type::EQ;
                    switch (k) {
                    case atom::EQ: t = polynomial::manager::ineq_type::EQ; break;
                    case atom::LT: t = polynomial::manager::ineq_type::LT; break;
                    case atom::GT: t = polynomial::manager::ineq_type::GT; break;
                    default: UNREACHABLE(); break;
                    }
                    polynomial::var_vector vars;
                    m_pm.vars(p, vars);
                    bool all_int = all_of(vars, [&](var x) { return is_int(x); });
                    if (!all_int) 
                        t = polynomial::manager::ineq_type::EQ;                    
                    m_pm.gcd_simplify(p, t);
                }
                uniq_ps.push_back(m_cache.mk_unique(p));
                TRACE(nlsat_table_bug, tout << "p: " << p << ", uniq: " << uniq_ps.back() << "\n";);
                //verbose_stream() << "p: " << p.get() << ", uniq: " << uniq_ps.back() << "\n";
            }
            void * mem = m_allocator.allocate(ineq_atom::get_obj_size(sz));
            if (sign < 0)
                k = atom::flip(k);
            ineq_atom * tmp_atom = new (mem) ineq_atom(k, sz, uniq_ps.data(), is_even, max);
            ineq_atom * atom = m_ineq_atoms.insert_if_not_there(tmp_atom);
            CTRACE(nlsat_table_bug, tmp_atom != atom, ineq_atom::hash_proc h; 
                   tout << "mk_ineq_atom hash: " << h(tmp_atom) << "\n"; display(tout, *tmp_atom, m_display_var) << "\n";);
            CTRACE(nlsat_table_bug, atom->max_var() != max, display(tout << "nonmax: ", *atom, m_display_var) << "\n";);
            SASSERT(atom->max_var() == max);
            is_new = (atom == tmp_atom);
            if (is_new) {
                for (unsigned i = 0; i < sz; i++) {
                    m_pm.inc_ref(atom->p(i));
                }
            }
            else {
                deallocate(tmp_atom);
            }
            return atom;
        }

        bool_var mk_ineq_atom(atom::kind k, unsigned sz, poly * const * ps, bool const * is_even, bool simplify = false) {
            bool is_new = false;
            ineq_atom* atom = mk_ineq_atom(k, sz, ps, is_even, is_new, simplify);
            if (!is_new) {
                return atom->bvar();
            }
            else {
                bool_var b = mk_bool_var_core();
                m_atoms[b] = atom;
                atom->m_bool_var = b;
                TRACE(nlsat_verbose, display(tout << "create: b" << atom->m_bool_var << " ", *atom) << "\n";);
                return b;
            }
        }

        literal mk_ineq_literal(atom::kind k, unsigned sz, poly * const * ps, bool const * is_even, bool simplify = false) {
            SASSERT(k == atom::LT || k == atom::GT || k == atom::EQ);
            bool is_const = true;
            polynomial::manager::scoped_numeral cnst(m_pm.m());
            m_pm.m().set(cnst, 1);            
            for (unsigned i = 0; i < sz; ++i) {
                if (m_pm.is_const(ps[i])) {
                    if (m_pm.is_zero(ps[i])) {
                        m_pm.m().set(cnst, 0);
                        is_const = true;
                        break;
                    }
                    auto const& c = m_pm.coeff(ps[i], 0);
                    m_pm.m().mul(cnst, c, cnst);
                    if (is_even[i] && m_pm.m().is_neg(c)) {
                        m_pm.m().neg(cnst);
                    }                            
                }
                else {
                    is_const = false;
                }
            }
            if (is_const) {
                if (m_pm.m().is_pos(cnst) && k == atom::GT) return true_literal;
                if (m_pm.m().is_neg(cnst) && k == atom::LT) return true_literal;
                if (m_pm.m().is_zero(cnst) && k == atom::EQ) return true_literal;
                return false_literal;
            }
            return literal(mk_ineq_atom(k, sz, ps, is_even, simplify), false);            
        }

        bool_var mk_root_atom(atom::kind k, var x, unsigned i, poly * p) {
            polynomial_ref p1(m_pm), uniq_p(m_pm);
            p1 = m_pm.flip_sign_if_lm_neg(p); // flipping the sign of the polynomial will not change its roots.
            uniq_p = m_cache.mk_unique(p1); 
            TRACE(nlsat_solver, tout << x << " " << p1 << " " << uniq_p << "\n";);
            SASSERT(i > 0);
            SASSERT(x >= max_var(p));
            SASSERT(k == atom::ROOT_LT || k == atom::ROOT_GT || k == atom::ROOT_EQ || k == atom::ROOT_LE || k == atom::ROOT_GE);

            void * mem = m_allocator.allocate(sizeof(root_atom));
            root_atom * new_atom = new (mem) root_atom(k, x, i, uniq_p);
            root_atom * old_atom = m_root_atoms.insert_if_not_there(new_atom);
            SASSERT(old_atom->max_var() == x);
            if (old_atom != new_atom) {
                deallocate(new_atom);
                return old_atom->bvar();
            }
            bool_var b = mk_bool_var_core();
            m_atoms[b] = new_atom;
            new_atom->m_bool_var = b;
            m_pm.inc_ref(new_atom->p());
            return b;
        }

        void add_clause_to_watches(clause & cls) {
            var x      = max_var(cls);
            if (x != null_var) {
                m_watches[x].push_back(&cls);
            }
            else {
                bool_var b = max_bvar(cls);
                m_bwatches[b].push_back(&cls);
            }
        }

        void remove_clause_from_watches(clause & cls) {
            var x = max_var(cls);
            if (x != null_var) {
                auto & w = m_watches[x];
                auto it = std::find(w.begin(), w.end(), &cls);
                if (it != w.end())
                    w.erase(it);
            }
            else {
                bool_var b = max_bvar(cls);
                auto & bw = m_bwatches[b];
                auto it = std::find(bw.begin(), bw.end(), &cls);
                if (it != bw.end())
                    bw.erase(it);
            }
        }

        void deallocate(clause * cls) {
            size_t obj_sz = clause::get_obj_size(cls->size());
            cls->~clause();
            m_allocator.deallocate(obj_sz, cls);
        }
        
        void del_clause(clause * cls) {
            remove_clause_from_watches(*cls);
            m_cid_gen.recycle(cls->id());
            unsigned sz = cls->size();
            for (unsigned i = 0; i < sz; i++)
                dec_ref((*cls)[i]);
            _assumption_set a = static_cast<_assumption_set>(cls->assumptions());
            dec_ref(a);
            deallocate(cls);
        }

        void del_clause(clause * cls, clause_vector& clauses) {
            auto it = std::find(clauses.begin(), clauses.end(), cls);
            if (it != clauses.end())
                clauses.erase(it);
            del_clause(cls);
        }

        void del_clauses(clause_vector & cs) {
            for (clause* cp : cs) 
                del_clause(cp);
            cs.clear();
        }

        void del_clauses() {
            del_clauses(m_clauses);
            del_clauses(m_learned);
            del_clauses(m_valids);
        }

        // We use a simple heuristic to sort literals
        //   - bool literals < arith literals
        //   - sort literals based on max_var
        //   - sort literal with the same max_var using degree
        //     break ties using the fact that ineqs are usually cheaper to process than eqs.
        struct lit_lt {
            imp & m;
            lit_lt(imp & _m):m(_m) {}

            bool operator()(literal l1, literal l2) const {
                atom * a1 = m.m_atoms[l1.var()];
                atom * a2 = m.m_atoms[l2.var()];
                if (a1 == nullptr && a2 == nullptr)
                    return l1.index() < l2.index();
                if (a1 == nullptr)
                    return true;
                if (a2 == nullptr)
                    return false;
                var x1 = a1->max_var();
                var x2 = a2->max_var();
                if (x1 < x2)
                    return true;
                if (x1 > x2)
                    return false;
                SASSERT(x1 == x2);
                unsigned d1 = m.degree(a1);
                unsigned d2 = m.degree(a2);
                if (d1 < d2)
                    return true;
                if (d1 > d2)
                    return false;
                if (!a1->is_eq() && a2->is_eq())
                    return true;
                if (a1->is_eq() && !a2->is_eq())
                    return false;
                return l1.index() < l2.index();
            }
        };

        class scoped_bool_vars { 
            imp& s;
            svector<bool_var> vec;
        public:
            scoped_bool_vars(imp& s):s(s) {}
            ~scoped_bool_vars() {
                for (bool_var v : vec) {
                    s.dec_ref(v);
                }
            }
            void push_back(bool_var v) {
                s.inc_ref(v);
                vec.push_back(v);
            }
            bool_var const* begin() const { return vec.begin(); }
            bool_var const* end() const { return vec.end(); }
            bool_var operator[](bool_var v) const { return vec[v]; }
        };

        std::vector<unsigned> collect_vars(literal l) {
            var_vector vars;
            this->vars(l, vars);
            std::vector<unsigned> result;
            for (unsigned i = 0; i < vars.size(); ++i) {
                result.push_back(vars[i]);
            }
            return result;
        }

        std::vector<unsigned> collect_vars_on_clause(unsigned n_of_literals, literal const *cls) {
            bool_vector seen(num_vars(), false);
            std::vector<unsigned> result;
            for (unsigned i = 0; i < n_of_literals; ++i) {
                auto vlist = collect_vars(cls[i]);
                for (unsigned x : vlist) {
                    if (x < seen.size() && !seen[x]) {
                        seen.setx(x, true, false);
                        result.push_back(x);
                    }
                }
            }
            return result;
        }

        std::ostream& display_assignment_on_clause(std::ostream& out, const assignment & x2v, unsigned n_of_literals, literal const *cls) {
            auto vars = collect_vars_on_clause(n_of_literals, cls);
            for (unsigned x : vars) {
                m_display_var(out, x);
                out << " = ";
                if (x2v.is_assigned(x))
                    m_am.display_decimal(out, x2v.value(x));
                else
                    out << "undef";
                out << "\n";
            }
            return out;
        }

        void debug_parse_known_assignment(
            std::vector<std::pair<std::string, anum>> & var_sat_values,
            assignment& debug_assignment) {
            std::ifstream in(m_debug_known_solution_file_name);
            std::string line;
            while (std::getline(in, line)) {
                std::istringstream iss(line);
                std::string name, value_str;
                if (!(iss >> name >> value_str)) {
                    std::cout << line << std::endl;
                    std::cout << "is not recognized\n";
                    exit(1);
                }
                // Parse rational value
                rational r;
                size_t slash = value_str.find('/');
                if (slash == std::string::npos) {
                    r = rational(value_str.c_str());
                } else {
                    std::string num = value_str.substr(0, slash);
                    std::string den = value_str.substr(slash + 1);
                    r = rational(num.c_str()) / rational(den.c_str());
                }
                anum a;
                const auto& q = r.to_mpq();
                m_am.set(a, q);
                var_sat_values.emplace_back(name, a);
            }
            
            // Build a map from variable names to their known values
            std::unordered_map<std::string, anum> debug_known_sat_anum_map;
            for (auto const & kv : var_sat_values) {
                anum val;
                m_am.set(val, kv.second);
                debug_known_sat_anum_map[kv.first] = val;
            }
            
            // Set up the debug assignment with known values
            for (var x = 0; x < num_vars(); ++x) {
                std::string name = debug_get_var_name(x);
                auto it = debug_known_sat_anum_map.find(name);
                if (it != debug_known_sat_anum_map.end()) {
                    debug_assignment.set(x, it->second);
                }
            }
        }

        bool debug_check_lemma_literals(unsigned n_of_literals, literal const *cls, evaluator& debug_evaluator, assignment& debug_assignment) {           
            for (unsigned i = 0; i < n_of_literals; ++i) {
                literal l = cls[i];
                bool_var b = l.var();
                atom* a = m_atoms[b];
                if (a == nullptr) 
                    return true; // ignore lemmas with pure boolean variables

                lbool val = l_undef;
                // Arithmetic atom: evaluate directly
                var max = a->max_var();
                SASSERT(debug_assignment.is_assigned(max));
                val = to_lbool(debug_evaluator.eval(a, l.sign()));
                SASSERT(val != l_undef);
                if (val == l_true)
                    return true;
            }
            return false;
        }
        
        // At least one literal has to be evaluate to true.
        // The method might ignore a lemma with pure boolean varibles.
        void debug_check_lemma_on_known_sat_values(unsigned n_of_literals, literal const *cls) {
            // If no debug file is specified, just return
            if (m_debug_known_solution_file_name.empty()) 
                return;
            assignment debug_assignment(m_am);
            evaluator debug_evaluator(m_solver, debug_assignment, m_pm, m_allocator);
            std::vector<std::pair<std::string, anum>> var_sat_values;
            debug_parse_known_assignment(var_sat_values, debug_assignment);
            bool satisfied = debug_check_lemma_literals(n_of_literals, cls, debug_evaluator, debug_assignment);
            if (!satisfied) {
                m_display_var.m_proc = nullptr;
                std::cout << "Known sat assignment does not satisfy valid lemma!\n";
                display(std::cout, n_of_literals, cls) << "\n";
                display_assignment_on_clause(std::cout, debug_assignment, n_of_literals, cls);
                exit(1);
            }
        }

        void check_lemma(unsigned n, literal const* cls, bool is_valid, assumption_set a) {
            TRACE(nlsat, display(tout << "check lemma: ", n, cls) << "\n";
                  display(tout););
            if (!m_debug_known_solution_file_name.empty()) {
                debug_check_lemma_on_known_sat_values(n, cls);
                return;
            }
            IF_VERBOSE(2, display(verbose_stream() << "check lemma " << (is_valid?"valid: ":"consequence: "), n, cls) << "\n");
            for (clause* c : m_learned) IF_VERBOSE(1, display(verbose_stream() << "lemma: ", *c) << "\n"); 
            scoped_suspend_rlimit _limit(m_rlimit);
            ctx c(m_rlimit, m_ctx.m_params, m_ctx.m_incremental);
            solver solver2(c);
            imp& checker = *(solver2.m_imp);
            checker.m_check_lemmas = false;
            checker.m_log_lemmas = false;
            checker.m_dump_mathematica = false;
            checker.m_inline_vars = false;

            auto pconvert = [&](poly* p) {
                return convert(m_pm, p, checker.m_pm);
            };

            // need to translate Boolean variables and literals
            scoped_bool_vars tr(checker);
            for (var x = 0; x < m_is_int.size(); ++x) {
                checker.register_var(x, is_int(x));
            }
            bool_var bv = 0;
            tr.push_back(bv);
            for (bool_var b = 1; b < m_atoms.size(); ++b) {
                atom* a = m_atoms[b];
                if (a == nullptr) {
                    bv = checker.mk_bool_var();
                }
                else if (a->is_ineq_atom()) {
                    ineq_atom& ia = *to_ineq_atom(a);
                    unsigned sz = ia.size();
                    polynomial_ref_vector ps(checker.m_pm);
                    bool_vector is_even;
                    for (unsigned i = 0; i < sz; ++i) {
                        ps.push_back(pconvert(ia.p(i)));
                        is_even.push_back(ia.is_even(i));
                    }
                    bv = checker.mk_ineq_atom(ia.get_kind(), sz, ps.data(), is_even.data());
                }
                else if (a->is_root_atom()) {
                    root_atom& r = *to_root_atom(a);
                    if (r.x() >= max_var(r.p())) {
                        // permutation may be reverted after check completes, 
                        // but then root atoms are not used in lemmas.
                        bv = checker.mk_root_atom(r.get_kind(), r.x(), r.i(), pconvert(r.p()));
                    }
                }
                else {
                    UNREACHABLE();
                }
                tr.push_back(bv);
            }
            if (!is_valid) {
                for (clause* c : m_clauses) {
                    if (!a && c->assumptions()) {
                        continue;
                    }
                    literal_vector lits;
                    for (literal lit : *c) {
                        lits.push_back(literal(tr[lit.var()], lit.sign()));
                    }
                    checker.mk_external_clause(lits.size(), lits.data(), nullptr);
                }
            }
            for (unsigned i = 0; i < n; ++i) {
                literal lit = cls[i];
                literal nlit(tr[lit.var()], !lit.sign());
                checker.mk_external_clause(1, &nlit, nullptr);
            }
            lbool r = checker.check();
            if (r == l_true) {
                for (bool_var b : tr) {
                    literal lit(b, false);
                    IF_VERBOSE(0, checker.display(verbose_stream(), lit) << " := " << checker.value(lit) << "\n");
                    TRACE(nlsat, checker.display(tout, lit) << " := " << checker.value(lit) << "\n";);
                }
                for (clause* c : m_learned) {
                    bool found = false;
                    for (literal lit: *c) {
                        literal tlit(tr[lit.var()], lit.sign());
                        found |= checker.value(tlit) == l_true;
                    }
                    if (!found) {
                        IF_VERBOSE(0, display(verbose_stream() << "violdated clause: ", *c) << "\n");
                        TRACE(nlsat, display(tout << "violdated clause: ", *c) << "\n";);
                    }
                }
                for (clause* c : m_valids) {
                    bool found = false;
                    for (literal lit: *c) {
                        literal tlit(tr[lit.var()], lit.sign());
                        found |= checker.value(tlit) == l_true;
                    }
                    if (!found) {
                        IF_VERBOSE(0, display(verbose_stream() << "violdated tautology clause: ", *c) << "\n");
                        TRACE(nlsat, display(tout << "violdated tautology clause: ", *c) << "\n";);
                    }                    
                }
                throw default_exception("lemma did not check");
                UNREACHABLE();
            }
        }

        void log_lemma(std::ostream& out, clause const& cls) {
            log_lemma(out, cls.size(), cls.data(), false);
        }

        void log_lemma(std::ostream& out, unsigned n, literal const* cls, bool is_valid) {
            ++m_lemma_count;
            out << "(set-logic NRA)\n";
            if (is_valid) {
                display_smt2_bool_decls(out);
                display_smt2_arith_decls(out);
            }
            else             
                display_smt2(out);            
            for (unsigned i = 0; i < n; ++i) 
                display_smt2(out << "(assert ", ~cls[i]) << ")\n";
            display(out << "(echo \"#" << m_lemma_count << " ", n, cls) << "\")\n";
            out << "(check-sat)\n(reset)\n";

            TRACE(nlsat, display(tout << "(echo \"#" << m_lemma_count << " ", n, cls) << "\")\n");
        }

        clause * mk_clause_core(unsigned num_lits, literal const * lits, bool learned, _assumption_set a) {
            SASSERT(num_lits > 0);
            unsigned cid = m_cid_gen.mk();
            void * mem = m_allocator.allocate(clause::get_obj_size(num_lits));
            clause * cls = new (mem) clause(cid, num_lits, lits, learned, a);
            for (unsigned i = 0; i < num_lits; i++)
                inc_ref(lits[i]);
            inc_ref(a);
            return cls;
        }

        clause * mk_clause(unsigned num_lits, literal const * lits, bool learned, _assumption_set a) {
            if (num_lits == 0) {
                num_lits = 1;
                lits = &false_literal;
            }
            SASSERT(num_lits > 0);
            clause * cls = mk_clause_core(num_lits, lits, learned, a);
            TRACE(nlsat_sort, display(tout << "mk_clause:\n", *cls) << "\n";);
            std::sort(cls->begin(), cls->end(), lit_lt(*this));
            TRACE(nlsat, display(tout << " after sort:\n", *cls) << "\n";);
            if (learned && m_log_lemmas) {
                log_lemma(verbose_stream(), *cls);
            }
            if (learned && m_check_lemmas) {
                check_lemma(cls->size(), cls->data(), false, cls->assumptions());
            }
            if (learned)
                m_learned.push_back(cls);
            else
                m_clauses.push_back(cls);
            add_clause_to_watches(*cls);
            return cls;
        }

        void mk_external_clause(unsigned num_lits, literal const * lits, assumption a) {
            _assumption_set as = nullptr;
            if (a != nullptr)
                as = m_asm.mk_leaf(a);
            if (num_lits == 0) {
                num_lits = 1;
                lits = &false_literal;
            }
            mk_clause(num_lits, lits, false, as);
        }

        // -----------------------
        //
        // Search
        //
        // -----------------------

        void save_assign_trail(bool_var b) {
            m_trail.push_back(trail(b, bvar_assignment()));
        }

        void save_set_updt_trail(interval_set * old_set) {
            m_trail.push_back(trail(old_set));
        }

        void save_updt_eq_trail(atom * old_eq) {
            m_trail.push_back(trail(old_eq));
        }

        void save_new_stage_trail() {
            m_trail.push_back(trail(true, stage()));
        }

        void save_new_level_trail() {
            m_trail.push_back(trail(false, stage()));
        }
     
        void unassign_bool_var(bool_var b) {
            TRACE(nlsat_assign, tout << "unassign bool var b" << b << "\n";);
            m_bvalues[b] = l_undef;
            m_levels[b]  = UINT_MAX;
            del_jst(m_allocator, m_justifications[b]);
            m_justifications[b] = null_justification;
            if (m_atoms[b] == nullptr && b < m_bk)
                m_bk = b;
        }

        void undo_set_updt(interval_set * old_set) {
            if (m_xk == null_var) 
                return;
            var x = m_xk;
            if (x < m_infeasible.size()) {
                m_ism.dec_ref(m_infeasible[x]);
                m_infeasible[x] = old_set;
            }
        }

        void undo_new_stage() {
            TRACE(nlsat, tout << "m_xk was " << m_xk << ",(" << debug_get_var_name(m_xk) << "), becaming " << m_xk - 1; if (m_xk) tout << "(" << debug_get_var_name(m_xk - 1) << ")"; tout << "\n";);
            if (m_xk == 0) {
                m_xk = null_var;
            }
            else if (m_xk != null_var) {
                m_xk--;
                m_assignment.reset(m_xk);
            }
        }

        void undo_new_level() {
            SASSERT(m_scope_lvl > 0);
            m_scope_lvl--;
            m_evaluator.pop(1);
        }

        void undo_updt_eq(atom * a) {
            if (m_var2eq.size() > m_xk)
                m_var2eq[m_xk] = a; 
        }

        template<typename Predicate>
        void undo_until(Predicate const & pred) {
            while (pred() && !m_trail.empty()) {
                trail & t = m_trail.back();
                switch (t.m_kind) {
                case trail::BVAR_ASSIGNMENT:
                    unassign_bool_var(t.m_b);
                    break;
                case trail::INFEASIBLE_UPDT:
                    undo_set_updt(t.m_old_set);
                    break;
                case trail::NEW_STAGE:
                    undo_new_stage();
                    break;
                case trail::NEW_LEVEL:
                    undo_new_level();
                    break;
                case trail::UPDT_EQ:
                    undo_updt_eq(t.m_old_eq);
                    break;
                default:
                    break;
                }
                m_trail.pop_back();
            }
        }
        
        struct size_pred {
            svector<trail> & m_trail;
            unsigned         m_old_size;
            size_pred(svector<trail> & trail, unsigned old_size):m_trail(trail), m_old_size(old_size) {}
            bool operator()() const { return m_trail.size() > m_old_size; }
        };
        
        // Keep undoing until trail has the given size
        void undo_until_size(unsigned old_size) {
            SASSERT(m_trail.size() >= old_size);
            undo_until(size_pred(m_trail, old_size));
        }

        struct stage_pred {
            var const & m_xk;
            var         m_target;
            stage_pred(var const & xk, var target):m_xk(xk), m_target(target) {}
            bool operator()() const { return m_xk != m_target; }
        };

        // Keep undoing until stage is new_xk
        void undo_until_stage(var new_xk) {
            undo_until(stage_pred(m_xk, new_xk));
        }

        struct level_pred {
            unsigned const & m_scope_lvl;
            unsigned         m_new_lvl;
            level_pred(unsigned const & scope_lvl, unsigned new_lvl):m_scope_lvl(scope_lvl), m_new_lvl(new_lvl) {}
            bool operator()() const { return m_scope_lvl > m_new_lvl; }
        };

        // Keep undoing until level is new_lvl
        void undo_until_level(unsigned new_lvl) {
            undo_until(level_pred(m_scope_lvl, new_lvl));
        }

        struct unassigned_pred {
            bool_var               m_b;
            std_vector<lbool> const & m_bvalues;
            unassigned_pred(std_vector<lbool> const & bvalues, bool_var b):
                m_b(b),
                m_bvalues(bvalues) {}
            bool operator()() const { return m_bvalues[m_b] != l_undef; }
        };

        // Keep undoing until b is unassigned
        void undo_until_unassigned(bool_var b) {
            undo_until(unassigned_pred(m_bvalues, b));
            SASSERT(m_bvalues[b] == l_undef);
        }

        struct true_pred {
            bool operator()() const { return true; }
        };

        void undo_until_empty() {
            undo_until(true_pred());
        }

        /**
           \brief Create a new scope level
        */
        void new_level() {
            m_evaluator.push();
            m_scope_lvl++;
            save_new_level_trail();
        }

        /**
           \brief Return the value of the given literal that was assigned by the search
           engine.
        */
        lbool assigned_value(literal l) const {
            bool_var b = l.var();
            if (l.sign())
                return ~m_bvalues[b];
            else
                return m_bvalues[b];
        }

        /**
           \brief Assign literal to true using the given justification
        */
        void set_literal_to_true(literal l, justification j) {
            TRACE(nlsat_assign,
                  tout << "literal" << l << "\n";
                  display(tout << "assigning literal to true: ", l) << "\n";
                  display(tout << " <- ", j););
                
            SASSERT(assigned_value(l) == l_undef);
            SASSERT(j != null_justification);
            SASSERT(!j.is_null());
            if (j.is_decision())
                m_stats.m_decisions++;
            else
                m_stats.m_propagations++;
            bool_var b   = l.var();
            m_bvalues[b] = to_lbool(!l.sign());
            m_levels[b]  = m_scope_lvl;
            m_justifications[b] = j;
            save_assign_trail(b);
            updt_eq(b, j);
            
            TRACE(nlsat_assign, tout << "b" << b << " -> " << m_bvalues[b]  << "\n";);
        }

        /**
           \brief Create a "case-split"
        */
        void decide_literal(literal l) {
            new_level();
            set_literal_to_true(l, decided_justification); // decided_justification is a constant
        }
        
        /**
           \brief Return the value of a literal as defined in Dejan and Leo's paper.
        */
        lbool value(literal l) {
            lbool val = assigned_value(l);
            if (val != l_undef) {            
                TRACE(nlsat_verbose, display(tout << " assigned value " << val << " for ", l) << "\n";);
                return val;
            }
            bool_var b = l.var();
            atom * a = m_atoms[b];
            if (a == nullptr) {
                TRACE(nlsat_verbose, display(tout << " no atom for ", l) << "\n";);
                return l_undef;
            }
            var max = a->max_var();
            if (!m_assignment.is_assigned(max)) {
                TRACE(nlsat_verbose, display(tout << " maximal variable not assigned ", l) << "\n";);
                return l_undef;
            }
            val = to_lbool(m_evaluator.eval(a, l.sign()));
            TRACE(nlsat_verbose, display(tout << " evaluated value " << val << " for ", l) << "\n";);
            TRACE(value_bug, tout << "value of: "; display(tout, l); tout << " := " << val << "\n"; 
                  tout << "xk: " << m_xk << ", a->max_var(): " << a->max_var() << "\n";
                  display_assignment(tout););            
            return val;
        }

        /**
           \brief Return true if the given clause is already satisfied in the current partial interpretation.
        */
        bool is_satisfied(clause const & cls) {
            for (literal l : cls) {
                if (const_cast<imp*>(this)->value(l) == l_true) {
                    TRACE(value_bug , tout << l << " := true\n";);
                    return true;
                }
            }
            return false;
        }

        /**
           \brief Return true if the given clause is false in the current partial interpretation.
        */
        bool is_inconsistent(unsigned sz, literal const * cls) {
            for (unsigned i = 0; i < sz; i++) {
                if (value(cls[i]) != l_false) {
                    TRACE(is_inconsistent, tout << "literal is not false:\n"; display(tout, cls[i]); tout << "\n";); 
                    return false;
                }
            }
            return true;
        }

        /**
           \brief Process a clauses that contains only Boolean literals.
        */
        literal_vector core;
        ptr_vector<clause> clauses;
        bool process_boolean_clause(const clause & cls) {
            SASSERT(m_xk == null_var);
            unsigned num_undef   = 0;
            unsigned first_undef = UINT_MAX;
            unsigned sz = cls.size();
            for (unsigned i = 0; i < sz; i++) {
                literal l = cls[i];
                SASSERT(m_atoms[l.var()] == nullptr);
                SASSERT(value(l) != l_true);
                if (value(l) == l_false)
                    continue;
                SASSERT(value(l) == l_undef);
                num_undef++;
                if (first_undef == UINT_MAX)
                    first_undef = i;
            }
            if (num_undef == 0) 
                return false;
            SASSERT(first_undef != UINT_MAX);
            if (num_undef == 1)
                set_literal_to_true(cls[first_undef], mk_clause_jst(&cls));
            else
                decide_literal(cls[first_undef]);
            return true;
        }
        
        /**
           \brief assign l to true, because l + (justification of) s is infeasible in RCF in the current interpretation.
        */
        void R_propagate(literal l, interval_set const * s, bool include_l = true) {
            m_ism.get_justifications(s, core, clauses);
            if (include_l) 
                core.push_back(~l);

            auto j = mk_lazy_jst(m_allocator, core.size(), core.data(), clauses.size(), clauses.data());
            TRACE(nlsat_resolve, display(tout << "justification: ", j);
                  display_eval(tout << "evaluated justification: ", j);
                );
            set_literal_to_true(l, j);
            SASSERT(value(l) == l_true);
        }
        
        /**
           \brief m_infeasible[m_xk] <- m_infeasible[m_xk] Union s
        */
        void updt_infeasible(interval_set const * s) {
            SASSERT(m_xk != null_var);
            interval_set * xk_set = m_infeasible[m_xk];
            save_set_updt_trail(xk_set);
            interval_set_ref new_set(m_ism);
            TRACE(nlsat_inf_set, tout << "updating infeasible set\n"; m_ism.display(tout, xk_set) << "\n"; m_ism.display(tout, s) << "\n";);
            new_set = m_ism.mk_union(s, xk_set);
            TRACE(nlsat_inf_set, tout << "new infeasible set:\n"; m_ism.display(tout, new_set) << "\n";);
            SASSERT(!m_ism.is_full(new_set));
            m_ism.inc_ref(new_set);
            m_infeasible[m_xk] = new_set;
        }

        /**
           \brief Update m_var2eq mapping.
        */
        void updt_eq(bool_var b, justification j) {
            if (!m_simplify_cores)
                return;
            if (m_bvalues[b] != l_true)
                return;
            atom * a = m_atoms[b];
            if (a == nullptr || a->get_kind() != atom::EQ || to_ineq_atom(a)->size() > 1 || to_ineq_atom(a)->is_even(0))
                return;
            switch (j.get_kind()) {
            case justification::CLAUSE:
                if (j.get_clause()->assumptions() != nullptr) return;
                break;            
            case justification::LAZY:
                if (j.get_lazy()->num_clauses() > 0) return;
                if (j.get_lazy()->num_lits() > 0) return;
                break;
            default:
                break;
            }
            var x = m_xk;
            SASSERT(a->max_var() == x);
            SASSERT(x != null_var);
            if (m_var2eq[x] != 0 && degree(m_var2eq[x]) <= degree(a))
                return; // we only update m_var2eq if the new equality has smaller degree
            TRACE(nlsat_simplify_core, tout << "Saving equality for "; m_display_var(tout, x) << " (x" << x << ") ";
                  tout << "scope-lvl: " << scope_lvl() << "\n"; display(tout, literal(b, false)) << "\n";
                  display(tout, j);
                );
            save_updt_eq_trail(m_var2eq[x]);
            m_var2eq[x] = a;
        }
        
        /**
           \brief Process a clause that contains only arithmetic literals
           If satisfy_learned is true, then learned clauses are satisfied even if m_lazy > 0
        */
        bool process_arith_clause(clause const & cls, bool satisfy_learned) {
            if (!satisfy_learned && m_lazy >= 2 && cls.is_learned()) {
                TRACE(nlsat, tout << "skip learned\n";);
                return true; // ignore lemmas in super lazy mode
            }
            SASSERT(m_xk == max_var(cls));
            unsigned num_undef   = 0;                // number of undefined literals
            unsigned first_undef = UINT_MAX;         // position of the first undefined literal
            interval_set_ref first_undef_set(m_ism); // infeasible region of the first undefined literal
            interval_set * xk_set = m_infeasible[m_xk]; // current set of infeasible interval for current variable
            TRACE(nlsat_inf_set, tout << "m_infeasible["<< debug_get_var_name(m_xk) << "]:";
                  m_ism.display(tout, xk_set) << "\n";);
            SASSERT(!m_ism.is_full(xk_set));
            for (unsigned idx = 0; idx < cls.size(); ++idx) {
                literal l = cls[idx];
                checkpoint();
                if (value(l) == l_false)
                    continue;
                if (value(l) == l_true)
                    return true;  // could happen if clause is a tautology
                CTRACE(nlsat, max_var(l) != m_xk || value(l) != l_undef, display(tout); 
                       tout << "xk: " << m_xk << ", max_var(l): " << max_var(l) << ", l: "; display(tout, l) << "\n";
                       display(tout << "cls: ", cls) << "\n";);
                SASSERT(value(l) == l_undef);
                SASSERT(max_var(l) == m_xk);
                bool_var b = l.var();
                atom * a   = m_atoms[b];
                SASSERT(a != nullptr);
                interval_set_ref curr_set(m_ism);
                curr_set = m_evaluator.infeasible_intervals(a, l.sign(), &cls);           
				TRACE(nlsat_inf_set, 
                      tout << "infeasible set for literal: "; display(tout, l); tout << "\n"; m_ism.display(tout, curr_set); tout << "\n";
                      display(tout << "cls: " , cls) << "\n";
                      tout << "m_xk:" << m_xk << "(" << debug_get_var_name(m_xk) << ")"<< "\n";);
                if (m_ism.is_empty(curr_set)) {
                    TRACE(nlsat_inf_set, tout << "infeasible set is empty, found literal\n";);
                    R_propagate(l, nullptr);
                    SASSERT(is_satisfied(cls));
                    return true;
                }
                if (m_ism.is_full(curr_set)) {
                    TRACE(nlsat_inf_set, tout << "infeasible set is R, skip literal\n";);
                    R_propagate(~l, nullptr);
                    continue;
                }
                if (m_ism.subset(curr_set, xk_set)) {
                    TRACE(nlsat_inf_set, tout << "infeasible set is a subset of current set, found literal\n";);
                    R_propagate(l, xk_set);
                    return true;
                }
                interval_set_ref tmp(m_ism);
                tmp = m_ism.mk_union(curr_set, xk_set);
                if (m_ism.is_full(tmp)) {
                    TRACE(nlsat_inf_set, tout << "infeasible set + current set = R, skip literal\n";
                          display(tout, cls) << "\n";
                          display_assignment_for_clause(tout, cls);
                          m_ism.display(tout, tmp); tout << "\n";
                        );
                    R_propagate(~l, tmp, false);
                    continue;
                }
                num_undef++;
                if (first_undef == UINT_MAX) {
                    first_undef = idx;
                    first_undef_set = curr_set;
                }
            }
            TRACE(nlsat_inf_set, tout << "num_undef: " << num_undef << "\n";);
            if (num_undef == 0) 
                return false;
            SASSERT(first_undef != UINT_MAX);
            if (num_undef == 1) {
                CTRACE(nlsat, cls.size() > 1,
                       tout << "num_undef=1, "; display(tout, cls) << "\n";
                       for (unsigned i = 0; i < cls.size(); i++) {
                           tout << value(cls[i]) << ", ";
                       }
                    );
                
                set_literal_to_true(cls[first_undef], mk_clause_jst(&cls));
                updt_infeasible(first_undef_set);
            }
            else if ( satisfy_learned ||
                      !cls.is_learned() /* must always satisfy input clauses */ ||
                      m_lazy == 0 /* if not in lazy mode, we also satiffy lemmas */) {
                decide_literal(cls[first_undef]);
                updt_infeasible(first_undef_set);
            }
            else {
                TRACE(nlsat_lazy, tout << "skipping clause, satisfy_learned: " << satisfy_learned << ", cls.is_learned(): " << cls.is_learned()
                      << ", lazy: " << m_lazy << "\n";);
            }
            return true;
        }

        /**
           \brief Try to satisfy the given clause. Return true if succeeded.

           If satisfy_learned is true, then (arithmetic) learned clauses are satisfied even if m_lazy > 0
        */
        bool process_clause(clause const & cls, bool satisfy_learned) {
            if (is_satisfied(cls))
                return true;
            if (m_xk == null_var)
                return process_boolean_clause(cls);
            else
                return process_arith_clause(cls, satisfy_learned);
        }

        /**
           \brief Try to satisfy the given "set" of clauses. 
           Return 0, if the set was satisfied, or the violating clause otherwise
        */
        clause * process_clauses(clause_vector const & cs) {
            TRACE(nlsat, tout << "clauses where max_var is " << m_xk << "("
                  << debug_get_var_name(m_xk) << "):\n"; display(tout, cs) << "\n";);
            for (clause* c : cs) {
                if (!process_clause(*c, false))
                    return c;
            }
            return nullptr; // succeeded
        }

        /**
           \brief Make sure m_bk is the first unassigned pure Boolean variable.
           Set m_bk == null_bool_var if there is no unassigned pure Boolean variable.
        */
        void peek_next_bool_var() {
            while (m_bk < m_atoms.size()) {
                if (!m_dead[m_bk] && m_atoms[m_bk] == nullptr && m_bvalues[m_bk] == l_undef) {
                    return;
                }
                m_bk++;
            }
            m_bk = null_bool_var;
        }

        /**
           \brief Create a new stage. See Dejan and Leo's paper.
        */
        void new_stage() {
            m_stats.m_stages++;
            save_new_stage_trail();
            if (m_xk == null_var)
                m_xk = 0;
            else {
                m_xk++;
            }
        }

        /**
           \brief Assign m_xk
        */
        void select_witness() {
            scoped_anum w(m_am);
            SASSERT(!m_ism.is_full(m_infeasible[m_xk]));
            m_ism.pick_in_complement(m_infeasible[m_xk], is_int(m_xk), w, m_randomize);
            TRACE(nlsat, tout << "infeasible intervals: "; m_ism.display(tout, m_infeasible[m_xk]); tout << "\n";
                  tout << "assigning "; m_display_var(tout, m_xk) << "(x" << m_xk << ") -> " << w << "\n";);
            TRACE(nlsat_root, tout << "value as root object: "; m_am.display_root(tout, w); tout << "\n";);
            if (!m_am.is_rational(w))
                m_stats.m_irrational_assignments++;
            m_assignment.set_core(m_xk, w);
        }

        bool is_satisfied() {
            if (m_bk == null_bool_var && m_xk >= num_vars()) {
                TRACE(nlsat, tout << "found model\n"; display_assignment(tout););
                fix_patch();
                SASSERT(check_satisfied(m_clauses));
                return true; // all variables were assigned, and all clauses were satisfied.
            }
            else {
                return false;
            }
        }

        /**
           \brief main procedure
        */
        lbool search() {
            TRACE(nlsat, tout << "starting search...\n"; display(tout); tout << "\nvar order:\n"; display_vars(tout););
            TRACE(nlsat_proof, tout << "ASSERTED\n"; display(tout););
            TRACE(nlsat_proof_sk, tout << "ASSERTED\n"; display_abst(tout);); 
            TRACE(nlsat_mathematica, display_mathematica(tout););
            TRACE(nlsat, display_smt2(tout););
            m_bk = 0;
            m_xk = null_var;

            while (true) {
                if (should_reorder())
                    do_reorder();

#if 0
                if (should_gc())
                    do_gc();
#endif

                if (should_simplify())
                    do_simplify();

                CASSERT("nlsat", check_satisfied());
                if (m_xk == null_var) {
                    peek_next_bool_var();
                    if (m_bk == null_bool_var) 
                        new_stage(); // move to arith vars
                }
                else {
                    new_stage(); // peek next arith var
                }
                TRACE(nlsat_bug, tout << "xk: x" << m_xk << " bk: b" << m_bk << "\n";);
                if (is_satisfied()) {
                    return l_true;
                }
                while (true) {
                    TRACE(nlsat_verbose, tout << "processing variable "; 
                          if (m_xk != null_var) {
                              m_display_var(tout, m_xk); tout << " " << m_watches[m_xk].size();
                          }
                          else {
                              tout << m_bwatches[m_bk].size() << " boolean b" << m_bk;
                          }
                          tout << "\n";);
                    checkpoint();
                    clause * conflict_clause;
                    if (m_xk == null_var)
                        conflict_clause = process_clauses(m_bwatches[m_bk]);
                    else 
                        conflict_clause = process_clauses(m_watches[m_xk]);
                    if (conflict_clause == nullptr)
                        break;
                    if (!resolve(*conflict_clause)) {
                        return l_false;
                    }
                    if (m_stats.m_conflicts >= m_max_conflicts)
                        return l_undef;
                    log();
                }
               
                if (m_xk == null_var) {
                    if (m_bvalues[m_bk] == l_undef) {
                        decide_literal(literal(m_bk, true));
                        m_bk++;
                    }
                }
                else {
                    select_witness();
                }
            }
        }

        void gc() {
            if (m_learned.size() <= 4*m_clauses.size())
                return;
            reset_watches();
            reinit_cache();
            unsigned j = 0;
            for (unsigned i = 0; i < m_learned.size(); ++i) {
                auto cls = m_learned[i];
                if (i - j < m_clauses.size() && cls->size() > 1 && !cls->is_active()) 
                    del_clause(cls);
                else {
                    m_learned[j++] = cls;
                    cls->set_active(false);
                }
            }
            m_learned.resize(j);
            reattach_arith_clauses(m_clauses);
            reattach_arith_clauses(m_learned);
        }


        bool should_gc() {
            return m_learned.size() > 10 * m_clauses.size();
        }

        void do_gc() {
            undo_to_base();
            gc();
        }

        void undo_to_base() {
            init_search();
            m_bk = 0;
            m_xk = null_var;
        }

        unsigned m_restart_threshold = 10000;
        bool should_reorder() {
            return m_stats.m_conflicts > 0 && m_stats.m_conflicts % m_restart_threshold == 0;
        }

        void do_reorder() {
            undo_to_base();
            m_stats.m_restarts++; 
            m_stats.m_conflicts++;
            if (m_reordered)
                restore_order();
            apply_reorder();
        }

        bool m_did_simplify = false;
        bool should_simplify() {
            return 
                !m_did_simplify && m_inline_vars && 
                !m_incremental && m_stats.m_conflicts > 100;
        }

        void do_simplify() {
            undo_to_base();
            m_did_simplify = true;
            m_simplify();
        }        

        unsigned m_next_conflict = 100;
        void log() {
            if (m_stats.m_conflicts != 1 && m_stats.m_conflicts < m_next_conflict)
                return;
            m_next_conflict += 100;
            IF_VERBOSE(2, verbose_stream() << "(nlsat :conflicts " << m_stats.m_conflicts 
                       << " :decisions " << m_stats.m_decisions 
                       << " :propagations " << m_stats.m_propagations 
                       << " :clauses " << m_clauses.size() 
                       << " :learned " << m_learned.size() << ")\n");
        }


        lbool search_check() {
            lbool r = l_undef;
            m_stats.m_conflicts = 0;
            m_stats.m_restarts = 0;
            m_next_conflict = 0;
            while (true) {
                r = search();
                if (r != l_true) 
                    break; 
                ++m_stats.m_restarts;
                vector<std::pair<var, rational>> bounds;                

                for (var x = 0; x < num_vars(); x++) {
                    if (is_int(x) && m_assignment.is_assigned(x) && !m_am.is_int(m_assignment.value(x))) {
                        scoped_anum v(m_am), vlo(m_am);
                        v = m_assignment.value(x);
                        rational lo;
                        m_am.int_lt(v, vlo);
                        if (!m_am.is_int(vlo)) 
                            continue;
                        m_am.to_rational(vlo, lo);
                        // derive tight bounds.
                        while (true) {
                            lo++;
                            if (!m_am.gt(v, lo.to_mpq())) { 
                                lo--; 
                                break; 
                            }
                        }
                        bounds.push_back(std::make_pair(x, lo));
                    }
                }
                if (bounds.empty()) 
                    break;

                gc();
                if (m_stats.m_restarts % 10 == 0) {
                    if (m_reordered)
                        restore_order();
                    apply_reorder();
                }

                init_search();
                IF_VERBOSE(2, verbose_stream() << "(nlsat-b&b :conflicts " << m_stats.m_conflicts 
                           << " :decisions " << m_stats.m_decisions 
                           << " :propagations " << m_stats.m_propagations 
                           << " :clauses " << m_clauses.size() 
                           << " :learned " << m_learned.size() << ")\n");
                for (auto const& b : bounds) {
                    var x = b.first;
                    rational lo = b.second;
                    rational hi = lo + 1; // rational::one();
                    bool is_even = false;                        
                    polynomial_ref p(m_pm);
                    rational one(1);
                    m_lemma.reset();
                    p = m_pm.mk_linear(1, &one, &x, -lo);
                    poly* p1 = p.get();
                    m_lemma.push_back(~mk_ineq_literal(atom::GT, 1, &p1, &is_even));
                    p = m_pm.mk_linear(1, &one, &x, -hi);
                    poly* p2 = p.get();
                    m_lemma.push_back(~mk_ineq_literal(atom::LT, 1, &p2, &is_even));
                    
                    // perform branch and bound
                    clause * cls = mk_clause(m_lemma.size(), m_lemma.data(), true, nullptr);
                    IF_VERBOSE(4, display(verbose_stream(), *cls) << "\n");
                    if (cls) {
                        TRACE(nlsat, display(tout << "conflict " << lo << " " << hi, *cls); tout << "\n";);
                    }
                }
            }
            return r;
        }

        bool m_reordered = false;
        bool simple_check() {
            literal_vector learned_unit;
            simple_checker checker(m_pm, m_am, m_clauses, learned_unit, m_atoms, m_is_int.size());
            if (!checker())
                return false;
            for (unsigned i = 0, sz = learned_unit.size(); i < sz; ++i) {
                clause *cla = mk_clause(1, &learned_unit[i], true, nullptr);
                if (m_atoms[learned_unit[i].var()] == nullptr) {
                    set_literal_to_true(learned_unit[i], mk_clause_jst(cla));
                }
            }
            return true;
        }


        void run_variable_ordering_strategy() {
            TRACE(reorder, tout << "runing vos: " << m_variable_ordering_strategy << '\n';);

            unsigned num = num_vars();
            vos_var_info_collector vos_collector(m_pm, m_atoms, num, m_variable_ordering_strategy);
            vos_collector.collect(m_clauses);
            vos_collector.collect(m_learned);
            
            var_vector perm;
            vos_collector(perm);
            reorder(perm.size(), perm.data());
        }

        void apply_reorder() {
            m_reordered = false;
            if (!can_reorder())
                ;
            else if (m_random_order) {
                shuffle_vars();
                m_reordered = true;
            }
            else if (m_reorder) {
                heuristic_reorder();
                m_reordered = true;
            }
        }

        lbool check() {
            TRACE(nlsat_smt2, display_smt2(tout););
            TRACE(nlsat_fd, tout << "is_full_dimensional: " << is_full_dimensional() << "\n";);
            init_search();
            m_explain.set_full_dimensional(is_full_dimensional());
            bool reordered = false;

           
            if (!can_reorder()) {

            }
            else if (m_variable_ordering_strategy > 0) {
                run_variable_ordering_strategy();
                reordered = true;
            }
            else if (m_random_order) {
                shuffle_vars();
                reordered = true;
            }
            else if (m_reorder) {
                heuristic_reorder();
                reordered = true;
            }
            sort_watched_clauses();
            lbool r = search_check();
            if (reordered) {
                restore_order();
            }
            CTRACE(nlsat_model, r == l_true, tout << "model\n"; display_assignment(tout, false););
            CTRACE(nlsat, r == l_false, display(tout << "unsat\n"););
            SASSERT(r != l_true || check_satisfied(m_clauses));
            return r;
        }

        

        void init_search() {
            undo_until_empty();
            while (m_scope_lvl > 0) {
                undo_new_level();
            }
            m_xk = null_var;
            for (unsigned i = 0; i < m_bvalues.size(); ++i) {
                m_bvalues[i] = l_undef;
            }
            m_assignment.reset();
        }

        lbool check(literal_vector& assumptions) {
            literal_vector result;
            unsigned sz = assumptions.size();
            literal const* ptr = assumptions.data();
            for (unsigned i = 0; i < sz; ++i) {
                mk_external_clause(1, ptr+i, (assumption)(ptr+i));
            }
            display_literal_assumption dla(*this, assumptions);
            scoped_display_assumptions _scoped_display(*this, dla);
            lbool r = check();

            if (r == l_false) {
                // collect used literals from m_lemma_assumptions
                vector<assumption, false> deps;
                get_core(deps);
                for (unsigned i = 0; i < deps.size(); ++i) {
                    literal const* lp = (literal const*)(deps[i]);
                    if (ptr <= lp && lp < ptr + sz) {
                        result.push_back(*lp);
                    } 
                }
            }
            collect(assumptions, m_clauses);
            collect(assumptions, m_learned);
            del_clauses(m_valids);
            
            if (m_check_lemmas)
                for (clause* c : m_learned) 
                    check_lemma(c->size(), c->data(), false, nullptr);
            
            assumptions.reset();
            assumptions.append(result);
            return r;
        }

        void get_core(vector<assumption, false>& deps) {
            m_asm.linearize(m_lemma_assumptions.get(), deps);
        }

        void collect(literal_vector const& assumptions, clause_vector& clauses) {
            unsigned j  = 0;
            for (clause * c : clauses) {
                if (collect(assumptions, *c)) {
                    del_clause(c);
                }
                else {
                    clauses[j++] = c;
                }
            }
            clauses.resize(j);
        }

        bool collect(literal_vector const& assumptions, clause const& c) {
            unsigned sz = assumptions.size();
            literal const* ptr = assumptions.data();            
            _assumption_set asms = static_cast<_assumption_set>(c.assumptions());
            if (asms == nullptr) {
                return false;
            }
            vector<assumption, false> deps;
            m_asm.linearize(asms, deps);
            for (auto dep : deps) {
                if (ptr <= dep && dep < ptr + sz) {
                    return true;
                }
            }
            return false;
        }

        // -----------------------
        //
        // Conflict Resolution
        //
        // -----------------------
        svector<char>          m_marks;        // bool_var -> bool  temp mark used during conflict resolution
        unsigned               m_num_marks;
        scoped_literal_vector  m_lemma;
        scoped_literal_vector  m_lazy_clause;
        assumption_set_ref     m_lemma_assumptions; // assumption tracking

        // Conflict resolution invariant: a marked literal is in m_lemma or on the trail stack.

        bool check_marks() {
            for (unsigned m : m_marks) {
                (void)m;
                SASSERT(m == 0);
            }
            return true;
        }
        
        unsigned scope_lvl() const { return m_scope_lvl; }
        
        bool is_marked(bool_var b) const { return m_marks.get(b, 0) == 1; }

        void mark(bool_var b) { m_marks.setx(b, 1, 0); }
        
        void reset_mark(bool_var b) { m_marks[b] = 0; }

        void reset_marks() {
            for (auto const& l : m_lemma) {
                reset_mark(l.var());
            }
        }

        void process_antecedent(literal antecedent) {
            checkpoint();
            bool_var b  = antecedent.var();
            TRACE(nlsat_resolve, display(tout << "resolving antecedent: ", antecedent) << "\n";);
            if (assigned_value(antecedent) == l_undef) {
                checkpoint();
                // antecedent must be false in the current arith interpretation
                SASSERT(value(antecedent) == l_false || m_rlimit.is_canceled());
                if (!is_marked(b)) {
                    SASSERT(is_arith_atom(b) && max_var(b) < m_xk); // must be in a previous stage
                    TRACE(nlsat_resolve, tout << "marking an unmarked literal, it is unassigned, but it is false in arithmetic interpretation, adding it to lemma\n";); 
                    mark(b);
                    m_lemma.push_back(antecedent);
                }
                return;
            }
            
            unsigned b_lvl = m_levels[b];
            TRACE(nlsat_resolve, tout << "b_lvl: " << b_lvl << ", is_marked(b): " << is_marked(b) << ", m_num_marks: " << m_num_marks << "\n";);
            if (!is_marked(b)) {
                mark(b);
                if (b_lvl == scope_lvl() /* same level */ && max_var(b) == m_xk /* same stage */) {
                    TRACE(nlsat_resolve, tout << "literal is in the same level and stage, increasing marks\n";);
                    m_num_marks++;
                }
                else {
                    TRACE(nlsat_resolve, tout << "previous level or stage, adding literal to lemma\n";
                          tout << "max_var(b): " << max_var(b) << ", m_xk: " << m_xk << ", lvl: " << b_lvl << ", scope_lvl: " << scope_lvl() << "\n";);
                    m_lemma.push_back(antecedent);
                }
            }
        }

        void resolve_clause(bool_var b, unsigned sz, literal const * c) {
            TRACE(nlsat_proof, tout << "resolving "; if (b != null_bool_var) display_atom(tout, b) << "\n"; display(tout, sz, c); tout << "\n";);
            TRACE(nlsat_proof_sk, tout << "resolving "; if (b != null_bool_var) tout << "b" << b; tout << "\n"; display_abst(tout, sz, c); tout << "\n";); 

            for (unsigned i = 0; i < sz; i++) {
                if (c[i].var() != b)
                    process_antecedent(c[i]);
            }
        }

        void resolve_clause(bool_var b, clause & c) {
            TRACE(nlsat_resolve, tout << "resolving clause "; if (b != null_bool_var) tout << "for b: " << b << "\n"; display(tout, c) << "\n";);
            c.set_active(true);
            resolve_clause(b, c.size(), c.data());
            m_lemma_assumptions = m_asm.mk_join(static_cast<_assumption_set>(c.assumptions()), m_lemma_assumptions);
        }

        std::ostream& print_out_as_math(std::ostream& out, lazy_justification const & jst) {
            literal_vector core;
            for (unsigned i = 0; i < jst.num_lits(); i++) {
                core.push_back(~jst.lit(i));
            }
            display_mathematica_lemma(out, core.size(), core.data(), true);
            return out;
        }
        
        void resolve_lazy_justification(bool_var b, lazy_justification const & jst) {
            TRACE(nlsat_resolve, tout << "resolving lazy_justification for b" << b << "\n";);
            unsigned sz = jst.num_lits();

            // Dump lemma as Mathematica formula that must be true,
            // if the current interpretation (really) makes the core in jst infeasible.
            TRACE(nlsat_mathematica, tout << "assignment lemma\n"; print_out_as_math(tout, jst););
            if (m_dump_mathematica) {
//                verbose_stream() << "assignment lemma in matematica\n";
                print_out_as_math(verbose_stream(), jst) << std::endl;
//                verbose_stream() << "\nend of assignment lemma\n";
            }

            
            
            
            m_lazy_clause.reset();
            m_explain.main_operator(jst.num_lits(), jst.lits(), m_lazy_clause);
            for (unsigned i = 0; i < sz; i++)
                m_lazy_clause.push_back(~jst.lit(i));
            
            // lazy clause is a valid clause
            TRACE(nlsat_mathematica, display_mathematica_lemma(tout, m_lazy_clause.size(), m_lazy_clause.data()););
            if (m_dump_mathematica) {
//                verbose_stream() << "lazy clause\n";
                display_mathematica_lemma(verbose_stream(), m_lazy_clause.size(), m_lazy_clause.data()) << std::endl;
//                verbose_stream() << "\nend of lazy\n";
            }
            
            TRACE(nlsat_proof_sk, tout << "theory lemma\n"; display_abst(tout, m_lazy_clause.size(), m_lazy_clause.data()); tout << "\n";); 
            TRACE(nlsat_resolve, 
                  tout << "m_xk: " << m_xk << ", "; m_display_var(tout, m_xk) << "\n";
                  tout << "new valid clause:\n";
                  display(tout, m_lazy_clause.size(), m_lazy_clause.data()) << "\n";);

            
            if (m_log_lemmas)
                log_lemma(verbose_stream(), m_lazy_clause.size(), m_lazy_clause.data(), true);

            if (m_check_lemmas) {
                check_lemma(m_lazy_clause.size(), m_lazy_clause.data(), false, nullptr);
                m_valids.push_back(mk_clause_core(m_lazy_clause.size(), m_lazy_clause.data(), false, nullptr));
            }
            
#ifdef Z3DEBUG
            {
                unsigned sz = m_lazy_clause.size();
                for (unsigned i = 0; i < sz; i++) {
                    literal l = m_lazy_clause[i];
                    if (l.var() != b) {
                        if (value(l) != l_false)
                            display(verbose_stream() << value(l) << " ", 1, &l);
                        SASSERT(value(l) == l_false || m_rlimit.is_canceled());
                    }
                    else {
                        SASSERT(value(l) == l_true || m_rlimit.is_canceled());
                        SASSERT(!l.sign() || m_bvalues[b] == l_false);
                        SASSERT(l.sign()  || m_bvalues[b] == l_true);
                    }
                }
            }
#endif
            checkpoint();
            resolve_clause(b, m_lazy_clause.size(), m_lazy_clause.data());

            for (unsigned i = 0; i < jst.num_clauses(); ++i) {
                clause const& c = jst.clause(i);
                TRACE(nlsat, display(tout << "adding clause assumptions ", c) << "\n";);
                m_lemma_assumptions = m_asm.mk_join(static_cast<_assumption_set>(c.assumptions()), m_lemma_assumptions);
            }
        }
        
        /**
           \brief Return true if all literals in ls are from previous stages.
        */
        bool only_literals_from_previous_stages(unsigned num, literal const * ls) const {
            for (unsigned i = 0; i < num; i++) {
                if (max_var(ls[i]) == m_xk)
                    return false;
            }
            return true;
        }

        /**
           \brief Return the maximum scope level in ls. 
           
           \pre This method assumes value(ls[i]) is l_false for i in [0, num)
        */
        unsigned max_scope_lvl(unsigned num, literal const * ls) {
            unsigned max = 0;
            for (unsigned i = 0; i < num; i++) {
                literal l = ls[i];
                bool_var b = l.var();
                SASSERT(value(ls[i]) == l_false);
                if (assigned_value(l) == l_false) {
                    unsigned lvl = m_levels[b];
                    if (lvl > max)
                        max = lvl;
                }
                else {
                    // l must be a literal from a previous stage that is false in the current interpretation
                    SASSERT(assigned_value(l) == l_undef);
                    SASSERT(max_var(b) != null_var);
                    SASSERT(m_xk       != null_var);
                    SASSERT(max_var(b) < m_xk);
                }
            }
            return max;
        }

        /**
           \brief Remove literals of the given lvl (that are in the current stage) from lemma.

           \pre This method assumes value(ls[i]) is l_false for i in [0, num)
        */
        void remove_literals_from_lvl(scoped_literal_vector & lemma, unsigned lvl) {
            TRACE(nlsat_resolve, tout << "removing literals from lvl: " << lvl << " and stage " << m_xk << "\n";);
            unsigned sz = lemma.size();
            unsigned j  = 0;
            for (unsigned i = 0; i < sz; i++) {
                literal l = lemma[i];
                bool_var b = l.var();
                SASSERT(is_marked(b));
                SASSERT(value(lemma[i]) == l_false);
                if (assigned_value(l) == l_false && m_levels[b] == lvl && max_var(b) == m_xk) {
                    m_num_marks++;
                    continue;
                }
                lemma.set(j, l);
                j++;
            }
            lemma.shrink(j);
        }

        /**
           \brief Return true if it is a Boolean lemma.
        */
        bool is_bool_lemma(unsigned sz, literal const * ls) const {
            for (unsigned i = 0; i < sz; i++) {
                if (m_atoms[ls[i].var()] != nullptr)
                    return false;
            }
            return true;
        }


        /** 
            Return the maximal decision level in lemma for literals in the first sz-1 positions that 
            are at the same stage. If all these literals are from previous stages,
            we just backtrack the current level.
        */
        unsigned find_new_level_arith_lemma(unsigned sz, literal const * lemma) {
            SASSERT(!is_bool_lemma(sz, lemma));
            unsigned new_lvl = 0;
            bool found_lvl   = false;
            for (unsigned i = 0; i < sz - 1; i++) {
                literal l = lemma[i];
                if (max_var(l) == m_xk) {
                    bool_var b = l.var();
                    if (!found_lvl) {
                        found_lvl = true;
                        new_lvl   = m_levels[b];
                    }
                    else {
                        if (m_levels[b] > new_lvl)
                            new_lvl = m_levels[b];
                    }
                }
            }
            SASSERT(!found_lvl || new_lvl < scope_lvl());
            if (!found_lvl) {
                TRACE(nlsat_resolve, tout << "fail to find new lvl, using previous one\n";);
                new_lvl = scope_lvl() - 1;
            }
            return new_lvl;
        }

        struct scoped_reset_marks {
            imp& i;
            scoped_reset_marks(imp& i):i(i) {}
            ~scoped_reset_marks() { if (i.m_num_marks > 0) { i.m_num_marks = 0; for (char& m : i.m_marks) m = 0; } }
        };


        /**
           \brief Return true if the conflict was solved.
        */
        bool resolve(clause & conflict) {
            clause * conflict_clause = &conflict;
            m_lemma_assumptions = nullptr;
        start:
            SASSERT(check_marks());
            TRACE(nlsat_proof, tout << "STARTING RESOLUTION\n";);
            TRACE(nlsat_proof_sk, tout << "STARTING RESOLUTION\n";);
            m_stats.m_conflicts++;
            TRACE(nlsat, tout << "resolve, conflicting clause:\n"; display(tout, *conflict_clause) << "\n";
                  tout << "xk: "; if (m_xk != null_var) m_display_var(tout, m_xk); else tout << "<null>"; tout << "\n";
                  tout << "scope_lvl: " << scope_lvl() << "\n";
                  // tout << "current assignment\n"; display_assignment(tout);
                );
            
            m_num_marks = 0;
            m_lemma.reset();
            m_lemma_assumptions = nullptr;
            scoped_reset_marks _sr(*this);
            resolve_clause(null_bool_var, *conflict_clause);

            unsigned top = m_trail.size();
            bool found_decision;
            while (true) {
                found_decision = false;
                while (m_num_marks > 0) {
                    checkpoint();
                    SASSERT(top > 0);
                    trail & t = m_trail[top-1];
                    SASSERT(t.m_kind != trail::NEW_STAGE); // we only mark literals that are in the same stage
                    if (t.m_kind == trail::BVAR_ASSIGNMENT) {
                        bool_var b = t.m_b;
                        if (is_marked(b)) {
                            TRACE(nlsat_resolve, tout << "found marked: b" << b << "\n"; display_atom(tout, b) << "\n";);
                            m_num_marks--;
                            reset_mark(b);
                            justification jst = m_justifications[b];
                            switch (jst.get_kind()) {
                            case justification::CLAUSE:
                                resolve_clause(b, *(jst.get_clause()));
                                break;
                            case justification::LAZY:
                                resolve_lazy_justification(b, *(jst.get_lazy()));
                                break;
                            case justification::DECISION:
                                SASSERT(m_num_marks == 0);
                                found_decision = true;
                                TRACE(nlsat_resolve, tout << "found decision\n";);
                                m_lemma.push_back(literal(b, m_bvalues[b] == l_true));
                                break;
                            default:
                                UNREACHABLE();
                                break;
                            }
                        }
                    }
                    top--;
                }

                // m_lemma is an implicating clause after backtracking current scope level.
                if (found_decision)
                    break;

                // If lemma only contains literals from previous stages, then we can stop.
                // We make progress by returning to a previous stage with additional information (new lemma)
                // that forces us to select a new partial interpretation
                if (only_literals_from_previous_stages(m_lemma.size(), m_lemma.data()))
                    break;
                
                // Conflict does not depend on the current decision, and it is still in the current stage.
                // We should find
                //    - the maximal scope level in the lemma
                //    - remove literal assigned in the scope level from m_lemma
                //    - backtrack to this level
                //    - and continue conflict resolution from there
                //    - we must bump m_num_marks for literals removed from m_lemma
                unsigned max_lvl = max_scope_lvl(m_lemma.size(), m_lemma.data());
                TRACE(nlsat_resolve, tout << "conflict does not depend on current decision, backtracking to level: " << max_lvl << "\n";);
                SASSERT(max_lvl < scope_lvl());
                remove_literals_from_lvl(m_lemma, max_lvl);
                undo_until_level(max_lvl);
                top = m_trail.size();
                TRACE(nlsat_resolve, tout << "scope_lvl: " << scope_lvl() << " num marks: " << m_num_marks << "\n";);
                SASSERT(scope_lvl() == max_lvl);
            }

            TRACE(nlsat_proof, tout << "New lemma\n"; display(tout, m_lemma); tout << "\n=========================\n";);
            TRACE(nlsat_proof_sk, tout << "New lemma\n"; display_abst(tout, m_lemma); tout << "\n=========================\n";);

            if (m_lemma.empty()) {
                TRACE(nlsat, tout << "empty clause generated\n";);
                return false; // problem is unsat, empty clause was generated
            }

            reset_marks(); // remove marks from the literals in m_lemmas.
            TRACE(nlsat, tout << "new lemma:\n"; display(tout, m_lemma.size(), m_lemma.data()); tout << "\n";
                  tout << "found_decision: " << found_decision << "\n";);
            
            if (m_check_lemmas) {
                check_lemma(m_lemma.size(), m_lemma.data(), false, m_lemma_assumptions.get());
            }

            if (m_log_lemmas) 
                log_lemma(verbose_stream(), m_lemma.size(), m_lemma.data(), false);
    
            // There are two possibilities:
            // 1) m_lemma contains only literals from previous stages, and they
            //    are false in the current interpretation. We make progress 
            //    by returning to a previous stage with additional information (new clause)
            //    that forces us to select a new partial interpretation
            //    >>> Return to some previous stage (we may also backjump many decisions and stages).
            //    
            // 2) m_lemma contains at most one literal from the current level (the last literal).
            //    Moreover, this literal was a decision, but the new lemma forces it to 
            //    be assigned to a different value.
            //    >>> In this case, we remain in the same stage but, we add a new asserted literal
            //        in a previous scope level. We may backjump many decisions.
            //
            unsigned sz = m_lemma.size();
            clause * new_cls = nullptr;
            if (!found_decision) {
                // Case 1)
                // We just have to find the maximal variable in m_lemma, and return to that stage
                // Remark: the lemma may contain only boolean literals, in this case new_max_var == null_var;
                var new_max_var = max_var(sz, m_lemma.data());
                TRACE(nlsat_resolve, tout << "backtracking to stage: " << new_max_var << ", curr: " << m_xk << "\n";);
                undo_until_stage(new_max_var);
                SASSERT(m_xk == new_max_var);
                new_cls = mk_clause(sz, m_lemma.data(), true, m_lemma_assumptions.get());
                TRACE(nlsat, tout << "new_level: " << scope_lvl() << "\nnew_stage: " << new_max_var; 
                      if (new_max_var != null_var) {tout << "("; m_display_var(tout, new_max_var) << ")\n";});
            }
            else {
                SASSERT(scope_lvl() >= 1);
                // Case 2)
                if (is_bool_lemma(m_lemma.size(), m_lemma.data())) {
                    // boolean lemma, we just backtrack until the last literal is unassigned.
                    bool_var max_bool_var = m_lemma[m_lemma.size()-1].var();
                    undo_until_unassigned(max_bool_var);
                }
                else {
                    // We must find the maximal decision level in literals in the first sz-1 positions that 
                    // are at the same stage. If all these literals are from previous stages,
                    // we just backtrack the current level.
                    unsigned new_lvl = find_new_level_arith_lemma(m_lemma.size(), m_lemma.data());
                    TRACE(nlsat, tout << "backtracking to new level: " << new_lvl << ", curr: " << m_scope_lvl << "\n";);
                    undo_until_level(new_lvl);
                }

                if (lemma_is_clause(*conflict_clause)) {
                    TRACE(nlsat, tout << "found decision literal in conflict clause\n";);
                    VERIFY(process_clause(*conflict_clause, true));
                    return true;
                }
                new_cls = mk_clause(sz, m_lemma.data(), true, m_lemma_assumptions.get());                
            }
            NLSAT_VERBOSE(display(verbose_stream(), *new_cls) << "\n";);
            if (!process_clause(*new_cls, true)) {
                TRACE(nlsat, tout << "new clause triggered another conflict, restarting conflict resolution...\n";
                      display(tout, *new_cls) << "\n";
                    );
                // we are still in conflict
                conflict_clause = new_cls;
                goto start;
            }
            TRACE(nlsat_resolve_done, display_assignment(tout););
            return true;
        }

        bool lemma_is_clause(clause const& cls) const {
            bool same = (m_lemma.size() == cls.size());
            for (unsigned i = 0; same && i < m_lemma.size(); ++i) {
                same = m_lemma[i] == cls[i];
            }
            return same;
        }


        // -----------------------
        //
        // Debugging
        //
        // -----------------------
        
        bool check_watches() const {
#ifdef Z3DEBUG
            for (var x = 0; x < num_vars(); x++) {
                clause_vector const & cs = m_watches[x];
                unsigned sz = cs.size();
                for (unsigned i = 0; i < sz; i++) {
                    SASSERT(max_var(*(cs[i])) == x);
                }
            }
#endif            
            return true;
        }

        bool check_bwatches() const {
#ifdef Z3DEBUG
            for (bool_var b = 0; b < m_bwatches.size(); b++) {
                clause_vector const & cs = m_bwatches[b];
                unsigned sz = cs.size();
                for (unsigned i = 0; i < sz; i++) {
                    clause const & c = *(cs[i]);
                    (void)c;
                    SASSERT(max_var(c) == null_var);
                    SASSERT(max_bvar(c) == b);
                }
            }
#endif                
            return true;
        }

        bool check_invariant() const {
            SASSERT(check_watches());
            SASSERT(check_bwatches());
            return true;
        }

        bool check_satisfied(clause_vector const & cs) {
            unsigned sz = cs.size();
            for (unsigned i = 0; i < sz; i++) {
                clause const & c = *(cs[i]);
                if (!is_satisfied(c)) {
                    TRACE(nlsat, tout << "not satisfied\n"; display(tout, c); tout << "\n";); 
                    return false;
                }
            }
            return true;
        }

        bool check_satisfied() {
            TRACE(nlsat, tout << "bk: b" << m_bk << ", xk: x" << m_xk << "\n"; if (m_xk != null_var) { m_display_var(tout, m_xk); tout << "\n"; });
            unsigned num = usize(m_atoms);
            if (m_bk != null_bool_var)
                num = m_bk;
            for (bool_var b = 0; b < num; b++) {
                if (!check_satisfied(m_bwatches[b])) {
                    UNREACHABLE();
                    return false;
                }
            }
            if (m_xk != null_var) {
                for (var x = 0; x < m_xk; x++) {
                    if (!check_satisfied(m_watches[x])) {
                        UNREACHABLE();
                        return false;
                    }
                }
            }
            return true;
        }
        
        // -----------------------
        //
        // Statistics
        //
        // -----------------------

        void collect_statistics(statistics & st) {
            st.update("nlsat conflicts", m_stats.m_conflicts);
            st.update("nlsat propagations", m_stats.m_propagations);
            st.update("nlsat decisions", m_stats.m_decisions);
            st.update("nlsat restarts", m_stats.m_restarts);
            st.update("nlsat stages", m_stats.m_stages);
            st.update("nlsat simplifications", m_stats.m_simplifications);
            st.update("nlsat irrational assignments", m_stats.m_irrational_assignments);
        }

        void reset_statistics() {
            m_stats.reset();
        }

        // -----------------------
        //
        // Variable reordering
        //
        // -----------------------

        struct var_info_collector {
            pmanager &          pm;
            atom_vector const & m_atoms;
            var_vector          m_shuffle;
            unsigned_vector     m_max_degree;
            unsigned_vector     m_num_occs;

            var_info_collector(pmanager & _pm, atom_vector const & atoms, unsigned num_vars):
                pm(_pm),
                m_atoms(atoms) {
                m_max_degree.resize(num_vars, 0);
                m_num_occs.resize(num_vars, 0);
            }

            var_vector      m_vars;
            void collect(poly * p) {
                m_vars.reset();
                pm.vars(p, m_vars);
                unsigned sz = m_vars.size(); 
                for (unsigned i = 0; i < sz; i++) {
                    var x      = m_vars[i];
                    unsigned k = pm.degree(p, x);
                    m_num_occs[x]++;
                    if (k > m_max_degree[x])
                        m_max_degree[x] = k;
                }
            }

            void collect(literal l) {
                bool_var b = l.var();
                atom * a = m_atoms[b];
                if (a == nullptr)
                    return;
                if (a->is_ineq_atom()) {
                    unsigned sz = to_ineq_atom(a)->size();
                    for (unsigned i = 0; i < sz; i++) {
                        collect(to_ineq_atom(a)->p(i));
                    }
                }
                else {
                    collect(to_root_atom(a)->p());
                }
            }
            
            void collect(clause const & c) {
                unsigned sz = c.size();
                for (unsigned i = 0; i < sz; i++) 
                    collect(c[i]);
            }

            void collect(clause_vector const & cs) {
                unsigned sz = cs.size();
                for (unsigned i = 0; i < sz; i++) 
                    collect(*(cs[i]));
            }

            std::ostream& display(std::ostream & out, display_var_proc const & proc) {
                unsigned sz = m_num_occs.size();
                for (unsigned i = 0; i < sz; i++) {
                    proc(out, i); out << " -> " << m_max_degree[i] << " : " << m_num_occs[i] << "\n";
                }
                return out;
            }
        };
        
        struct reorder_lt {
            var_info_collector const & m_info;
            reorder_lt(var_info_collector const & info):m_info(info) {}
            bool operator()(var x, var y) const {
                // high degree first
                if (m_info.m_max_degree[x] < m_info.m_max_degree[y])
                    return false;
                if (m_info.m_max_degree[x] > m_info.m_max_degree[y])
                    return true;
                // more constrained first
                if (m_info.m_num_occs[x] < m_info.m_num_occs[y])
                    return false;
                if (m_info.m_num_occs[x] > m_info.m_num_occs[y])
                    return true;
                return m_info.m_shuffle[x] < m_info.m_shuffle[y];
            }
        };

        // Order variables by degree and number of occurrences
        void heuristic_reorder() {
            unsigned num = num_vars();
            var_info_collector collector(m_pm, m_atoms, num);
            collector.collect(m_clauses);
            collector.collect(m_learned);
            init_shuffle(collector.m_shuffle);
            TRACE(nlsat_reorder, collector.display(tout, m_display_var););
            var_vector new_order;
            for (var x = 0; x < num; x++) 
                new_order.push_back(x);
            
            std::sort(new_order.begin(), new_order.end(), reorder_lt(collector));
            TRACE(nlsat_reorder, 
                  tout << "new order: "; for (unsigned i = 0; i < num; i++) tout << new_order[i] << " "; tout << "\n";);
            var_vector perm;
            perm.resize(num, 0);
            for (var x = 0; x < num; x++) {
                perm[new_order[x]] = x;
            }
            reorder(perm.size(), perm.data());
            SASSERT(check_invariant());
        }

        void init_shuffle(var_vector& p) {
            unsigned num = num_vars();
            for (var x = 0; x < num; x++)
                p.push_back(x);

            random_gen r(++m_random_seed);
            shuffle(p.size(), p.data(), r);
        }

        void shuffle_vars() {
            var_vector p;
            init_shuffle(p);
            reorder(p.size(), p.data());
        }

        bool can_reorder() const {
            return all_of(m_learned, [&](clause* c) { return !has_root_atom(*c); }) 
                && all_of(m_clauses, [&](clause* c) { return !has_root_atom(*c); });
        }

        /**
           \brief Reorder variables using the giving permutation.
           p maps internal variables to their new positions
        */


        void reorder(unsigned sz, var const * p) {

            remove_learned_roots();
            SASSERT(can_reorder());
            TRACE(nlsat_reorder, tout << "solver before variable reorder\n"; display(tout);
                  display_vars(tout);
                  tout << "\npermutation:\n";
                  for (unsigned i = 0; i < sz; i++) tout << p[i] << " "; tout << "\n";                  
                );
            // verbose_stream() << "\npermutation: " << p[0] << " count " << count << " " << m_rlimit.is_canceled() << "\n";
            reinit_cache();
            SASSERT(num_vars() == sz);
            TRACE(nlsat_bool_assignment_bug, tout << "before reset watches\n"; display_bool_assignment(tout););
            reset_watches();
            assignment new_assignment(m_am);
            for (var x = 0; x < num_vars(); x++) {
                if (m_assignment.is_assigned(x)) 
                    new_assignment.set(p[x], m_assignment.value(x));
            }
            var_vector new_inv_perm;
            new_inv_perm.resize(sz);
            // the undo_until_size(0) statement erases the Boolean assignment.
            // undo_until_size(0)
            undo_until_stage(null_var);
            m_cache.reset();               
#ifdef Z3DEBUG
            for (var x = 0; x < num_vars(); x++) {
                SASSERT(m_watches[x].empty());
            }
#endif            
            // update m_perm mapping
            for (unsigned ext_x = 0; ext_x < sz; ext_x++) {
                // p: internal -> new pos
                // m_perm: internal -> external
                // m_inv_perm: external -> internal
                new_inv_perm[ext_x] = p[m_inv_perm[ext_x]];
                m_perm.set(new_inv_perm[ext_x], ext_x);
            }
            bool_vector is_int;
            is_int.swap(m_is_int);
            for (var x = 0; x < sz; x++) {
                m_is_int.setx(p[x], is_int[x], false);
                SASSERT(m_infeasible[x] == 0);
            }
            m_inv_perm.swap(new_inv_perm);
#ifdef Z3DEBUG
            for (var x = 0; x < num_vars(); x++) {
                SASSERT(x == m_inv_perm[m_perm[x]]);
                SASSERT(m_watches[x].empty());
            }
#endif            
            m_pm.rename(sz, p);
            for (auto& b : m_bounds) 
                b.x = p[b.x];                                   
            TRACE(nlsat_bool_assignment_bug, tout << "before reinit cache\n"; display_bool_assignment(tout););
            reinit_cache();
            m_assignment.swap(new_assignment);
            reattach_arith_clauses(m_clauses);
            reattach_arith_clauses(m_learned);
            TRACE(nlsat_reorder, tout << "solver after variable reorder\n"; display(tout); display_vars(tout););
        }

        
        /**
           \brief Restore variable order.
        */
        void restore_order() {
            // m_perm: internal -> external
            // m_inv_perm: external -> internal            
            var_vector p;
            p.append(m_perm);
            reorder(p.size(), p.data());
#ifdef Z3DEBUG
            for (var x = 0; x < num_vars(); x++) {
                SASSERT(m_perm[x] == x);
                SASSERT(m_inv_perm[x] == x);
            }
#endif            
        }

        /**
           \brief After variable reordering some lemmas containing root atoms may be ill-formed.
        */
        void remove_learned_roots() {
            unsigned j  = 0;
            for (clause* c : m_learned) {
                if (has_root_atom(*c)) {
                    del_clause(c);
                }
                else {
                    m_learned[j++] = c;
                }
            }
            m_learned.resize(j);
        }

        /** 
            \brief Return true if the clause contains an ill formed root atom
        */
        bool has_root_atom(clause const & c) const {
            for (literal lit : c) {
                bool_var b = lit.var();
                atom * a = m_atoms[b];
                if (a && a->is_root_atom()) 
                    return true;
            }
            return false;
        }

        /**
           \brief reinsert all polynomials in the unique cache
        */
        void reinit_cache() {
            reinit_cache(m_clauses);
            reinit_cache(m_learned);
            for (atom* a : m_atoms) 
                reinit_cache(a);            
        }
        void reinit_cache(clause_vector const & cs) {
            for (clause* c : cs) 
                reinit_cache(*c);
        }
        void reinit_cache(clause const & c) {
            for (literal l : c) 
                reinit_cache(l);
        }
        void reinit_cache(literal l) {
            bool_var b = l.var();
            reinit_cache(m_atoms[b]);
        }
        void reinit_cache(atom* a) {
            if (a == nullptr) {

            }
            else if (a->is_ineq_atom()) {
                var max = 0;
                unsigned sz = to_ineq_atom(a)->size();
                for (unsigned i = 0; i < sz; i++) {
                    poly * p = to_ineq_atom(a)->p(i);
                    VERIFY(m_cache.mk_unique(p) == p);
                    var x = m_pm.max_var(p);
                    if (x > max)
                        max = x;
                }
                a->m_max_var = max;
            }
            else {
                poly * p = to_root_atom(a)->p();
                VERIFY(m_cache.mk_unique(p) == p);
                a->m_max_var = m_pm.max_var(p);
            }
        }

        void reset_watches() {
            unsigned num = num_vars();
            for (var x = 0; x < num; x++) {
                m_watches[x].clear();
            }
        }

        void reattach_arith_clauses(clause_vector const & cs) {
            for (clause* cp : cs) {
                var x = max_var(*cp);
                if (x != null_var)
                    m_watches[x].push_back(cp);
            }
        }

        // -----------------------
        //
        // Solver initialization
        //
        // -----------------------
        
        struct degree_lt {
            unsigned_vector & m_degrees;
            degree_lt(unsigned_vector & ds):m_degrees(ds) {}
            bool operator()(unsigned i1, unsigned i2) const { 
                if (m_degrees[i1] < m_degrees[i2])
                    return true;
                if (m_degrees[i1] > m_degrees[i2])
                    return false;
                return i1 < i2;
            }
        };

        unsigned_vector m_cs_degrees;
        unsigned_vector m_cs_p;
        void sort_clauses_by_degree(unsigned sz, clause ** cs) {
            if (sz <= 1)
                return;
            TRACE(nlsat_reorder_clauses, tout << "before:\n"; for (unsigned i = 0; i < sz; i++) { display(tout, *(cs[i])); tout << "\n"; });
            m_cs_degrees.reset();
            m_cs_p.reset();
            for (unsigned i = 0; i < sz; i++) {
                m_cs_p.push_back(i);
                m_cs_degrees.push_back(degree(*(cs[i])));
            }
            std::sort(m_cs_p.begin(), m_cs_p.end(), degree_lt(m_cs_degrees));
            TRACE(nlsat_reorder_clauses, tout << "permutation: "; ::display(tout, m_cs_p.begin(), m_cs_p.end()); tout << "\n";);
            apply_permutation(sz, cs, m_cs_p.data());
            TRACE(nlsat_reorder_clauses, tout << "after:\n"; for (unsigned i = 0; i < sz; i++) { display(tout, *(cs[i])); tout << "\n"; });
        }

        
        struct degree_lit_num_lt {
            unsigned_vector & m_degrees;
            unsigned_vector & m_lit_num;
            degree_lit_num_lt(unsigned_vector & ds, unsigned_vector & ln) :
                m_degrees(ds),
                m_lit_num(ln) {
            }
            bool operator()(unsigned i1, unsigned i2) const {
                if (m_lit_num[i1] == 1 && m_lit_num[i2] > 1)
                    return true;
                if (m_lit_num[i1] > 1 && m_lit_num[i2] == 1)
                    return false;
                if (m_degrees[i1] != m_degrees[i2])
                    return m_degrees[i1] < m_degrees[i2];
                if (m_lit_num[i1] != m_lit_num[i2])
                    return m_lit_num[i1] < m_lit_num[i2];
                return i1 < i2;
            }
        };

        unsigned_vector m_dl_degrees;
        unsigned_vector m_dl_lit_num;
        unsigned_vector m_dl_p;
        void sort_clauses_by_degree_lit_num(unsigned sz, clause ** cs) {
            if (sz <= 1)
                return;
            TRACE(nlsat_reorder_clauses, tout << "before:\n"; for (unsigned i = 0; i < sz; i++) { display(tout, *(cs[i])); tout << "\n"; });
            m_dl_degrees.reset();
            m_dl_lit_num.reset();
            m_dl_p.reset();
            for (unsigned i = 0; i < sz; i++) {
                m_dl_degrees.push_back(degree(*(cs[i])));
                m_dl_lit_num.push_back(cs[i]->size());
                m_dl_p.push_back(i);
            }
            std::sort(m_dl_p.begin(), m_dl_p.end(), degree_lit_num_lt(m_dl_degrees, m_dl_lit_num));
            TRACE(nlsat_reorder_clauses, tout << "permutation: "; ::display(tout, m_dl_p.begin(), m_dl_p.end()); tout << "\n";);
            apply_permutation(sz, cs, m_dl_p.data());
            TRACE(nlsat_reorder_clauses, tout << "after:\n"; for (unsigned i = 0; i < sz; i++) { display(tout, *(cs[i])); tout << "\n"; });
        }

        void sort_watched_clauses() {
            unsigned num = num_vars();
            for (unsigned i = 0; i < num; i++) {
                clause_vector & ws = m_watches[i];
                sort_clauses_by_degree(ws.size(), ws.data());
            }
        }

        // -----------------------
        //
        // Full dimensional 
        // 
        // A problem is in the full dimensional fragment if it does
        // not contain equalities or non-strict inequalities.
        //
        // -----------------------
        
        bool is_full_dimensional(literal l) const {
            atom * a = m_atoms[l.var()];
            if (a == nullptr)
                return true;
            switch (a->get_kind()) {
            case atom::EQ:      return l.sign();
            case atom::LT:      return !l.sign();
            case atom::GT:      return !l.sign();
            case atom::ROOT_EQ: return l.sign();
            case atom::ROOT_LT: return !l.sign();
            case atom::ROOT_GT: return !l.sign();
            case atom::ROOT_LE: return l.sign();
            case atom::ROOT_GE: return l.sign();
            default:
                UNREACHABLE();
                return false;
            }
        }

        bool is_full_dimensional(clause const & c) const {
            for (literal l : c) {
                if (!is_full_dimensional(l))
                    return false;
            }
            return true;
        }

        bool is_full_dimensional(clause_vector const & cs) const {
            for (clause* c : cs) {
                if (!is_full_dimensional(*c)) 
                    return false;
            }
            return true;
        }

        bool is_full_dimensional() const {
            return is_full_dimensional(m_clauses);
        }


        // -----------------------
        //
        // Simplification
        //
        // -----------------------

        // solve simple equalities
        // TBD WU-Reit decomposition?

        // - elim_unconstrained
        // - solve_eqs
        // - fm

        /**
           \brief isolate variables in unit equalities.
           Assume a clause is c == v*p + q
           and the context implies p > 0
           
           replace v by -q/p
           remove clause c, 
           The for other occurrences of v, 
           replace v*r + v*v*r' > 0 by 
           by p*p*v*r + p*p*v*v*r' > 0
           by p*q*r + q*q*r' > 0        

           The method ignores lemmas and assumes constraints don't use roots.
        */



        // Eliminated variables are tracked in m_bounds.
        // Each element in m_bounds tracks the eliminated variable and an upper or lower bound
        // that has to be satisfied. Variables that are eliminated through equalities are tracked
        // by non-strict bounds. A satisfiable solution is required to provide an evaluation that
        // is consistent with the bounds. For equalities, the non-strict lower or upper bound can 
        // always be assigned as a value to the variable.

        void fix_patch() {
            m_lo.reset(); m_hi.reset();
            for (auto& b : m_bounds)
                m_assignment.reset(b.x);
            for (unsigned i = m_bounds.size(); i-- > 0; ) 
                fix_patch(m_bounds[i]);            
        }

        // x is unassigned, lo < x -> x <- lo + 1
        // x is unassigned, x < hi -> x <- hi - 1
        // x is unassigned, lo <= x -> x <- lo
        // x is unassigned, x <= hi -> x <- hi
        // x is assigned above hi, lo is strict lo < x < hi -> set x <- (lo + hi)/2
        // x is assigned below hi, above lo -> no-op
        // x is assigned below lo, hi is strict lo < x < hi -> set x <-> (lo + hi)/2
        // x is assigned above hi, x <= hi -> x <- hi
        // x is assigned blow lo, lo <= x -> x <- lo
        void fix_patch(bound_constraint& b) {
            var x = b.x;
            scoped_anum Av(m_am), Bv(m_am), val(m_am);
            m_pm.eval(b.A, m_assignment, Av);
            m_pm.eval(b.B, m_assignment, Bv);
            m_am.neg(Bv);
            val = Bv / Av;
            // Ax >= B
            // is-lower : A > 0
            // is-upper:  A < 0
            // x <- B / A
            bool is_lower = m_am.is_pos(Av);
            TRACE(nlsat,
                  m_display_var(tout << "patch v" << x << " ", x) << "\n";
                  if (m_assignment.is_assigned(x)) m_am.display(tout << "previous value: ", m_assignment.value(x)); tout << "\n";
                  m_am.display(tout << "updated value: ", val); tout << "\n";
                );

            if (!m_assignment.is_assigned(x)) {
                if (!b.is_strict)
                    m_assignment.set_core(x, val);
                else if (is_lower)
                    m_assignment.set_core(x, val + 1);
                else
                    m_assignment.set_core(x, val - 1);
            }
            else {
                auto& aval = m_assignment.value(x);
                if (is_lower) {
                    // lo < value(x), lo < x -> x is unchanged
                    if (b.is_strict && m_am.lt(val, aval))
                        ;
                    else if (!b.is_strict && m_am.le(val, aval))
                        ;
                    else if (!b.is_strict)
                        m_assignment.set_core(x, val);
                    // aval < lo < x, hi is unassigned: x <- lo + 1
                    else if (!m_hi.is_assigned(x))
                        m_assignment.set_core(x, val + 1);
                    // aval < lo < x, hi is assigned: x <- (lo + hi) / 2
                    else {
                        scoped_anum mid(m_am);
                        m_am.add(m_hi.value(x), val, mid);
                        mid = mid / 2;
                        m_assignment.set_core(x, mid);
                    }
                }
                else {
                    // dual to lower bounds
                    if (b.is_strict && m_am.lt(aval, val))
                        ;
                    else if (!b.is_strict && m_am.le(aval, val))
                        ;
                    else if (!b.is_strict)
                        m_assignment.set_core(x, val);
                    else if (!m_lo.is_assigned(x))
                        m_assignment.set_core(x, val - 1);
                    else {
                        scoped_anum mid(m_am);
                        m_am.add(m_lo.value(x), val, mid);
                        mid = mid / 2;
                        m_assignment.set_core(x, mid);
                    }
                }
            }

            if (is_lower) {
                if (!m_lo.is_assigned(x) || m_am.lt(m_lo.value(x), val))
                    m_lo.set_core(x, val);
            }
            else {
                if (!m_hi.is_assigned(x) || m_am.gt(m_hi.value(x), val))
                    m_hi.set_core(x, val);
            }        
        }
       
        bool is_unit_ineq(clause const& c) const {
            return 
                c.size() == 1 &&
                m_atoms[c[0].var()] && 
                m_atoms[c[0].var()]->is_ineq_atom();
        }

        bool is_unit_eq(clause const& c) const {
            return 
                is_unit_ineq(c) && 
                !c[0].sign() && 
                m_atoms[c[0].var()]->is_eq();
        }

        bool is_single_poly(ineq_atom const& a, poly*& p) {
            unsigned sz = a.size();
            return sz == 1 && a.is_odd(0) && (p = a.p(0), true);
        } 

        bool is_unit(polynomial_ref const& p) {
            if (!m_pm.is_const(p))
                return false;
            auto const& c = m_pm.coeff(p, 0);
            return m_pm.m().is_one(c) || m_pm.m().is_minus_one(c);
        }

        // -----------------------
        //
        // Pretty printing
        //
        // -----------------------
        
        std::ostream& display_num_assignment(std::ostream & out, display_var_proc const & proc) const {
            for (var x = 0; x < num_vars(); x++) {
                if (m_assignment.is_assigned(x)) {
                    proc(out, x);
                    out << " -> ";
                    m_am.display_decimal(out, m_assignment.value(x));
                    out << "\n";
                }
            }
            return out;
        }

        std::ostream& display_bool_assignment(std::ostream & out, bool eval_atoms = false) const {
            unsigned sz = usize(m_atoms);
            if (!eval_atoms) {
                for (bool_var b = 0; b < sz; b++) {
                    if (m_bvalues[b] == l_undef)
                        continue;
                    if (m_atoms[b] == nullptr) 
                        out << "b" << b << " -> " << (m_bvalues[b] == l_true ? "true" : "false") << " @" << m_levels[b] << "pure \n";
                    else  {
                        display(out << "b" << b << " ", *m_atoms[b]) << " -> " << (m_bvalues[b] == l_true ? "true" : "false") << " @" << m_levels[b] << "\n";
                    }                                                                                     
                    
                }
            }
            else { //if (eval_atoms) {
                for (bool_var b = 0; b < sz; b++) {
                    if (m_atoms[b] == nullptr) continue;
                    lbool val = to_lbool(m_evaluator.eval(m_atoms[b], false));
                    out << "b" << b << " -> " << val << " ";
                    if (m_atoms[b]) {
                        out << "\"";
                        display(out, *m_atoms[b]);
                        out << "\"";
                    }
                    out << "\n";
                }
            }

            return out;
        }

        bool display_mathematica_assignment(std::ostream & out) const {
            bool first = true;
            for (var x = 0; x < num_vars(); x++) {
                if (m_assignment.is_assigned(x)) {
                    if (first)
                        first = false;
                    else
                        out << " && ";
                    out << "x" << x << " == ";
                    m_am.display_mathematica(out, m_assignment.value(x));
                }
            }
            return !first;
        }

        std::ostream& display_num_assignment(std::ostream & out) const { 
            return display_num_assignment(out, m_display_var);
        }

        std::ostream& display_assignment(std::ostream& out, bool eval_atoms = false) const {
            display_bool_assignment(out, eval_atoms);
            display_num_assignment(out);
            return out;
        }

        std::ostream& display_assignment_for_clause(std::ostream& out, const clause& c) const {
            // Print literal assignments
            out << "Literals:\n";
            for (unsigned i = 0; i < c.size(); ++i) {
                literal l = c[i];
                out << "  ";
                display(out, l);
                out << " := ";
                lbool val = assigned_value(l);
                if (val == l_true) out << "true";
                else if (val == l_false) out << "false";
                else out << "undef";
                out << "\n";
            }

            // Collect all variables used in the clause
            bool_vector printed_vars(num_vars(), false);
            var_vector vars;
            out << "Variables:\n";
            for (unsigned i = 0; i < c.size(); ++i) {
                vars.reset();
                const_cast<imp*>(this)->vars(c[i], vars);
                for (unsigned j = 0; j < vars.size(); ++j) {
                    var x = vars[j];
                    if (x >= printed_vars.size() || printed_vars[x])
                        continue;
                    printed_vars.setx(x, true, false);
                    out << "  ";
                    m_display_var(out, x);
                    out << " = ";
                    if (m_assignment.is_assigned(x)) {
                        m_am.display_decimal(out, m_assignment.value(x));
                    } else {
                        out << "undef";
                    }
                    out << "\n";
                }
            } return out;
        }


        std::ostream& display(std::ostream& out, justification j) const {
            switch (j.get_kind()) {
            case justification::CLAUSE:
                display(out, *j.get_clause()) << "\n";
                break;
            case justification::LAZY: {
                lazy_justification const& lz = *j.get_lazy();
                display_not(out, lz.num_lits(), lz.lits()) << "\n";
                for (unsigned i = 0; i < lz.num_clauses(); ++i) {
                    display(out, lz.clause(i)) << "\n";
                }
                break;
            }
            default:
                out << j.get_kind() << "\n";
                break;                
            }
            return out;
        }

        bool m_display_eval = false;
        std::ostream& display_eval(std::ostream& out, justification j) {
            flet<bool> _display(m_display_eval, true);
            return display(out, j);
        }
       
        std::ostream& display_ineq(std::ostream & out, ineq_atom const & a, display_var_proc const & proc, bool use_star = false) const {
            unsigned sz = a.size();
            for (unsigned i = 0; i < sz; i++) {
                if (use_star && i > 0)
                    out << "*";
                bool is_even = a.is_even(i);
                if (is_even || sz > 1)
                    out << "(";
                display_polynomial(out, a.p(i), proc, use_star);
                if (is_even || sz > 1)
                    out << ")";
                if (is_even)
                    out << "^2";
            }
            switch (a.get_kind()) {
            case atom::LT: out << " < 0"; break;
            case atom::GT: out << " > 0"; break;
            case atom::EQ: out << " = 0"; break;
            default: UNREACHABLE(); break;
            }
            return out;
        }
        
        std::ostream& display_mathematica(std::ostream & out, ineq_atom const & a) const {
            unsigned sz = a.size();
            for (unsigned i = 0; i < sz; i++) {
                if (i > 0)
                    out << "*";
                bool is_even = a.is_even(i);
                if (sz > 1)
                    out << "(";
                if (is_even)
                    out << "(";
                m_pm.display(out, a.p(i), display_var_proc(), true);
                if (is_even)
                    out << "^2)";
                if (sz > 1)
                    out << ")";
            }
            switch (a.get_kind()) {
            case atom::LT: out << " < 0"; break;
            case atom::GT: out << " > 0"; break;
            case atom::EQ: out << " == 0"; break;
            default: UNREACHABLE(); break;
            }
            return out;
        }

        std::ostream& display_polynomial_smt2(std::ostream & out, poly const* p, display_var_proc const & proc) const {
            return m_pm.display_smt2(out, p, proc);
        }

        std::ostream& display_ineq_smt2(std::ostream & out, ineq_atom const & a, display_var_proc const & proc) const {
            switch (a.get_kind()) {
            case atom::LT: out << "(< "; break;
            case atom::GT: out << "(> "; break;
            case atom::EQ: out << "(= "; break;
            default: UNREACHABLE(); break;
            }
            unsigned sz = a.size();
            if (sz > 1)
                out << "(* ";
            for (unsigned i = 0; i < sz; i++) {
                if (i > 0) out << " ";
                if (a.is_even(i)) {
                    out << "(* ";
                    display_polynomial_smt2(out, a.p(i), proc);
                    out << " ";
                    display_polynomial_smt2(out, a.p(i), proc);
                    out << ")";
                }
                else {
                    display_polynomial_smt2(out, a.p(i), proc);
                }
            }
            if (sz > 1)
                out << ")";
            out << " 0)";
            return out;
        }

        std::ostream& display_poly_root(std::ostream& out, char const* y, root_atom const& a, display_var_proc const& proc) const {
            out << "(exists (("; proc(out,a.x()); out << " Real))\n";
            out << "(and (= " << y << " ";
            proc(out, a.x());
            out << ") (= 0 ";
            display_polynomial_smt2(out, a.p(), proc);
            out << ")))\n";
            return out;
        }

        std::ostream& display_binary_smt2(std::ostream& out,  poly const* p1, char const* rel, poly const* p2, display_var_proc const& proc) const {
            out << "(" << rel << " ";
            display_polynomial_smt2(out, p1, proc);
            out << " ";
            display_polynomial_smt2(out, p2, proc);
            out << ")";
            return out;
        }
        
        
        std::ostream& display_linear_root_smt2(std::ostream & out, root_atom const & a, display_var_proc const & proc) const {
            polynomial_ref A(m_pm), B(m_pm), Z(m_pm), Ax(m_pm);
            polynomial::scoped_numeral zero(m_qm);
            m_pm.m().set(zero, 0);
            A = m_pm.derivative(a.p(), a.x());
            B = m_pm.neg(m_pm.substitute(a.p(), a.x(), zero));
            Z = m_pm.mk_zero();

            Ax = m_pm.mul(m_pm.mk_polynomial(a.x()), A);

            // x < root[1](ax + b) == (a > 0 => ax + b < 0) & (a < 0 => ax + b > 0)
            // x < root[1](ax + b) == (a > 0 => ax < -b) & (a < 0 => ax > -b)

            char const* rel1 = "<", *rel2 = ">";
            switch (a.get_kind()) {
            case atom::ROOT_LT: rel1 = "<"; rel2 = ">"; break;
            case atom::ROOT_GT: rel1 = ">"; rel2 = "<"; break;
            case atom::ROOT_LE: rel1 = "<="; rel2 = ">="; break;
            case atom::ROOT_GE: rel1 = ">="; rel2 = "<="; break;
            case atom::ROOT_EQ: rel1 = rel2 = "="; break;
            default: UNREACHABLE(); break;
            }
            
            out << "(and ";
            out << "(=> ";  display_binary_smt2(out, A, ">", Z, proc); display_binary_smt2(out, Ax, rel1, B, proc); out << ") ";
            out << "(=> ";  display_binary_smt2(out, A, "<", Z, proc); display_binary_smt2(out, Ax, rel2, B, proc); out << ") ";
            out << ")";
            
            return out;
        }


        std::ostream& display_root_smt2(std::ostream& out, root_atom const& a, display_var_proc const& proc) const {
            if (a.i() == 1 && m_pm.degree(a.p(), a.x()) == 1)
                return display_linear_root_smt2(out, a, proc); 
#if 1
            out << "(exists (";
            for (unsigned j = 0; j < a.i(); ++j) {
                std::string y = std::string("y") + std::to_string(j);
                out << "(" << y << " Real) ";
            }
            out << ")\n";
            out << "(and\n";
            for (unsigned j = 0; j < a.i(); ++j) {
                std::string y = std::string("y") + std::to_string(j);
                display_poly_root(out, y.c_str(), a, proc);
            }
            for (unsigned j = 0; j + 1 < a.i(); ++j) {
                std::string y1 = std::string("y") + std::to_string(j);
                std::string y2 = std::string("y") + std::to_string(j+1);
                out << "(< " << y1 << " " << y2 << ")\n";
            }

            std::string yn = "y" + std::to_string(a.i() - 1);

            // TODO we need (forall z : z < yn . p(z) => z = y1 or ... z = y_{n-1})
            // to say y1, .., yn are the first n distinct roots.
            //
            out << "(forall ((z Real)) (=> (and (< z " << yn << ") "; display_poly_root(out, "z", a, proc) << ") ";
            if (a.i() == 1) {
                out << "false))\n";
            }
            else {
                out << "(or ";
                for (unsigned j = 0; j + 1 < a.i(); ++j) {
                    std::string y1 = std::string("y") + std::to_string(j);
                    out << "(= z " << y1 << ") ";
                }
                out << ")))\n";
            }
            switch (a.get_kind()) {
            case atom::ROOT_LT: out << "(< "; proc(out, a.x()); out << " " << yn << ")"; break;
            case atom::ROOT_GT: out << "(> "; proc(out, a.x()); out << " " << yn << ")"; break;
            case atom::ROOT_LE: out << "(<= "; proc(out, a.x()); out << " " << yn << ")"; break;
            case atom::ROOT_GE: out << "(>= "; proc(out, a.x()); out << " " << yn << ")"; break;
            case atom::ROOT_EQ: out << "(= "; proc(out, a.x()); out << " " << yn << ")"; break;
            default: UNREACHABLE(); break;
            }
            out << "))";
            return out;
#endif


            return display_root(out, a, proc);
        }

        std::ostream& display_root(std::ostream & out, root_atom const & a, display_var_proc const & proc) const {
            proc(out, a.x());
            switch (a.get_kind()) {
            case atom::ROOT_LT: out << " < "; break;
            case atom::ROOT_GT: out << " > "; break;
            case atom::ROOT_LE: out << " <= "; break;
            case atom::ROOT_GE: out << " >= "; break;
            case atom::ROOT_EQ: out << " = "; break;
            default: UNREACHABLE(); break;
            }
            out << "root[" << a.i() << "](";
            display_polynomial(out, a.p(), proc);
            out << ")";
            return out;
        }

        struct mathematica_var_proc : public display_var_proc {
            var m_x;
        public:
            mathematica_var_proc(var x):m_x(x) {}
            std::ostream& operator()(std::ostream & out, var x) const override {
                if (m_x == x)
                    return out << "#1";
                else
                    return out << "x" << x; 
            }
        };

        std::ostream& display_mathematica(std::ostream & out, root_atom const & a) const {
            out << "x" << a.x();
            switch (a.get_kind()) {
            case atom::ROOT_LT: out << " < "; break;
            case atom::ROOT_GT: out << " > "; break;
            case atom::ROOT_LE: out << " <= "; break;
            case atom::ROOT_GE: out << " >= "; break;
            case atom::ROOT_EQ: out << " == "; break;
            default: UNREACHABLE(); break;
            }
            out << "Root[";
            display_polynomial(out, a.p(), mathematica_var_proc(a.x()), true);
            out << " &, " << a.i() << "]";
            return out;
        }
        
        std::ostream& display(std::ostream & out, atom const & a, display_var_proc const & proc) const {
            if (a.is_ineq_atom())
                return display_ineq(out, static_cast<ineq_atom const &>(a), proc);
            else
                return display_root(out, static_cast<root_atom const &>(a), proc);
        }

        std::ostream& display(std::ostream & out, atom const & a) const {
            return display(out, a, m_display_var);
        }

        std::ostream& display_mathematica(std::ostream & out, atom const & a) const {
            if (a.is_ineq_atom())
                return display_mathematica(out, static_cast<ineq_atom const &>(a));
            else
                return display_mathematica(out, static_cast<root_atom const &>(a));
        }

        std::ostream& display_smt2(std::ostream & out, atom const & a, display_var_proc const & proc) const {
            if (a.is_ineq_atom())
                return display_ineq_smt2(out, static_cast<ineq_atom const &>(a), proc);
            else
                return display_root_smt2(out, static_cast<root_atom const &>(a), proc);
        }

        std::ostream& display_atom(std::ostream & out, bool_var b, display_var_proc const & proc) const {
            if (b == 0)
                out << "true";
            else if (m_atoms[b] == 0)
                out << "b" << b;
            else
                display(out, *(m_atoms[b]), proc);
            return out;
        }

        std::ostream& display_atom(std::ostream & out, bool_var b) const {
            return display_atom(out, b, m_display_var);
        }

        std::ostream& display_mathematica_atom(std::ostream & out, bool_var b) const {
            if (b == 0)
                out << "(0 < 1)";
            else if (m_atoms[b] == 0)
                out << "b" << b;
            else
                display_mathematica(out, *(m_atoms[b]));
            return out;
        }

        std::ostream& display_smt2_atom(std::ostream & out, bool_var b, display_var_proc const & proc) const {
            if (b == 0)
                out << "true";
            else if (m_atoms[b] == 0)
                out << "b" << b;
            else
                display_smt2(out, *(m_atoms[b]), proc);
            return out;
        }

        std::ostream& display(std::ostream & out, literal l, display_var_proc const & proc) const {
            if (l.sign()) {
                bool_var b = l.var();
                out << "!";
                if (m_atoms[b] != 0)
                    out << "(";
                display_atom(out, b, proc);
                if (m_atoms[b] != 0)
                    out << ")";
            }
            else {
                display_atom(out, l.var(), proc);
            }
            return out;
        }

        std::ostream& display(std::ostream & out, literal l) const {
            return display(out, l, m_display_var);
        }

        std::ostream& display_smt2(std::ostream & out, literal l) const {
            return display_smt2(out, l, m_display_var);
        }

        std::ostream& display_mathematica(std::ostream & out, literal l) const {
            if (l.sign()) {
                bool_var b = l.var();
                out << "!";
                if (m_atoms[b] != 0)
                    out << "(";
                display_mathematica_atom(out, b);
                if (m_atoms[b] != 0)
                    out << ")";
            }
            else {
                display_mathematica_atom(out, l.var());
            }
            return out;
        }

        std::ostream& display_smt2(std::ostream & out, literal l, display_var_proc const & proc) const {
            if (l.sign()) {
                bool_var b = l.var();
                out << "(not ";
                display_smt2_atom(out, b, proc);
                out << ")";
            }
            else {
                display_smt2_atom(out, l.var(), proc);
            }
            return out;
        }
            
        std::ostream& display_assumptions(std::ostream & out, _assumption_set s) const {
            if (!m_display_assumption)
                return out;
            vector<assumption, false> deps;
            m_asm.linearize(s, deps);
            bool first = true;
            for (auto dep : deps) {
                if (first) first = false; else out << " ";
                (*m_display_assumption)(out, dep); 
            }
            return out;
        }
        
        std::ostream& display(std::ostream & out, unsigned num, literal const * ls, display_var_proc const & proc) const {
            for (unsigned i = 0; i < num; i++) {
                if (i > 0)
                    out << " or ";
                display(out, ls[i], proc);
            }
            return out;
        }

        std::ostream& display(std::ostream & out, unsigned num, literal const * ls) const {
            return display(out, num, ls, m_display_var);
        }

        std::ostream& display_not(std::ostream & out, unsigned num, literal const * ls, display_var_proc const & proc) const {
            for (unsigned i = 0; i < num; i++) {
                if (i > 0)
                    out << " or ";
                display(out, ~ls[i], proc);
            }
            return out;
        }

        std::ostream& display_not(std::ostream & out, unsigned num, literal const * ls) const {
            return display_not(out, num, ls, m_display_var);
        }
        
        std::ostream& display(std::ostream & out, scoped_literal_vector const & cs) {
            return display(out, cs.size(), cs.data(), m_display_var);
        }

        std::ostream& display(std::ostream & out, clause const & c, display_var_proc const & proc) const {
            if (c.assumptions() != nullptr) {
                display_assumptions(out, static_cast<_assumption_set>(c.assumptions()));
                out << " |- ";
            }
            return display(out, c.size(), c.data(), proc);
        }

        std::ostream& display(std::ostream & out, clause const & c) const {
            return display(out, c, m_display_var);
        }


        std::ostream& display_polynomial(std::ostream& out, poly* p, display_var_proc const & proc, bool use_star = false) const {
            if (m_display_eval) {
                polynomial_ref q(m_pm);
                q = p;
                for (var x = 0; x < num_vars(); x++) 
                    if (m_assignment.is_assigned(x)) {
                        auto& a = m_assignment.value(x);
                        if (!m_am.is_rational(a))
                            continue;
                        mpq r;
                        m_am.to_rational(a, r);
                        q = m_pm.substitute(q, 1, &x, &r);            
                    }
                m_pm.display(out, q, proc, use_star);
            }
            else 
                m_pm.display(out, p, proc, use_star);
            return out;
        }

        // --

        std::ostream& display_smt2(std::ostream & out, unsigned n, literal const* ls) const {
            return display_smt2(out, n, ls, display_var_proc());
        }


        std::ostream& display_smt2(std::ostream & out, unsigned num, literal const * ls, display_var_proc const & proc) const {
            if (num == 0) {
                out << "false";
            }
            else if (num == 1) {
                display_smt2(out, ls[0], proc);
            }
            else {
                out << "(or";
                for (unsigned i = 0; i < num; i++) {
                    out << " ";
                    display_smt2(out, ls[i], proc);
                }
                out << ")";
            }
            return out;
        }

        std::ostream& display_smt2(std::ostream & out, clause const & c, display_var_proc const & proc = display_var_proc()) const {
            return display_smt2(out, c.size(), c.data(), proc);
        }

        std::ostream& display_abst(std::ostream & out, literal l) const {
            if (l.sign()) {
                bool_var b = l.var();
                out << "!";
                if (b == true_bool_var)
                    out << "true";
                else
                    out << "b" << b;
            }
            else {
                out << "b" << l.var();
            }
            return out;
        }

        std::ostream& display_abst(std::ostream & out, unsigned num, literal const * ls) const {
            for (unsigned i = 0; i < num; i++) {
                if (i > 0)
                    out << " or ";
                display_abst(out, ls[i]);
            }
            return out;
        }

        std::ostream& display_abst(std::ostream & out, scoped_literal_vector const & cs) const {
            return display_abst(out, cs.size(), cs.data());
        }

        std::ostream& display_abst(std::ostream & out, clause const & c) const {
            return display_abst(out, c.size(), c.data());
        }

        std::ostream& display_mathematica(std::ostream & out, clause const & c) const {
            out << "(";
            unsigned sz = c.size();
            for (unsigned i = 0; i < sz; i++) {
                if (i > 0)
                    out << " || ";
                display_mathematica(out, c[i]);
            }
            out << ")";
            return out;
        }

        // Debugging support:
        // Display generated lemma in Mathematica format.
        // Mathematica must reduce lemma to True (modulo resource constraints).
        std::ostream& display_mathematica_lemma(std::ostream & out, unsigned num, literal const * ls, bool include_assignment = false) const {
            bool_vector used_vars(num_vars(), false);
            var_vector vars;
            for (unsigned i = 0; i < num; i++) {
                vars.reset();
                this->vars(ls[i], vars);
                for (var v : vars)
                    used_vars[v] = true;
            }

            if (include_assignment) {
                for (var x = 0; x < num_vars(); x++) {
                    if (m_assignment.is_assigned(x))
                        used_vars[x] = true;
                }
            }

            out << "Resolve[ForAll[{";
            bool first = true;
            for (var x = 0; x < num_vars(); x++) {                
                if (used_vars[x] == false) continue;
                if (!first) out << ", ";
                first = false;
                out << "x" << x;
            }
            out << "}, ";

            if (include_assignment) {
                out << "!(";
                if (!display_mathematica_assignment(out))
                    out << "0 < 1"; // nothing was printed
                out << ") || ";
            }

            for (unsigned i = 0; i < num; i++) {
                if (i > 0)
                    out << " || ";
                display_mathematica(out, ls[i]);
            }
            out << "], Reals]";
            return out;
        }
        
        std::ostream& display(std::ostream & out, clause_vector const & cs, display_var_proc const & proc) const {
            for (clause* c : cs) {
                display(out, *c, proc) << "\n";
            }
            return out; 
        }

        std::ostream& display(std::ostream & out, clause_vector const & cs) const {
            return display(out, cs, m_display_var);
        }

        std::ostream& display_mathematica(std::ostream & out, clause_vector const & cs) const {            
            unsigned sz = cs.size();
            for (unsigned i = 0; i < sz; i++) {
                if (i > 0) out << ",\n";
                display_mathematica(out << " ", *(cs[i]));
            }
            return out;
        }

        std::ostream& display_abst(std::ostream & out, clause_vector const & cs) const {
            for (clause* c : cs) {
                display_abst(out, *c) << "\n";
            }
            return out;
        }

        std::ostream& display(std::ostream & out, display_var_proc const & proc) const {
            display(out, m_clauses, proc);
            if (!m_learned.empty()) {
                display(out << "Lemmas:\n", m_learned, proc);
            }
            return out;
        }

        std::ostream& display_mathematica(std::ostream & out) const {
            return display_mathematica(out << "{\n", m_clauses) << "}\n";
        }

        std::ostream& display_abst(std::ostream & out) const {
            display_abst(out, m_clauses);
            if (!m_learned.empty()) {
                display_abst(out << "Lemmas:\n", m_learned);
            }
            return out;
        }

        std::ostream& display(std::ostream & out) const {
            display(out, m_display_var);
            display_assignment(out << "assignment:\n");
            return out << "---\n";
        }

        std::ostream& display_vars(std::ostream & out) const {
            for (unsigned i = 0; i < num_vars(); i++) {
                out << i << " -> "; m_display_var(out, i); out << "\n";
            }
            return out;
        }

        std::ostream& display_var(std::ostream& out, unsigned j) const {
            return m_display_var(out, j);
        }
        
        std::ostream& display_smt2_arith_decls(std::ostream & out) const {
            unsigned sz = m_is_int.size();
            for (unsigned i = 0; i < sz; i++) {
                if (is_int(i)) {
                    out << "(declare-fun "; m_display_var(out, i) << " () Int)\n";
                }
                else {
                    out << "(declare-fun "; m_display_var(out, i) << " () Real)\n";
                }
            }
            return out;
        }

        std::ostream& display_smt2_bool_decls(std::ostream & out) const {
            unsigned sz = usize(m_atoms);
            for (unsigned i = 0; i < sz; i++) {
                if (m_atoms[i] == nullptr)
                    out << "(declare-fun b" << i << " () Bool)\n";
            }
            return out;
        }

        std::ostream& display_smt2(std::ostream & out) const {
            display_smt2_bool_decls(out);
            display_smt2_arith_decls(out);
            out << "(assert (and true\n";
            for (clause* c : m_clauses) {
                display_smt2(out, *c, m_display_var) << "\n";
            }
            out << "))\n" << std::endl;
            return out;
        }

        std::string debug_get_var_name(unsigned v) const {
            std::stringstream ss;
            if (v >= m_perm.size()) {
                ss << "x" << v << "\n";
            } else if (m_display_var.m_proc) {
                // Use the display procedure to get the variable name
                (*m_display_var.m_proc)(ss, m_perm[v]);
            } else {
                // Fallback if no display_var procedure
                ss << "x" << m_perm[v];
            }
            return ss.str();
        }
        std::string debug_atom_string(unsigned v) const {
            std::stringstream ss;
            display_atom(ss, v);
            return ss.str();
        }

        std::vector<std::pair<std::string, anum>> debug_parse_var_anum_file() {
            std::vector<std::pair<std::string, anum>> result;
            std::ifstream in(m_debug_known_solution_file_name);
            std::string line;
            while (std::getline(in, line)) {
                std::istringstream iss(line);
                std::string name, value_str;
                if (!(iss >> name >> value_str)) {
                    std::cout << line << std::endl;
                    std::cout << "is not recognized\n";
                    exit(1); // skip malformed lines
                }
                // Parse rational value
                rational r;
                size_t slash = value_str.find('/');
                if (slash == std::string::npos) {
                    r = rational(value_str.c_str());
                } else {
                    std::string num = value_str.substr(0, slash);
                    std::string den = value_str.substr(slash + 1);
                     r = rational(num.c_str()) / rational(den.c_str());
                }
                anum a;
                const auto& q =  r.to_mpq();
                m_am.set(a, q);
                result.emplace_back(name, a);
            }

            return result;
        }
    };
    
    solver::solver(reslimit& rlim, params_ref const & p, bool incremental) {
        m_ctx = alloc(ctx, rlim, p, incremental);
        m_imp = alloc(imp, *this, *m_ctx);
    }

    solver::solver(ctx& ctx) {
        m_ctx = nullptr;
        m_imp = alloc(imp, *this, ctx);
    }
        
    solver::~solver() {
        dealloc(m_imp);
        dealloc(m_ctx);
    }

    lbool solver::check() {
        return m_imp->check();
    }

    lbool solver::check(literal_vector& assumptions) {
        return m_imp->check(assumptions);
    }

    void solver::get_core(vector<assumption, false>& assumptions) {
        return m_imp->get_core(assumptions);
    }

    void solver::reset() {
        m_imp->reset();
    }


    void solver::updt_params(params_ref const & p) {
        m_imp->updt_params(p);
    }


    void solver::collect_param_descrs(param_descrs & d) {
        algebraic_numbers::manager::collect_param_descrs(d);
        nlsat_params::collect_param_descrs(d);
    }

    unsynch_mpq_manager & solver::qm() {
        return m_imp->m_qm;
    }
        
    anum_manager & solver::am() {
        return m_imp->m_am;
    }

    pmanager & solver::pm() {
        return m_imp->m_pm;
    }

    

    void solver::set_display_var(display_var_proc const & proc) {
        m_imp->m_display_var.m_proc = &proc;
    }

    void solver::set_display_assumption(display_assumption_proc const& proc) {
        m_imp->m_display_assumption = &proc;
    }


    unsigned solver::num_vars() const {
        return m_imp->num_vars();
    }

    bool solver::is_int(var x) const {
        return m_imp->is_int(x);
    }

    bool_var solver::mk_bool_var() {
        return m_imp->mk_bool_var();
    }
    
    literal solver::mk_true() {
        return literal(0, false);
    }

    atom * solver::bool_var2atom(bool_var b) {
        return m_imp->m_atoms[b];
    }

    void solver::vars(literal l, var_vector& vs) {
        m_imp->vars(l, vs);
    }

    atom_vector const& solver::get_atoms() {
        return m_imp->m_atoms;
    }

    atom_vector const& solver::get_var2eq() {
        return m_imp->m_var2eq;
    }

    evaluator& solver::get_evaluator() {
        return m_imp->m_evaluator;
    }

    explain& solver::get_explain() {
        return m_imp->m_explain;
    }

    void solver::reorder(unsigned sz, var const* p) {
        m_imp->reorder(sz, p);
    }

    void solver::restore_order() {
        m_imp->restore_order();
    }

    void solver::set_rvalues(assignment const& as) {
        m_imp->m_assignment.copy(as);
    }

    void solver::get_rvalues(assignment& as) {
        as.copy(m_imp->m_assignment);
    }

    void solver::get_bvalues(svector<bool_var> const& bvars, svector<lbool>& vs) {
        vs.reset();
        for (bool_var b : bvars) {
            vs.reserve(b + 1, l_undef);
            if (!m_imp->m_atoms[b]) {
                vs[b] = m_imp->m_bvalues[b];
            }
        }
        TRACE(nlsat, display(tout););
    }

    void solver::set_bvalues(svector<lbool> const& vs) {
        TRACE(nlsat, display(tout););
        for (bool_var b = 0; b < vs.size(); ++b) {
            if (vs[b] != l_undef) {
                TRACE(nlsat_assign, tout << "setting bool values " << b << "\n";);
                m_imp->m_bvalues[b] = vs[b];
                SASSERT(!m_imp->m_atoms[b]);
            }
        }
#if 0        
        m_imp->m_bvalues.reset();
        m_imp->m_bvalues.append(vs);
        m_imp->m_bvalues.resize(m_imp->m_atoms.size(), l_undef);        
        for (unsigned i = 0; i < m_imp->m_atoms.size(); ++i) {
            atom* a = m_imp->m_atoms[i];
            SASSERT(!a);
            if (a) {
                m_imp->m_bvalues[i] = to_lbool(m_imp->m_evaluator.eval(a, false));
            }
        }
#endif
        TRACE(nlsat, display(tout););
    }

    void solver::del_clause(clause* c) {
        m_imp->del_clause(c);
    }
    
    var solver::mk_var(bool is_int) {
        return m_imp->mk_var(is_int);
    }
        
    bool_var solver::mk_ineq_atom(atom::kind k, unsigned sz, poly * const * ps, bool const * is_even) {
        return m_imp->mk_ineq_atom(k, sz, ps, is_even);
    }

    literal solver::mk_ineq_literal(atom::kind k, unsigned sz, poly * const * ps, bool const * is_even, bool simplify) {
        return m_imp->mk_ineq_literal(k, sz, ps, is_even, simplify);
    }

    bool_var solver::mk_root_atom(atom::kind k, var x, unsigned i, poly * p) {
        return m_imp->mk_root_atom(k, x, i, p);
    }
    
    void solver::inc_ref(bool_var b) {
        m_imp->inc_ref(b);
    }

    void solver::dec_ref(bool_var b) {
        m_imp->dec_ref(b);
    }

    void solver::inc_ref(assumption a) {
        m_imp->inc_ref(static_cast<imp::_assumption_set>(a));
    }

    void solver::dec_ref(assumption a) {
        m_imp->dec_ref(static_cast<imp::_assumption_set>(a));
    }
        
    void solver::mk_clause(unsigned num_lits, literal * lits, assumption a) {
        return m_imp->mk_external_clause(num_lits, lits, a);
    }

    std::ostream& solver::display(std::ostream & out) const {
        return m_imp->display(out);
    }

    std::ostream& solver::display_var(std::ostream & out, unsigned j) const {
        return m_imp->display_var(out, j);
    }

    std::ostream& solver::display(std::ostream & out, literal l) const {
        return m_imp->display(out, l);
    }

    std::ostream& solver::display_assignment(std::ostream & out) const {
        return m_imp->display_assignment(out);
    }

    
    std::ostream& solver::display(std::ostream & out, unsigned n, literal const* ls) const {
        for (unsigned i = 0; i < n; ++i) {
            display(out, ls[i]);
            out << ";  ";
        }
        return out;
    }

    std::ostream& solver::display(std::ostream & out, literal_vector const& ls) const {
        return display(out, ls.size(), ls.data());
    }

    std::ostream& solver::display_smt2(std::ostream & out, literal l) const {
        return m_imp->display_smt2(out, l);
    }

    std::ostream& solver::display_smt2(std::ostream & out, unsigned n, literal const* ls) const {
        for (unsigned i = 0; i < n; ++i) {
            display_smt2(out, ls[i]);
            out << "  ";
        }
        return out;
    }

    std::ostream& solver::display(std::ostream& out, clause const& c) const {
        return m_imp->display(out, c);
    }

    std::ostream& solver::display_smt2(std::ostream & out) const {
        return m_imp->display_smt2(out);
    }

    std::ostream& solver::display_smt2(std::ostream & out, literal_vector const& ls) const {
        return display_smt2(out, ls.size(), ls.data());
    }

    std::ostream& solver::display(std::ostream & out, var x) const {
        return m_imp->m_display_var(out, x);
    }

    std::ostream& solver::display(std::ostream & out, atom const& a) const {
        return m_imp->display(out, a, m_imp->m_display_var);
    }

    display_var_proc const & solver::display_proc() const {
        return m_imp->m_display_var;
    }

    anum const & solver::value(var x) const {
        if (m_imp->m_assignment.is_assigned(x))
            return m_imp->m_assignment.value(x);
        return m_imp->m_zero;
    }
    
    lbool solver::bvalue(bool_var b) const {
        return m_imp->m_bvalues[b];
    }

    lbool solver::value(literal l) const {
        return m_imp->value(l);
    }

    bool solver::is_interpreted(bool_var b) const {
        return m_imp->m_atoms[b] != 0;
    }

    void solver::reset_statistics() {
        return m_imp->reset_statistics();
    }

    void solver::collect_statistics(statistics & st) {
        return m_imp->collect_statistics(st);
    }

    clause* solver::mk_clause(unsigned n, literal const* lits, bool learned, internal_assumption a) {
        return m_imp->mk_clause(n, lits, learned, static_cast<imp::_assumption_set>(a));
    }

    void solver::inc_simplify() {
        m_imp->m_stats.m_simplifications++;
    }

    bool solver::has_root_atom(clause const& c) const {
        return m_imp->has_root_atom(c);
    }

    void solver::add_bound(bound_constraint const& c) {
        m_imp->m_bounds.push_back(c);
    }

    assumption solver::join(assumption a, assumption b) {
        return (m_imp->m_asm.mk_join(static_cast<imp::_assumption_set>(a), static_cast<imp::_assumption_set>(b)));
    }
    
        
};
