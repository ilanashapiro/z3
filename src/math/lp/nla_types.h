/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

  nla_types.h

Author:
  Lev Nachmanson (levnach)
  Nikolaj Bjorner (nbjorner)

Description:
  Types used for nla solver.
  
--*/

#pragma once

namespace nla {

    typedef lp::constraint_index     lpci;
    typedef lp::lconstraint_kind     llc;
    typedef lp::constraint_index     lpci;
    typedef lp::explanation          expl_set;
    typedef lp::lpvar                    lpvar;
    const lpvar null_lpvar = UINT_MAX;


    
    inline int rat_sign(const rational& r) { return r.is_pos()? 1 : ( r.is_neg()? -1 : 0); }
    inline rational rrat_sign(const rational& r) { return rational(rat_sign(r)); }
    inline bool is_set(unsigned j) {  return j != null_lpvar; } 
    inline bool is_even(unsigned k) { return (k & 1) == 0; }
    class ineq {
        lp::lconstraint_kind m_cmp;
        lp::lar_term         m_term;
        rational             m_rs;
    public:
        ineq(lp::lconstraint_kind cmp, const lp::lar_term& term, const rational& rs) : m_cmp(cmp), m_term(term), m_rs(rs) {}
        ineq(const lp::lar_term& term, lp::lconstraint_kind cmp, int i) : m_cmp(cmp), m_term(term), m_rs(rational(i)) {}
        ineq(const lp::lar_term& term, lp::lconstraint_kind cmp, const rational& rs) : m_cmp(cmp), m_term(term), m_rs(rs) {}
        ineq(lpvar v, lp::lconstraint_kind cmp, int i): m_cmp(cmp), m_term(v), m_rs(rational(i)) {}
        ineq(lpvar v, lp::lconstraint_kind cmp, rational const& r): m_cmp(cmp), m_term(v), m_rs(r) {}
        bool operator==(const ineq& a) const {
            return m_cmp == a.m_cmp && m_term == a.m_term && m_rs == a.m_rs;
        }
        const lp::lar_term& term() const { return m_term; };
        lp::lconstraint_kind cmp() const { return m_cmp;  };
        const rational& rs() const { return m_rs; };
    };
    
    class lemma {
        vector<ineq>     m_ineqs;
        lp::explanation  m_expl;
    public:
        void push_back(const ineq& i) { m_ineqs.push_back(i);}
        size_t size() const { return m_ineqs.size() + m_expl.size(); }
        const vector<ineq>& ineqs() const { return m_ineqs; }
        vector<ineq>& ineqs() { return m_ineqs; }
        lp::explanation& expl() { return m_expl; }
        const lp::explanation& expl() const { return m_expl; }
        bool is_conflict() const { return m_ineqs.empty() && !m_expl.empty(); }
        bool is_empty() const { return m_ineqs.empty() && m_expl.empty(); }
    };
    
    class core;
    //
    // lemmas are created in a scope.
    // when the destructor of lemma_builder is invoked
    // all constraints are assumed already added to the current_lemma
    // correctness of the lemma can be checked at this point.
    //
    class lemma_builder {
        char const* name;
        core& c;
        // the non-const version is private
        lemma& current();
        const lemma& current() const;
        
    public:
        lemma_builder(core& c, char const* name);
        ~lemma_builder();
        std::ostream& display(std::ostream& out) const;
        lemma_builder& operator&=(lp::explanation const& e);
        lemma_builder& operator&=(const monic& m);
        lemma_builder& operator&=(const factor& f);
        lemma_builder& operator&=(const factorization& f);
        lemma_builder& operator&=(lpvar j);
        lemma_builder& operator|=(ineq const& i);
        lemma_builder& explain_fixed(lpvar j);
        lemma_builder& explain_equiv(lpvar u, lpvar v);
        lemma_builder& explain_var_separated_from_zero(lpvar j);
        lemma_builder& explain_existing_lower_bound(lpvar j);
        lemma_builder& explain_existing_upper_bound(lpvar j);    
        
        lp::explanation& expl() { return current().expl(); }
        
        unsigned num_ineqs() const { return current().ineqs().size(); }
    };


    inline std::ostream& operator<<(std::ostream& out, lemma_builder const& l) {
        return l.display(out);
    }

    struct pp_fac {
        core const& c;
        factor const& f;
        pp_fac(core const& c, factor const& f): c(c), f(f) {}
    };
    
    struct pp_var {
        core const& c;
        lpvar v;
        pp_var(core const& c, lpvar v): c(c), v(v) {}
    };
    
    struct pp_factorization {
        core const& c;
        factorization const& f;
        pp_factorization(core const& c, factorization const& f): c(c), f(f) {}
    };
    
}
