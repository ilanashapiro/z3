/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    smt2_stream_pp.cpp

Abstract:

    Implementation of smt2_stream_pp. See header for design.

--*/
#include "ast/smt2_stream_pp.h"
#include "ast/format.h"
#include "util/smt2_util.h"
#include <sstream>

smt2_stream_pp::smt2_stream_pp(ast_manager & m)
    : m_manager(m), m_env(m) {
    // Emit single-line even inside format subtrees produced by pp_leaf /
    // pp_fdecl / pp_sort. flatten() enforces this too, but setting the
    // params keeps semantics consistent for any code path that flattens
    // via pp() rather than flatten().
    m_leaf_params.set_bool("single_line", true);
    m_leaf_params.set_uint("max_width",  UINT_MAX);
    m_leaf_params.set_uint("max_ribbon", UINT_MAX);
}

void smt2_stream_pp::flatten(format_ns::format * f) {
    if (!f) return;
    // Iterative depth-first walk to avoid deep C++ stacks on wide formats.
    svector<format_ns::format *> todo;
    todo.push_back(f);
    while (!todo.empty()) {
        format_ns::format * n = todo.back();
        todo.pop_back();
        switch (n->get_decl_kind()) {
        case format_ns::OP_STRING:
            m_out.append(n->get_decl()->get_parameter(0).get_symbol().bare_str());
            break;
        case format_ns::OP_INDENT:
            todo.push_back(to_app(n->get_arg(0)));
            break;
        case format_ns::OP_COMPOSE: {
            unsigned i = n->get_num_args();
            while (i > 0) { --i; todo.push_back(to_app(n->get_arg(i))); }
            break;
        }
        case format_ns::OP_CHOICE:
            // The flat branch is arg(0) by construction.
            todo.push_back(to_app(n->get_arg(0)));
            break;
        case format_ns::OP_LINE_BREAK:
        case format_ns::OP_LINE_BREAK_EXT:
            m_out.push_back(' ');
            break;
        default:
            break;
        }
    }
}

void smt2_stream_pp::emit(expr * e) {
    if (!e) { write("null"); return; }
    switch (e->get_kind()) {
    case AST_VAR:
        emit_var(to_var(e));
        return;
    case AST_QUANTIFIER:
        emit_quantifier(to_quantifier(e));
        return;
    case AST_APP: {
        app * a = to_app(e);
        unsigned num_args = a->get_num_args();
        if (num_args == 0) {
            // Delegate ALL constant/leaf formatting to the environment.
            // Every theory that ships with Z3 has already registered its
            // rules there; new theories extend one central place.
            format_ns::format_ref fr(format_ns::fm(m_manager));
            fr = m_env.pp_leaf(a, m_leaf_params);
            flatten(fr);
            return;
        }
        write('(');
        format_ns::format_ref fr(format_ns::fm(m_manager));
        unsigned len;
        fr = m_env.pp_fdecl(a->get_decl(), len);
        flatten(fr);
        for (unsigned i = 0; i < num_args; ++i) {
            write(' ');
            emit(a->get_arg(i));
        }
        write(')');
        return;
    }
    default:
        // AST_SORT / AST_FUNC_DECL shouldn't appear as unit literals. Fall
        // back through mk_ismt2_pp for parity.
        std::ostringstream oss;
        oss << mk_ismt2_pp(e, m_manager, m_leaf_params);
        m_out.append(oss.str());
        return;
    }
}

void smt2_stream_pp::emit_var(var * v) {
    unsigned idx = v->get_idx();
    if (idx < m_var_names.size()) {
        symbol const & s = m_var_names[m_var_names.size() - idx - 1];
        if (is_smt2_quoted_symbol(s)) write(mk_smt2_quoted_symbol(s));
        else                          write(s.str());
    }
    else {
        write("(:var ");
        write(std::to_string(idx));
        write(')');
    }
}

void smt2_stream_pp::emit_quantifier(quantifier * q) {
    // Quantifiers cannot appear as ground unit literals; on the rare path
    // where a caller does hand one in, defer to mk_ismt2_pp for full
    // fidelity (patterns, weights, qid, etc.). Kept correct, not fast.
    std::ostringstream oss;
    oss << mk_ismt2_pp(q, m_manager, m_leaf_params);
    m_out.append(oss.str());
}
