/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    smt2_stream_pp.h

Abstract:

    Fast SMT2 emitter for high-throughput serialization of many small
    expressions (learned unit clauses, in particular). Writes directly into
    a std::string and skips the shared_occs / alias analysis performed by
    smt2_printer -- units are ground literals so aliasing never wins.

    Theory-specific formatting is delegated entirely to smt2_pp_environment
    (via pp_leaf, pp_fdecl, pp_sort). New plugins / literal kinds require no
    changes to this file: they extend the environment.

    Output is single-line: no line breaks, no aliases, no let-bindings.

--*/
#pragma once

#include "ast/ast.h"
#include "ast/ast_smt2_pp.h"
#include "util/params.h"
#include <string>

class smt2_stream_pp {
    ast_manager &            m_manager;
    smt2_pp_environment_dbg  m_env;
    params_ref               m_leaf_params;   // consulted by pp_leaf
    std::string              m_out;
    svector<symbol>          m_var_names;
    unsigned                 m_fresh_idx = 0;

    void write(char c)              { m_out.push_back(c); }
    void write(char const * s)      { m_out.append(s); }
    void write(std::string const & s){ m_out.append(s); }

    // Walk a format tree, appending to m_out. Single-line: line breaks
    // become a single space. Choices always take the flat branch. This is
    // the minimal subset of pp() we need since we never build wide format
    // trees ourselves -- only smt2_pp_environment's leaf outputs pass here.
    void flatten(format_ns::format * f);

    void emit(expr * e);
    void emit_var(var * v);
    void emit_quantifier(quantifier * q);

public:
    smt2_stream_pp(ast_manager & m);
    void reset() { m_out.clear(); m_var_names.reset(); m_fresh_idx = 0; }
    std::string const & buffer() const { return m_out; }
    std::string && take_buffer() { return std::move(m_out); }
    void print(expr * e) { emit(e); }
};
