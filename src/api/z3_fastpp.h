/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    z3_fastpp.h

Abstract:

    Opt-in fast SMT-LIB2 serialization APIs.

    The functions in this header are additive: the standard
    Z3_ast_to_string / Z3_solver_get_units path is preserved unchanged.
    Clients who want the fast path must explicitly call the entries
    declared here. This keeps the standard API's output format stable and
    lets callers A/B test the fast path against baseline as an ablation.

    Design notes:

    - Z3_ast_to_string_fast serializes one AST using a direct AST->string
      emitter that skips the format-tree intermediate, shared_occs, and
      alias/let analysis in ast_smt2_pp. All theory-specific formatting
      (numerals, BV/FP/string literals, indexed decls, ...) is delegated
      to smt2_pp_environment::pp_leaf / pp_fdecl, so support for new
      plugins costs zero changes in this header.

    - Z3_solver_get_units_smt2 batches every unit produced by the solver
      into a single newline-separated blob, memoizing each unit's rendered
      string by hash-consed expr* in a per-context cache. Intended for
      high-throughput unit harvesting where per-call boundary costs
      dominate.

    - Z3_reset_smt2_cache drops the memoization state (rarely needed).

    All returned strings are owned by the Z3 context and are valid only
    until the next Z3 API call that writes to the context's external
    string buffer -- the same rule as Z3_ast_to_string. Callers should
    copy or consume the bytes before making another API call.

Author:

--*/
#pragma once

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

    /** \defgroup capi C API */
    /**@{*/

    /** @name Fast SMT-LIB2 serialization */
    /**@{*/

    /**
       \brief Single-AST fast serializer. Byte-for-byte compatible (up to
       whitespace) with Z3_ast_to_string under the default print mode, but
       skips the format-tree machinery used by mk_ismt2_pp. Emits single-line
       output (no line breaks even for large expressions). No caching --
       useful as an ablation to compare emitter cost alone against
       Z3_ast_to_string.

       The returned string is valid only until the next API call that writes
       to the context's external string buffer.

       def_API('Z3_ast_to_string_fast', STRING, (_in(CONTEXT), _in(AST)))
    */
    Z3_string Z3_API Z3_ast_to_string_fast(Z3_context c, Z3_ast a);

    /**
       \brief Batch-serialize every unit clause of a solver into one
       newline-separated SMT-LIB2 blob, using the same fast emitter as
       Z3_ast_to_string_fast plus a per-context expr* -> string cache.
       Repeated calls hit the cache and reduce to memcpy on units seen
       before, which is the common case across incremental / warm-context
       workloads.

       Equivalent to iterating Z3_solver_get_units and calling
       Z3_ast_to_string_fast on each entry, joining with '\n', but avoids
       the per-unit API boundary and reuses memoized bytes.

       def_API('Z3_solver_get_units_smt2', STRING, (_in(CONTEXT), _in(SOLVER)))
    */
    Z3_string Z3_API Z3_solver_get_units_smt2(Z3_context c, Z3_solver s);

    /**
       \brief Clear the fast-serialization cache used by
       Z3_solver_get_units_smt2. The cache is purely additive within a
       process; call this only if you want to free the memoized bytes
       explicitly.

       def_API('Z3_reset_smt2_cache', VOID, (_in(CONTEXT),))
    */
    void Z3_API Z3_reset_smt2_cache(Z3_context c);

    /**@}*/
    /**@}*/

#ifdef __cplusplus
}
#endif // __cplusplus
