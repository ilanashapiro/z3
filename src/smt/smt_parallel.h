/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_parallel.h

Abstract:

    Parallel SMT, portfolio loop specialized to SMT core.

Author:

    Ilana Shapiro - 2025

Revision History:

--*/
#pragma once

#include "smt/smt_context.h"
#include "util/search_tree.h"
#include "util/uint_set.h"
#include "ast/sls/sls_smt_solver.h"
#include <unordered_map>
#include <thread>
#include <mutex>


namespace smt {

    struct cube_config {
        using literal = expr_ref;
        static bool literal_is_null(expr_ref const& l) { return l == nullptr; }
        static std::ostream& display_literal(std::ostream& out, expr_ref const& l) { return out << mk_bounded_pp(l, l.get_manager()); }
    };

    class parallel {
        context& ctx;
        unsigned num_threads;
        bool m_should_run_sls = false;

        struct shared_clause {
            unsigned id = 0;
            unsigned source_worker_id;
            expr_ref clause;
            search_tree::node<cube_config>* valid_at = nullptr;
            unsigned score = 0;
            unsigned clause_size = 0;
            unsigned term_size = 0;
            bool is_unit = false;
            bool root_valid = false;
            shared_clause(ast_manager& m): source_worker_id(0), clause(m) {}
        };

        struct local_shared_clause {
            unsigned id = 0;
            expr_ref clause;
            expr_ref guard;
            search_tree::node<cube_config>* valid_at = nullptr;
            unsigned score = 0;
            bool root_valid = false;
            local_shared_clause(ast_manager& m): clause(m), guard(m) {}
        };

        class batch_manager {        

            enum state {
                is_running,
                is_sat,
                is_unsat,
                is_exception_msg,
                is_exception_code
            };

            struct stats {
                unsigned m_max_cube_depth = 0;
                unsigned m_num_cubes = 0;
                unsigned m_num_cores_reduced = 0;       // Total cores that were minimized
                unsigned m_total_literals_removed = 0;  // Total literals removed
            };


            ast_manager& m;
            parallel& p;
            std::mutex mux;
            state m_state = state::is_running;
            stats m_stats;
            using node = search_tree::node<cube_config>;
            search_tree::tree<cube_config> m_search_tree;
            
            unsigned m_exception_code = 0;
            std::string m_exception_msg;
            vector<shared_clause> shared_clause_db;
            obj_map<expr, unsigned> shared_clause_index;

            // called from batch manager to cancel other workers if we've reached a verdict
            void cancel_workers() {
                IF_VERBOSE(1, verbose_stream() << "Canceling workers\n");
                for (auto& w : p.m_workers) 
                    w->cancel();
            }

            void cancel_sls_worker() {
                if (!p.m_sls_worker)
                    return;
                IF_VERBOSE(1, verbose_stream() << "Canceling SLS worker\n");
                p.m_sls_worker->cancel();
            }

            void cancel_background_threads() {
                cancel_workers();
                cancel_sls_worker();  
            }

            void init_parameters_state();

        public:
            batch_manager(ast_manager& m, parallel& p) : m(m), p(p), m_search_tree(expr_ref(m)) { }

            void initialize();

            void set_unsat(ast_translation& l2g, expr_ref_vector const& unsat_core);
            void set_sat(ast_translation& l2g, model& m);
            void set_exception(std::string const& msg);
            void set_exception(unsigned error_code);
            void collect_statistics(::statistics& st) const;
            
            // Aggregate worker statistics
            void add_core_minimization_stats(unsigned cores_reduced, unsigned literals_removed) {
                std::scoped_lock lock(mux);
                m_stats.m_num_cores_reduced += cores_reduced;
                m_stats.m_total_literals_removed += literals_removed;
            }

            bool get_cube(ast_translation& g2l, unsigned id, expr_ref_vector& cube, node*& n);
            void backtrack(ast_translation& l2g, expr_ref_vector const& core, node* n);
            void split(ast_translation& l2g, unsigned id, node* n, expr* atom, uint64_t effort);
            node* current_scope(ast_translation& l2g, node* n, expr_ref_vector const& core) const;

            void collect_clause(ast_translation& l2g, unsigned source_worker_id, node* valid_at, expr* clause);
            void return_shared_clauses(ast_translation& g2l, unsigned worker_id, node* current_node, uint_set const& known_ids, vector<local_shared_clause>& result);

            lbool get_result() const;
        };

        class worker {
            struct config {
                unsigned m_threads_max_conflicts = 1000;
                bool m_share_units = true;
                bool m_share_conflicts = true;
                bool m_share_units_relevant_only = true;
                bool m_share_units_initial_only = true;
                unsigned m_clause_share_batch = 32;
                unsigned m_clause_share_max_lits = 8;
                unsigned m_clause_share_max_term_size = 64;
                double m_max_conflict_mul = 1.5;
                bool m_inprocessing = false;
                bool m_sls = false;
                bool m_core_minimize = false;
                unsigned m_inprocessing_delay = 1;
                unsigned m_max_cube_depth = 20;
                unsigned m_max_conflicts = UINT_MAX;
            };

            using node = search_tree::node<cube_config>;

            unsigned id; // unique identifier for the worker
            parallel& p;
            batch_manager& b;
            ast_manager m;
            expr_ref_vector asms;
            expr_ref_vector m_active_clause_guards;
            smt_params m_smt_params;
            config m_config;
            random_gen m_rand;
            scoped_ptr<context> ctx;
            ast_translation m_g2l, m_l2g;

            unsigned m_num_shared_units = 0;
            unsigned m_num_initial_atoms = 0;
            uint64_t m_last_check_effort = 1;
            uint_set m_known_shared_clause_ids;
            vector<local_shared_clause> m_shared_clauses;
            std::unordered_map<node*, expr_ref> m_node_guards;
            obj_map<expr, node*> m_guard_to_node;
            
            // Core minimization statistics
            unsigned m_num_cores_reduced = 0;           // How many cores were successfully minimized
            unsigned m_total_literals_removed = 0;      // Total literals removed across all minimizations
            
            expr_ref get_split_atom();
            expr_ref get_or_create_guard(node* n);
            bool is_guard(expr* e, node*& n) const;
            void extract_tree_core(expr_ref_vector const& unsat_core, expr_ref_vector& tree_core);

            lbool check_cube(expr_ref_vector const& cube, node* current_node);
            void share_units(node* current_node);
            void collect_shared_clauses(node* current_node);
            void append_active_clause_guards(node* current_node, expr_ref_vector& target);

            void update_max_thread_conflicts() {
                m_config.m_threads_max_conflicts = (unsigned)(m_config.m_max_conflict_mul * m_config.m_threads_max_conflicts);
            } // allow for backoff scheme of conflicts within the thread for cube timeouts.

            void simplify();

        public:
            worker(unsigned id, parallel& p, expr_ref_vector const& _asms);
            void run();

            void cancel();
            void collect_statistics(::statistics& st) const;

            // Statistics accessors for aggregation
            unsigned get_num_cores_reduced() const { return m_num_cores_reduced; }
            unsigned get_total_literals_removed() const { return m_total_literals_removed; }

            reslimit& limit() {
                return m.limit();
            }

        };

        class sls_worker {
            parallel &p;
            batch_manager &b;
            ast_manager m;
            ast_translation m_g2l, m_l2g;
            scoped_ptr<sls::smt_solver> m_sls;
            params_ref m_params;

            public:
                sls_worker(parallel &p);
                void cancel();
                void run();
                void collect_statistics(::statistics& st) const;

                reslimit &limit() {
                    return m.limit();
                }
        };

        batch_manager m_batch_manager;
        scoped_ptr_vector<worker> m_workers;
        scoped_ptr<sls_worker> m_sls_worker;

    public:
        parallel(context& ctx) : 
            ctx(ctx),
            num_threads(std::min(
                (unsigned)std::thread::hardware_concurrency(),
                ctx.get_fparams().m_threads)),
            m_batch_manager(ctx.m, *this) {}

        lbool operator()(expr_ref_vector const& asms);
    };

}
