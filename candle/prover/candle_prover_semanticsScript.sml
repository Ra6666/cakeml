(*
  Top-level soundness theorem for the Candle theorem prover.
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     evaluateTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory candle_kernelProgTheory
open permsTheory candle_kernel_funsTheory candle_kernel_valsTheory
     candle_prover_invTheory candle_prover_evaluateTheory ast_extrasTheory
     candle_basis_evaluateTheory semanticsTheory;
open holKernelProofTheory basisProgTheory ml_hol_kernel_funsProgTheory;
open ml_translatorLib ml_progTheory;
local open ml_progLib in end

val _ = new_theory "candle_prover_semantics";

val _ = translation_extends "candle_kernelProg";

Theorem LPREFIX_LNTH:
  ∀n xs l ll.
    LPREFIX xs l ∧
    LNTH n xs = NONE ∧
    LTAKE n l = SOME ll ⇒
      LPREFIX xs (fromList ll)
Proof
  Induct \\ rpt Cases \\ rw [llistTheory.fromList_def]
  \\ gvs [LPREFIX_LCONS, SF SFY_ss]
QED

(* TODO move to evaluateProps (or wherever evaluate_decs_cons is)
 *)

Theorem evaluate_decs_append:
  ∀ds1 s env ds2.
    evaluate_decs s env (ds1 ++ ds2) =
    case evaluate_decs s env ds1 of
      (s1,Rval env1) =>
        (case evaluate_decs s1 (extend_dec_env env1 env) ds2 of
           (s2,r) => (s2,combine_dec_result env1 r))
    | (s1,Rerr v7) => (s1,Rerr v7)
Proof
  Induct \\ rw []
  >- (
    rw [extend_dec_env_def, combine_dec_result_def]
    \\ rpt CASE_TAC)
  \\ once_rewrite_tac [evaluate_decs_cons] \\ simp []
  \\ gs [combine_dec_result_def, extend_dec_env_def]
  \\ rpt CASE_TAC \\ gs []
QED

(* TODO move *)

Theorem env_ok_write_cons:
  env_ok ctxt env ∧
  (t ∈ kernel_types ⇒ nm ∈ kernel_ctors) ⇒
    env_ok ctxt (write_cons nm (n, TypeStamp s t) env)
Proof
  simp [env_ok_def, write_cons_def, SF SFY_ss]
  \\ strip_tac
  \\ Cases \\ simp [nsLookup_nsBind_compute]
  \\ rw [] \\ gs [SF SFY_ss, namespaceTheory.id_to_n_def]
QED

(* TODO move *)

Theorem env_ok_extend_dec_env:
  env_ok ctxt env1 ∧
  env_ok ctxt env2 ⇒
    env_ok ctxt (extend_dec_env env1 env2)
Proof
  rw [env_ok_def, extend_dec_env_def, nsLookup_nsAppend_some] \\ gs [SF SFY_ss]
QED

(* TODO move *)

Theorem env_ok_write_mod:
  env_ok ctxt env1 ∧
  env_ok ctxt env2 ⇒
    env_ok ctxt (write_mod mn env1 env2)
Proof
  rw [env_ok_def, write_mod_def, nsLookup_nsAppend_some, nsLookup_nsLift,
      CaseEq "id"]
  \\ gs [namespaceTheory.id_to_n_def, SF SFY_ss]
QED

(* TODO move *)

Theorem env_ok_write_Exn:
  env_ok ctxt env ⇒
  env_ok ctxt (write_cons nm (n,ExnStamp m) env)
Proof
  simp [env_ok_def, write_cons_def, SF SFY_ss]
  \\ strip_tac
  \\ Cases \\ rw [nsLookup_nsBind_compute] \\ gs [SF SFY_ss]
QED

(* -------------------------------------------------------------------------
 * - The basis program:
 *   basis, basis_env, basis_state
 * - The candle program (includes the former):
 *   candle_code, candle_init_env, candle_init_state
 * ------------------------------------------------------------------------- *)

Overload basis_env = (basis_Decls_thm |> concl |> rator |> rand);

Overload basis_state = (basis_Decls_thm |> concl |> rand |> rator);

(* -------------------------------------------------------------------------
 * Show that the basis program satisfies post_state_ok, simple_dec and
 * safe_dec. Use this to show basis_env is env_ok.
 * ------------------------------------------------------------------------- *)

Theorem post_state_ok_basis_state:
  post_state_ok (basis_state ffi)
Proof
  rw [post_state_ok_def, kernel_types_def, kernel_locs_def,
      the_type_constants_def, the_term_constants_def,
      the_axioms_def, the_context_def]
  \\ EVAL_TAC \\ gs []
QED

Theorem basis_decs_ok:
  EVERY simple_dec basis ∧
  EVERY safe_dec basis
Proof
  once_rewrite_tac [basis_def]
  \\ conj_tac
  \\ EVAL_TAC
  \\ simp [namespaceTheory.id_to_n_def]
QED

Theorem env_ok_basis_env:
  env_ok ctxt basis_env
Proof
  assume_tac basis_Decls_thm
  \\ gs [Decls_def]
  \\ drule_then (qspec_then ‘ctxt’ mp_tac) evaluate_basis_v_ok_decs
  \\ simp [basis_decs_ok, post_state_ok_basis_state, env_ok_init_env]
  \\ impl_tac
  >- (
    simp [init_env_def]
    \\ simp [namespacePropsTheory.nsLookup_Bind_v_some, PULL_EXISTS]
    \\ rw [] \\ gs [kernel_types_def])
  \\ rw [env_ok_def, extend_dec_env_def, nsLookup_nsAppend_some, SF SFY_ss]
QED

(* --------------------------------------------------------------------------
 * Show that the candle_init_state is state_ok.
 * ------------------------------------------------------------------------- *)

(* TODO Move this to standard/ml_kernel; a copy of this is used by the
 *      OpenTheory reader.
 *)

Definition init_refs_def:
  init_refs = <|
      the_type_constants := init_type_constants;
      the_term_constants := init_term_constants;
      the_axioms         := init_axioms;
      the_context        := init_context |>
End

Theorem STATE_init_refs:
  STATE init_context init_refs
Proof
  simp [STATE_def, CONTEXT_def, init_type_constants_def, init_axioms_def,
        init_term_constants_def, init_context_def, init_refs_def,
        holSyntaxTheory.init_ctxt_def, holSyntaxTheory.extends_def]
QED

Theorem candle_init_state_stamp:
  n ∈ kernel_types ⇒ n < (candle_init_state ffi).next_type_stamp
Proof
  EVAL_TAC \\ gs []
QED

Theorem kernel_refs_distinct[local,simp]:
  the_type_constants ≠ the_term_constants ∧
  the_type_constants ≠ the_axioms ∧
  the_type_constants ≠ the_context ∧
  the_term_constants ≠ the_axioms ∧
  the_term_constants ≠ the_context ∧
  the_axioms ≠ the_context
Proof
  simp [the_type_constants_def, the_term_constants_def, the_context_def,
        the_axioms_def]
QED

Theorem LLOOKUPs[local]:
  (Loc loc = the_type_constants ⇒
     LLOOKUP (candle_init_state ffi).refs loc =
     SOME (Refv init_type_constants_v)) ∧
  (Loc loc = the_term_constants ⇒
     LLOOKUP (candle_init_state ffi).refs loc =
     SOME (Refv init_term_constants_v)) ∧
  (Loc loc = the_axioms ⇒
     LLOOKUP (candle_init_state ffi).refs loc =
     SOME (Refv init_axioms_v)) ∧
  (Loc loc = the_context ⇒
     LLOOKUP (candle_init_state ffi).refs loc =
     SOME (Refv init_context_v))
Proof
  rpt strip_tac
  \\ gvs [the_type_constants_def, the_term_constants_def, the_axioms_def,
          the_context_def]
  \\ rw [candle_init_state_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
QED

Theorem candle_init_state_refs:
  loc ∈ kernel_locs ⇒
    kernel_loc_ok init_refs loc (candle_init_state ffi).refs
Proof
  gvs [kernel_locs_def, kernel_loc_ok_def]
  \\ rw [] \\ gs []
  \\ FIRST (map (drule_then (qspec_then ‘ffi’ assume_tac))
                (CONJUNCTS LLOOKUPs))
  \\ first_assum (irule_at Any) \\ gs []
  \\ simp [init_refs_def, init_type_constants_v_thm, init_term_constants_v_thm,
           init_axioms_v_thm, init_context_v_thm]
QED

Theorem candle_init_state_eval[simp]:
  eval_state_ok (candle_init_state ffi).eval_state
Proof
  EVAL_TAC
QED

Theorem candle_init_state_ffi[simp]:
  (candle_init_state ffi).ffi = ffi
Proof
  EVAL_TAC
QED

Theorem candle_init_state_state_ok:
  ffi.io_events = [] ⇒
  state_ok init_context (candle_init_state ffi)
Proof
  strip_tac
  \\ simp [state_ok_def, candle_init_state_stamp]
  \\ irule_at Any STATE_init_refs
  \\ simp [candle_init_state_refs,kernel_locs]
  \\ rw [LLOOKUP_EQ_EL, EL_APPEND_EQN, candle_init_state_def, refs_defs]
  \\ ‘loc = 0’ by fs []
  \\ fs [ref_ok_def]
QED

(* --------------------------------------------------------------------------
 * First prove that all kernel values are v_ok (this follows from the
 * definition of v_ok but it's nice to have in one theorem.)
 * ------------------------------------------------------------------------- *)

fun prove_v_ok v_tm =
  auto_prove
    ("v_ok for " ^ (#1 (dest_const v_tm)))
    (“v_ok ctxt (^v_tm)”,
     irule v_ok_KernelVals
     \\ irule v_ok_Inferred
     \\ irule inferred_KernelFuns
     \\ simp_tac list_ss [kernel_funs_def]);

Theorem v_ok_kernel_funs[local] =
  kernel_funs_def |> concl |> rhs
  |> pred_setSyntax.strip_set
  |> map prove_v_ok
  |> LIST_CONJ;

(* --------------------------------------------------------------------------
 * Now prove that candle_init_env is env_ok.
 * ------------------------------------------------------------------------- *)

(* TODO move *)

Theorem env_ok_empty[local]:
  env_ok ctxt <| v := nsEmpty; c := nsEmpty |>
Proof
  rw [env_ok_def]
QED

(* Prove env_ok and cache intermediate results. This code is very brittle.
 *)

local
  val kernel_types_term = kernel_types_def |> concl |> lhs;
  val kernel_ctors_term = kernel_ctors_def |> concl |> lhs;
  val write_cons_term =
    write_cons_def |> SPEC_ALL |> concl |> lhs |> rator |> rator |> rator;
  val v_ok_term = v_ok_def |> CONJUNCT1 |> concl |> lhs |> rator |> rator;
  val write_term =
    write_def |> SPEC_ALL |> concl |> lhs |> rator |> rator |> rator;
  val write_mod_term =
    write_mod_def |> SPEC_ALL |> concl |> lhs |> rator |> rator |> rator;
  val merge_env_term = merge_env_def |> SPEC_ALL |> concl |> lhs |> rator
                       |> rator;
  val env_ok_term = env_ok_def |> concl |> lhs |> rator |> rator;
  val init_context_term = init_context_def |> concl |> lhs;
  val env_type = env_ok_def |> concl |> lhs |> rand |> type_of;
  val inst_context = INST [“ctxt:update list”|->init_context_term];
  val empty_net = Net.insert (“basis_env”, inst_context env_ok_basis_env)
                             Net.empty;
  val empty_net = Net.insert (“empty_env”, inst_context env_ok_empty_env)
                             empty_net;
  val empty_net = Net.insert (“<|v:=nsEmpty;c:=nsEmpty|>”,
                             inst_context env_ok_empty)
                             empty_net;
  val prev_ths = ref empty_net;
  fun dest_env_ok tm =
    let
      val (envok_ctxt, env) = dest_comb tm
      val (envok, ctxt) = dest_comb envok_ctxt
      val _ = same_const envok env_ok_term orelse
              failwith "not env_ok"
      val _ = same_const ctxt init_context_term orelse
              failwith "not init_context"
    in
      env
    end
    handle HOL_ERR _ => failwith ("dest_env_ok: not an env_ok")
  fun mk_env_ok tm =
    mk_comb (mk_comb (env_ok_term, init_context_term), tm);
  fun prove_v_ok tm =
    let
      val goal = mk_comb (mk_comb (v_ok_term, init_context_term), tm)
      val th = Lib.first (can (Lib.C match_term goal) o concl)
                         (CONJUNCTS v_ok_kernel_funs)
    in
      inst_context th
    end;
  val write_th = inst_context env_ok_write |> REWRITE_RULE [GSYM AND_IMP_INTRO];
  val merge_env_th = inst_context env_ok_merge_env
                     |> REWRITE_RULE [GSYM AND_IMP_INTRO];
  val write_mod_th = inst_context env_ok_write_mod
                     |> REWRITE_RULE [GSYM AND_IMP_INTRO];
  val write_cons_th = inst_context env_ok_write_cons
                      |> REWRITE_RULE [GSYM AND_IMP_INTRO];
  val write_exn_th = inst_context env_ok_write_Exn
  fun prove_bare tm = (* bare environment *)
    let
      val {Name, Thy, Ty} = dest_thy_const tm
      val _ = Ty = env_type orelse failwith "not an env"
      val defn = fetch Thy (Name ^ "_def")
      val th = iffRL (AP_TERM “env_ok init_context” defn)
      val (subgoal, _) = dest_imp (concl th)
      val th' = env_ok_conv subgoal
    in
      MATCH_MP th th'
    end
  and prove_merge_env tm = (* merge_env e1 e2 *)
    let
      val (me1, e2) = dest_comb tm
      val (me, e1) = dest_comb me1
      val _ = same_const me merge_env_term orelse
              failwith "not merge_env"
      val sg1 = mk_env_ok e1
      val sg2 = mk_env_ok e2
      val th1 = env_ok_conv sg1
      val th2 = env_ok_conv sg2
    in
      MATCH_MP (MATCH_MP merge_env_th th1) th2
    end
  and prove_write_mod tm = (* write_mod mn env1 env2 *)
    let
      val (wmmne1, e2) = dest_comb tm
      val (wmmn, e1) = dest_comb wmmne1
      val (wm, mn) = dest_comb wmmn
      val _ = same_const wm write_mod_term orelse
              failwith "not write_mod"
      val sg1 = mk_env_ok e1
      val sg2 = mk_env_ok e2
      val th1 = env_ok_conv sg1
      val th2 = env_ok_conv sg2
    in
      INST [“mn:string”|->mn] (MATCH_MP (MATCH_MP write_mod_th th1) th2)
    end
  and prove_write tm = (* write nm v env *)
    let
      val (wnv, env) = dest_comb tm
      val (wn, v) = dest_comb wnv
      val (w, n) = dest_comb wn
      val sg1 = mk_env_ok env
      val th1 = env_ok_conv sg1
      val th2 = prove_v_ok v
    in
      INST [“nm:string”|->n] (MATCH_MP (MATCH_MP write_th th1) th2)
    end
  and prove_write_cons tm = (* write_cons n (TypeStamp s t) env *)
    let
      val (wcns, env) = dest_comb tm
      val (wcn, s) = dest_comb wcns
      val (wc, n) = dest_comb wcn
      val _ = same_const wc write_cons_term orelse
              failwith "not write_cons"
      val m = dest_pair s |> #1
      val t = dest_pair s |> #2 |> rand
      val nm = dest_pair s |> #2 |> rator |> rand
      val sg1 = mk_env_ok env
      val th1 = env_ok_conv sg1
      val goal =
        mk_imp (pred_setSyntax.mk_in (t, kernel_types_term),
                pred_setSyntax.mk_in (nm, kernel_ctors_term))
      val th2 = SIMP_CONV list_ss [kernel_types_def, kernel_ctors_def] goal
      val th3 = INST [“n:num”|->m,
                      “s:string”|->nm,
                      “t:num”|->t,
                      “nm:string”|->n] (MATCH_MP write_cons_th th1)
    in
      MATCH_MP th3 (EQT_ELIM th2)
    end
  and prove_write_Exn tm = (* write_cons n (ExnStamp ...) env *)
    let
      val (wcns, env) = dest_comb tm
      val (wcn, s) = dest_comb wcns
      val (wc, n) = dest_comb wcn
      val _ = same_const wc write_cons_term orelse
              failwith "not write_cons"
      val sg1 = mk_env_ok env
      val th1 = env_ok_conv sg1
      val m = s |> dest_pair |> #2 |> rand
      val k = s |> dest_pair |> #1
    in
      INST [“n:num”|->k,
            “m:num”|->m,
            “nm:string”|->n] (MATCH_MP write_exn_th th1)
    end
  and env_ok_conv tm =
    let
      val env_tm = dest_env_ok tm
      fun prove env_tm =
          let
            fun prover env_tm =
              prove_bare env_tm handle HOL_ERR _ =>
              prove_merge_env env_tm handle HOL_ERR _ =>
              prove_write_mod env_tm handle HOL_ERR _ =>
              prove_write env_tm handle HOL_ERR _ =>
              prove_write_cons env_tm handle HOL_ERR _ =>
              prove_write_Exn env_tm
            val th = prover env_tm
          in
            prev_ths := Net.insert (env_tm, th) (!prev_ths);
            th
          end
    in
      case Net.match env_tm (!prev_ths) of
        th::_ => th (* if concl th ~~ tm then th else prove env_tm *)
      | _ => prove env_tm
    end;
in
  (*
  fun reset_prevs () = prev_ths := empty_net;
  fun get_prevs () = Net.listItems (!prev_ths)
   *)
  val prove_env_ok = env_ok_conv
end

Theorem env_ok_candle_init_env =
  prove_env_ok “env_ok init_context candle_init_env”;

(* --------------------------------------------------------------------------
 * Top-level semantics theorem.
 * ------------------------------------------------------------------------- *)

(* TODO Print context updates on FFI
    -- Magnus: actually, we might want to print the entire context
               for each theorem to make soundness statement simple
   TODO: Use 'ffi
 *)

(* TODO why do these both exist? *)

Theorem init_context_init_ctxt[local,simp]:
  init_ctxt = init_context
Proof
  rw [holSyntaxTheory.init_ctxt_def, init_context_def]
QED

Theorem semantics_thm:
  semantics_prog (init_state ffi) init_env (candle_code ++ prog) res ∧
  EVERY safe_dec prog ∧
  ffi.io_events = [] ∧
  res ≠ Fail ⇒
    ∃ctxt.
      (∀outcome io_list.
         res = Terminate outcome io_list ⇒
           EVERY (ok_event ctxt) io_list) ∧
      (∀io_trace.
         res = Diverge io_trace ⇒
           every (ok_event ctxt) io_trace)
Proof
  strip_tac
  \\ Cases_on ‘res’ \\ gs []
  >~ [‘Terminate outcome io_list’] >- (
    gs [semanticsTheory.semantics_prog_def]
    \\ gs [semanticsTheory.evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ gvs []
    \\ assume_tac candle_prog_thm
    \\ gvs [evaluate_decs_append, CaseEqs ["prod", "semanticPrimitives$result"]]
    >- (
      gs [ml_progTheory.Decls_def]
      \\ dxrule_then (qspec_then ‘k’ mp_tac) evaluate_decs_add_to_clock
      \\ qpat_x_assum ‘evaluate_decs _ _ _ = (s1, Rval _)’ assume_tac
      \\ dxrule_then (qspec_then ‘ck1’ mp_tac) evaluate_decs_add_to_clock
      \\ rw []
      \\ qpat_x_assum ‘evaluate_decs s1 _ prog = _’ assume_tac
      \\ drule_then (qspec_then ‘init_context’ mp_tac)
                    (el 3 (CONJUNCTS evaluate_v_ok))
      \\ impl_tac
      >- (
        drule_then assume_tac candle_init_state_state_ok
        \\ assume_tac env_ok_candle_init_env \\ gs []
        \\ irule_at Any env_ok_extend_dec_env \\ gs [env_ok_init_env]
        \\ gs [state_ok_def, semanticPrimitivesTheory.state_component_equality]
        \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
      \\ strip_tac
      \\ rename1 ‘combine_dec_result _ res’ \\ Cases_on ‘res’ \\ gs []
      >- (
        gs [state_ok_def]
        \\ first_assum (irule_at Any) \\ gs [])
      \\ rename1 ‘Rerr err’ \\ Cases_on ‘err’ \\ gs []
      >- (
        gs [state_ok_def]
        \\ first_assum (irule_at Any) \\ gs [])
      \\ first_assum (irule_at Any) \\ gs [])
    \\ gs [ml_progTheory.Decls_def]
    \\ dxrule_then (qspec_then ‘k’ mp_tac) evaluate_decs_add_to_clock
    \\ dxrule_then (qspec_then ‘ck1’ mp_tac) evaluate_decs_add_to_clock
    \\ rw [] \\ gs [CaseEqs ["semanticPrimitives$result"]])
  \\ gs [semanticsTheory.semantics_prog_def]
  \\ gs [lprefix_lub_def, PULL_EXISTS, every_LNTH]
  \\ qabbrev_tac ‘ff : num -> io_event llist =
                    λk. fromList (FST (evaluate_prog_with_clock
                                         (init_state ffi) init_env k
                                         (candle_code ++ prog))).io_events’
  \\ gs []
  \\ cheat
(*
    first_x_assum (qspec_then `k` assume_tac)
    \\ first_x_assum (qspec_then `k` strip_assume_tac)
    \\ imp_res_tac LPREFIX_LNTH
    \\ pop_assum kall_tac
    \\ fs [Abbr `ff`, semanticsTheory.evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ fs []
    \\ drule kernel_evaluate_decs
    \\ disch_then drule
    \\ rw [extract_events_def]
    \\ fs [EVERY_MEM, MEM_MAP, MEM_FILTER, PULL_EXISTS, ELIM_UNCURRY,
           CaseEq "io_event"]
    \\ PURE_CASE_TAC \\ rw []
    \\ first_x_assum irule
    \\ fs [LNTH_fromList]
    \\ drule EL_MEM
    \\ srw_tac [SATISFY_ss] []
  \\ `!k. LNTH n (ff k) = NONE` by metis_tac [option_nchotomy] \\ fs []
  \\ `F` suffices_by fs [] \\ rw []
  \\ qpat_x_assum `!ub. _ ==> _` mp_tac
  \\ simp []
  \\ drule LNTH_LTAKE \\ rw []
  \\ qexists_tac `fromList ll` \\ fs []
  \\ fsrw_tac [SATISFY_ss] [LTAKE_LPREFIX, LPREFIX_lemma] *)
QED

val _ = export_theory ();
