(*Generated by Lem from fpOpt.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory libTheory fpValTreeTheory;

val _ = numLib.prefer_num();



val _ = new_theory "fpOpt"

(*
  Definition of the fp_pattern language for Icing optimizations
*)

(*open import Pervasives*)
(*open import Lib*)
(*open import FpValTree*)

val _ = Hol_datatype `
 fp_pat =
       Word of word64
     | Var of num
     | Unop of fp_uop => fp_pat
     | Binop of fp_bop => fp_pat => fp_pat
     | Terop of fp_top => fp_pat => fp_pat => fp_pat
     (* | Pred of fp_pred * fp_pat *)
     | Cmp of fp_cmp => fp_pat => fp_pat
     | Optimise of fp_opt => fp_pat`;


(* Substitutions are maps (paired lists) from numbers to 'a *)
val _ = type_abbrev((*  'v *) "subst" , ``: (num # 'v) list``);

(*val substLookup: forall 'v. subst 'v -> nat -> maybe 'v*)
 val _ = Define `
 ((substLookup:(num#'v)list -> num -> 'v option) ([]) n=  NONE)
    /\ ((substLookup:(num#'v)list -> num -> 'v option) ((m, v)::s) n=
       (if (m = n) then SOME v else substLookup s n))`;


(*val substUpdate: forall 'v. nat -> 'v -> subst 'v -> maybe (subst 'v)*)
 val substUpdate_defn = Hol_defn "substUpdate" `
 ((substUpdate:num -> 'v ->(num#'v)list ->((num#'v)list)option) n v1 s=
     ((case s of
      [] => NONE
    | (s1::sN) =>
      (case s1 of
        (m,v2) =>
        if (n = m) then SOME ((n,v1)::sN)
        else
          (case (substUpdate n v1 sN) of
            NONE => NONE
          | SOME sNew => SOME ((m,v2)::sNew)
          )
      )
    )))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn substUpdate_defn;

(*val substAdd: forall 'v. nat -> 'v -> subst 'v -> subst 'v*)
 val _ = Define `
 ((substAdd:num -> 'v ->(num#'v)list ->(num#'v)list) n v s=
     ((case (substUpdate n v s) of
      SOME sNew => sNew
    | NONE => (n,v)::s
    )))`;


(* Matching a fp_pattern with the top-level of a value tree,
  if a matching exists an option with a substitution is returned.
  The matcher takes an additional substituion as argument to make sure
  that we do not double match a fp_pattern to different expressions
*)
(*val matchWordTree: fp_pat -> fp_word_val -> subst fp_word_val -> maybe (subst fp_word_val)*)
 val matchWordTree_defn = Defn.Hol_multi_defns `
 ((matchWordTree:fp_pat -> fp_word_val ->(num#fp_word_val)list ->((num#fp_word_val)list)option) (Word w1) (Fp_const w2) s=
     (if (w1 = w2) then SOME s else NONE))
    /\ ((matchWordTree:fp_pat -> fp_word_val ->(num#fp_word_val)list ->((num#fp_word_val)list)option) (Var n) v s=
       ((case substLookup s n of
        SOME v1 => if v1 = v then SOME s else NONE
      | NONE => SOME (substAdd n v s)
      )))
    /\ ((matchWordTree:fp_pat -> fp_word_val ->(num#fp_word_val)list ->((num#fp_word_val)list)option) (Unop op1 p) (Fp_uop op2 v) s=
       (if (op1 = op2)
      then matchWordTree p v s
      else NONE))
    /\ ((matchWordTree:fp_pat -> fp_word_val ->(num#fp_word_val)list ->((num#fp_word_val)list)option) (Binop b1 p1 p2) (Fp_bop b2 v1 v2) s=
       (if (b1 = b2)
      then
        (case matchWordTree p1 v1 s of
          NONE => NONE
        | SOME s1 => matchWordTree p2 v2 s1
        )
      else NONE))
    /\ ((matchWordTree:fp_pat -> fp_word_val ->(num#fp_word_val)list ->((num#fp_word_val)list)option) (Terop t1 p1 p2 p3) (Fp_top t2 v1 v2 v3) s=
       (if (t1 = t2)
      then
        (case matchWordTree p1 v1 s of
          NONE => NONE
        | SOME s1 =>
          (case matchWordTree p2 v2 s1 of
            NONE => NONE
          | SOME s2 => matchWordTree p3 v3 s2
          )
        )
      else NONE))
    /\ ((matchWordTree:fp_pat -> fp_word_val ->(num#fp_word_val)list ->((num#fp_word_val)list)option) (Optimise fp_opt1 p) (Fp_wopt fp_opt2 v) s=
       (if fp_opt1 = fp_opt2 then matchWordTree p v s else NONE))
    /\ ((matchWordTree:fp_pat -> fp_word_val ->(num#fp_word_val)list ->((num#fp_word_val)list)option) _ _ s=  NONE)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) matchWordTree_defn;

(*val matchBoolTree: fp_pat -> fp_bool_val -> subst fp_word_val -> maybe (subst fp_word_val)*)
 val matchBoolTree_defn = Defn.Hol_multi_defns `
 ((matchBoolTree:fp_pat -> fp_bool_val ->(num#fp_word_val)list ->((num#fp_word_val)list)option) (Optimise fp_opt1 p) (Fp_bopt fp_opt2 v) s=
       (if fp_opt1 = fp_opt2 then (matchBoolTree p v s) else NONE))
    (* and matchBoolTree (Pred pred1 p) (Fp_pred pred2 v) s =
      if (pred1 = pred2) then matchWordTree p v s else Nothing *)
    /\ ((matchBoolTree:fp_pat -> fp_bool_val ->(num#fp_word_val)list ->((fp_word_val)subst)option) (Cmp cmp1 p1 p2) (Fp_cmp cmp2 v1 v2) s=
       (if (cmp1 = cmp2)
      then
        (case matchWordTree p1 v1 s of
          NONE => NONE
        | SOME s1 => matchWordTree p2 v2 s1
        )
      else NONE))
    /\ ((matchBoolTree:fp_pat -> fp_bool_val ->(num#fp_word_val)list ->((num#fp_word_val)list)option) _ _ _=  NONE)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) matchBoolTree_defn;

(* Instantiate a given fp_pattern with a substitution into a value tree *)
(*val instWordTree: fp_pat -> subst fp_word_val -> maybe fp_word_val*)
 val instWordTree_defn = Defn.Hol_multi_defns `
 ((instWordTree:fp_pat ->(num#fp_word_val)list ->(fp_word_val)option) (Word w) s=  (SOME (Fp_const w)))
    /\ ((instWordTree:fp_pat ->(num#fp_word_val)list ->(fp_word_val)option) (Var n) s=  (substLookup s n))
    /\ ((instWordTree:fp_pat ->(num#fp_word_val)list ->(fp_word_val)option) (Unop u p) s=
       ((case instWordTree p s of
        NONE => NONE
      | SOME v => SOME (Fp_uop u v)
      )))
    /\ ((instWordTree:fp_pat ->(num#fp_word_val)list ->(fp_word_val)option) (Binop op p1 p2) s=
       ((case (instWordTree p1 s, instWordTree p2 s) of
        (SOME v1, SOME v2) => SOME (Fp_bop op v1 v2)
      | (_, _) => NONE
      )))
    /\ ((instWordTree:fp_pat ->(num#fp_word_val)list ->(fp_word_val)option) (Terop op p1 p2 p3) s=
       ((case (instWordTree p1 s, instWordTree p2 s , instWordTree p3 s) of
        (SOME v1, SOME v2, SOME v3) => SOME (Fp_top op v1 v2 v3)
      | (_, _, _) => NONE
      )))
    /\ ((instWordTree:fp_pat ->(num#fp_word_val)list ->(fp_word_val)option) (Optimise fp_opt p) s=
       ((case instWordTree p s of
        NONE => NONE
      | SOME v => SOME (Fp_wopt fp_opt v)
      )))
    /\ ((instWordTree:fp_pat ->(num#fp_word_val)list ->(fp_word_val)option) _ _=  NONE)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) instWordTree_defn;

(*val instBoolTree: fp_pat -> subst fp_word_val -> maybe fp_bool_val*)
 val instBoolTree_defn = Defn.Hol_multi_defns `
 ((instBoolTree:fp_pat ->(num#fp_word_val)list ->(fp_bool_val)option) (Optimise fp_opt p) s=
       ((case instBoolTree p s of
        NONE => NONE
      | SOME v => SOME (Fp_bopt fp_opt v)
      )))
    (* and instBoolTree (Pred pr p1) s =
      match instWordTree p1 s with
      | Nothing -> Nothing
      | Just v -> Just (Fp_pred pr v)
      end *)
    /\ ((instBoolTree:fp_pat ->(num#fp_word_val)list ->(fp_bool_val)option) (Cmp cmp p1 p2) s=
       ((case (instWordTree p1 s, instWordTree p2 s) of
        (SOME v1, SOME v2) => SOME (Fp_cmp cmp v1 v2)
      | (_, _) => NONE
      )))
    /\ ((instBoolTree:fp_pat ->(num#fp_word_val)list ->(fp_bool_val)option) _ _=  NONE)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) instBoolTree_defn;

(* Define a floating-point rewrite as a pair of a source and target fp_pattern *)
val _ = type_abbrev( "fp_rw" , ``: (fp_pat # fp_pat)``);

(** Rewriting on value trees is done in the semantics by picking a fp_path
  that walks down the value tree structure and then applies the rewrite in place
  if it matches **)

(* Datatype for fp_paths into a value tree. Here is the leaf node meaning that the
  rewrite should be applied *)
val _ = Hol_datatype `
 fp_path =   Left of fp_path | Right of fp_path | Center of fp_path | Here`;


(*val maybe_map: forall 'v1 'v2. ('v1 -> 'v2) -> maybe 'v1 -> maybe 'v2*)
 val _ = Define `
 ((maybe_map:('v1 -> 'v2) -> 'v1 option -> 'v2 option) f NONE=  NONE)
    /\ ((maybe_map:('v1 -> 'v2) -> 'v1 option -> 'v2 option) f (SOME res)=  (SOME (f res)))`;


(* Function rwFp_pathValTree b rw p v recurses through value tree v using fp_path p
  until p = Here or no further recursion is possible because of a mismatch.
  In case of a mismatch the function simply returns Nothing. *)
(*val rwFp_pathWordTree: fp_rw -> fp_path -> fp_word_val -> maybe fp_word_val*)
 val rwFp_pathWordTree_defn = Defn.Hol_multi_defns `
 ((rwFp_pathWordTree:fp_pat#fp_pat -> fp_path -> fp_word_val ->(fp_word_val)option) rw Here v=
       (let (lhs, rhs) = rw in
      (case matchWordTree lhs v [] of
          NONE => NONE
        | SOME s => instWordTree rhs s
      )))
    /\ ((rwFp_pathWordTree:fp_pat#fp_pat -> fp_path -> fp_word_val ->(fp_word_val)option) rw (Left p) (Fp_bop op v1 v2)=
       (maybe_map (\ v1 .  Fp_bop op v1 v2) (rwFp_pathWordTree rw p v1)))
    /\ ((rwFp_pathWordTree:fp_pat#fp_pat -> fp_path -> fp_word_val ->(fp_word_val)option) rw (Right p) (Fp_bop op v1 v2)=
       (maybe_map (\ v2 .  Fp_bop op v1 v2) (rwFp_pathWordTree rw p v2)))
    /\ ((rwFp_pathWordTree:fp_pat#fp_pat -> fp_path -> fp_word_val ->(fp_word_val)option) rw (Center p) (Fp_uop op v1)=
       (maybe_map (\ v .  Fp_uop op v) (rwFp_pathWordTree rw p v1)))
    /\ ((rwFp_pathWordTree:fp_pat#fp_pat -> fp_path -> fp_word_val ->(fp_word_val)option) rw (Left p) (Fp_top op v1 v2 v3)=
       (maybe_map (\ v1 .  Fp_top op v1 v2 v3) (rwFp_pathWordTree rw p v1)))
    /\ ((rwFp_pathWordTree:fp_pat#fp_pat -> fp_path -> fp_word_val ->(fp_word_val)option) rw (Center p) (Fp_top op v1 v2 v3)=
       (maybe_map (\ v2 .  Fp_top op v1 v2 v3) (rwFp_pathWordTree rw p v2)))
    /\ ((rwFp_pathWordTree:fp_pat#fp_pat -> fp_path -> fp_word_val ->(fp_word_val)option) rw (Right p) (Fp_top op v1 v2 v3)=
       (maybe_map (\ v3 .  Fp_top op v1 v2 v3) (rwFp_pathWordTree rw p v3)))
    /\ ((rwFp_pathWordTree:fp_pat#fp_pat -> fp_path -> fp_word_val ->(fp_word_val)option) rw (Center p) (Fp_wopt fp_opt v)=
       (maybe_map (\ v .  Fp_wopt fp_opt v) (rwFp_pathWordTree rw p v)))
    /\ ((rwFp_pathWordTree:fp_pat#fp_pat -> fp_path -> fp_word_val ->(fp_word_val)option) _ _ _=  NONE)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) rwFp_pathWordTree_defn;

(*val rwFp_pathBoolTree: fp_rw -> fp_path -> fp_bool_val -> maybe fp_bool_val*)
 val rwFp_pathBoolTree_defn = Defn.Hol_multi_defns `
 ((rwFp_pathBoolTree:fp_pat#fp_pat -> fp_path -> fp_bool_val ->(fp_bool_val)option) rw Here v=
       (let (lhs, rhs) = rw in
      (case matchBoolTree lhs v [] of
          NONE => NONE
        | SOME s => instBoolTree rhs s
      )))
    /\ ((rwFp_pathBoolTree:fp_pat#fp_pat -> fp_path -> fp_bool_val ->(fp_bool_val)option) rw (Center p) (Fp_bopt fp_opt v)=
       (maybe_map (\ v .  Fp_bopt fp_opt v) (rwFp_pathBoolTree rw p v)))
    (* and rwFp_pathBoolTree rw (Center p) (Fp_pred pr v) =
      maybe_map (fun v -> Fp_pred pr v) (rwFp_pathWordTree rw p v) *)
    /\ ((rwFp_pathBoolTree:fp_pat#fp_pat -> fp_path -> fp_bool_val ->(fp_bool_val)option) rw (Left p) (Fp_cmp cmp v1 v2)=
       (maybe_map (\ v1 .  Fp_cmp cmp v1 v2) (rwFp_pathWordTree rw p v1)))
    /\ ((rwFp_pathBoolTree:fp_pat#fp_pat -> fp_path -> fp_bool_val ->(fp_bool_val)option) rw (Right p) (Fp_cmp cmp v1 v2)=
       (maybe_map (\ v2 .  Fp_cmp cmp v1 v2) (rwFp_pathWordTree rw p v2)))
    /\ ((rwFp_pathBoolTree:fp_pat#fp_pat -> fp_path -> fp_bool_val ->(fp_bool_val)option) _ _ _=  NONE)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) rwFp_pathBoolTree_defn;

(* Datatype holding a single rewrite application in the form of a fp_path into the
  value tree and a number giving the index of the rewrite to be used *)
val _ = Hol_datatype `
 rewrite_app =   RewriteApp of fp_path => num`;
 (* which rewrite rule *)

(*val nth: forall 'v. list 'v -> nat -> maybe 'v*)
 val nth_defn = Defn.Hol_multi_defns `
 ((nth:'v list -> num -> 'v option) [] n=  NONE)
    /\ ((nth:'v list -> num -> 'v option) (x::xs) n=
       (if (n =( 0 : num)) then NONE
      else if (n =( 1 : num)) then SOME x
      else nth xs (n -( 1 : num))))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) nth_defn;

(* rwAllValTree rwApps canOpt rws v applies all the rewrite_app's in rwApps to
    value tree v using rwFp_pathValTree *)
(*val rwAllWordTree: list rewrite_app -> list fp_rw -> fp_word_val -> maybe fp_word_val*)
 val rwAllWordTree_defn = Defn.Hol_multi_defns `
 ((rwAllWordTree:(rewrite_app)list ->(fp_pat#fp_pat)list -> fp_word_val ->(fp_word_val)option) [] rws v=  (SOME v))
    /\ ((rwAllWordTree:(rewrite_app)list ->(fp_pat#fp_pat)list -> fp_word_val ->(fp_word_val)option) ((RewriteApp p n)::rs) rws v=
       ((case nth rws n of
        NONE => NONE
      | SOME rw =>
        (case rwFp_pathWordTree rw p v of
          NONE => NONE
        | SOME vNew => rwAllWordTree rs rws vNew
        )
      )))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) rwAllWordTree_defn;

(*val rwAllBoolTree: list rewrite_app -> list fp_rw -> fp_bool_val -> maybe fp_bool_val*)
 val rwAllBoolTree_defn = Defn.Hol_multi_defns `
 ((rwAllBoolTree:(rewrite_app)list ->(fp_pat#fp_pat)list -> fp_bool_val ->(fp_bool_val)option) [] rws v=  (SOME v))
    /\ ((rwAllBoolTree:(rewrite_app)list ->(fp_pat#fp_pat)list -> fp_bool_val ->(fp_bool_val)option) ((RewriteApp p n)::rs) rws v=
       ((case nth rws n of
        NONE => NONE
      | SOME rw =>
        (case rwFp_pathBoolTree rw p v of
          NONE => NONE
        | SOME vNew => rwAllBoolTree rs rws vNew
        )
      )))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) rwAllBoolTree_defn;

(*val no_fp_opts : nat -> list rewrite_app*)
val _ = Define `
 ((no_fp_opts:num ->(rewrite_app)list) (n:num)=  ([]))`;
val _ = export_theory()

