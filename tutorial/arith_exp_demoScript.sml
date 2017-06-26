(*
  A demonstration of interaction with HOL: a simple datatype for arithmetic
  expressions.
*)

(*
  A script file begins with a descriptive comment like the above, then opens
  the structures whose contents will be used. When working within the CakeML
  repository, it is usually sufficient to open preamble. Otherwise, one would
  typically open HolKernel boolLib bossLib and Parse (at least). CakeML's
  preamble wrapper includes all of those structures and more.
*)

open preamble

(*
  Create the logical theory in which we will work. Its name should match the name
  of this file, before the "Script.sml" suffix.
*)

val _ = new_theory "arith_exp_demo";

(*
  Define the arithmetic expression type.
  This shows how to define an inductive datatype in HOL.
*)

val _ = Datatype`
  exp = Num num | Add exp exp | Sub exp exp`;

(*
Try, for example
type_of ``Add``;
*)

(*
  Now we define some basic functions on this type.

  First, let us define the semantics of an expression.
  In other words, how to evaluate to a number.
  This shows how to define recursive functions in HOL.
*)

val eval_def = Define`
  eval (Num n) = n ∧
  eval (Add e1 e2) = eval e1 + eval e2 ∧
  eval (Sub e1 e2) = eval e1 - eval e2`;

(*
  We can "run" such definitions in the logic, producing a theorem as the result.
  To do this, we use the built-in function EVAL : term -> thm.
  For example, what is the semantics of "3 + (4 - 2)"?
*)

val example = EVAL``eval (Add (Num 3) (Sub (Num 4) (Num 2)))``;

(*
  We can also make this definition an "automatic" rewrite, so the simplifier
  expands it by default. This will be useful in proofs.
*)

val _ = export_rewrites["eval_def"];

(*
  Another function on expressions, this time it takes an expression and creates
  an addition of that expression with itself.
*)

val double_def = Define`
  double e = Add e e`;

(*
  Now let's prove a theorem about ``double``.
  We can prove that a doubled expression evaluates to two times the original
  expression.
*)

val double_thm = Q.store_thm("double_thm",
  `∀e. eval (double e) = 2 * eval e`,
  Induct \\ rw[double_def]);
(* a more detailed proof:
  Induct
  (* first subgoal solved by rewriting (eval_def is automatic; we add double_def manually) *)
  >- rw[double_def]
  (* second subgoal, for the Add case, also solved the same way *)
  >- rw[double_def]
  (* third subgoal also, hence the one line proof  above *)
  >- rw[double_def]
*)
(* a yet more detailed proof:
  Induct
  >- (
    gen_tac \\
    rewrite_tac[double_def] \\
    rewrite_tac[eval_def] \\
    (*
      DB.match [] ``(n:num) + n``
    *)
    rewrite_tac[TIMES2] )
  >- ...
*)

val _ = export_theory();
