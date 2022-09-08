(*
  Compile the my program to machine code by evaluation of the compiler in
  the logic.
*)

open preamble myProgTheory compilationLib

val _ = new_theory"myCompile";

val wordfreq_compiled = save_thm("my_compiled",
  compile_x64 "my" my_prog_def);

val _ = export_theory();
