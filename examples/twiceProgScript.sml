(*
  print the command line arguments multiplied by 2.
*)

open preamble basis doubleProgTheory

val _ = new_theory "twiceProg";

val _ = translation_extends"basisProg";

val twice = process_topdecs
            `fun twice u =
            let val x =
                case  Int.fromString(List.nth(CommandLine.arguments ()) 0) of
                  None => 0
                  | Some i => i
        val dx = double(x)
        val ok = TextIO.print (toString dx)
      in TextIO.output1 TextIO.stdOut #"\n" end`;

val () = append_prog twice;

val st = get_ml_prog_state()
                              


Theorem twice_spec:
  [x_name; mlint$toString n] = cl ==> 
   app (p:'ffi ffi_proj) ^(fetch_v "twice" st) [Conv NONE []]
   (STDIO fs * COMMANDLINE cl)
   (POSTv uv. &UNIT_TYPE () uv *
      STDIO (add_stdout fs (toString(double n) ^ (strlit"\n"))) *
      COMMANDLINE cl)
Proof
  xcf "twice" st \\

  xlet_auto >- (xcon \\ xsimpl) \\
  
  xlet_auto >- (xsimpl \\ qexists_tac ‘STDIO fs’
                \\ qexists_tac ‘n’
                \\xsimpl)

  \\xlet_auto
  >- (xsimpl \\ rw [])\\
  xlet_auto >- xsimpl\\
  gvs[mlintTheory.fromString_toString,  mllistTheory.nth_def ] \\
  
               
                
  xlet‘ (POSTv iv. &INT n iv * STDIO  fs * COMMANDLINE [x_name; mlint$toString n])’
      
  >-(xmatch \\ xsimpl \\ simp[PULL_EXISTS, v_of_pat_def, v_of_pat_norest_def, AllCaseEqs()]\\
     gvs[OPTION_TYPE_def]\\
     rw[] >-(xvar \\ xsimpl) 
        xcases)
CONV_TAC validate_pat_conv
            
        
  xlet`POSTv uv.  &UNIT_TYPE () uv * COMMANDLINE cl *
        STDIO (add_stdout fs ((concatWith (strlit " ") (TL cl))))`
  >- (xapp >> xsimpl >> instantiate >> xsimpl >>
      (* TODO: why? *)
      qexists_tac`COMMANDLINE cl` >> xsimpl >>
      qexists_tac`fs` >> xsimpl) >>
  xapp_spec output1_stdout_spec >> xsimpl >>
  qmatch_goalsub_abbrev_tac`STDIO fs'` \\
  CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`fs'` \\
  unabbrev_all_tac \\
  xsimpl >> fs[] >>
  imp_res_tac STD_streams_stdout >>
  simp[str_def,implode_def] >>
  imp_res_tac add_stdo_o >> xsimpl
QED



Theorem twice_whole_prog_spec:
   whole_prog_spec ^(fetch_v "twice" st) cl fs NONE
    ((=) (add_stdout fs (concatWith (strlit" ") (TL cl) ^ (strlit"\n"))))
Proof
  rw[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe twice_spec))
  \\ xsimpl
QED

val (call_thm_twice, echo_prog_tm) = whole_prog_thm st "twice" twice_whole_prog_spec;
val twice_prog_def = Define`twice_prog = ^twice_prog_tm`;

val twice_semantics = save_thm("twice_semantics",
  call_thm_twice |> ONCE_REWRITE_RULE[GSYM twice_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]);

val _ = export_theory();
