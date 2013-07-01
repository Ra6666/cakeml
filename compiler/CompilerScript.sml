(*Generated by Lem from compiler.lem.*)
open bossLib Theory Parse res_quanTheory
open fixedPointTheory finite_mapTheory listTheory pairTheory pred_setTheory
open integerTheory set_relationTheory sortingTheory stringTheory wordsTheory

val _ = numLib.prefer_num();



open ToBytecodeTheory ToIntLangTheory IntLangTheory CompilerPrimitivesTheory BytecodeTheory PrinterTheory CompilerLibTheory SemanticPrimitivesTheory AstTheory LibTheory

val _ = new_theory "Compiler"

(*open SemanticPrimitives*)
(*open Ast*)
(*open CompilerLib*)
(*open IntLang*)
(*open ToIntLang*)
(*open ToBytecode*)
(*open Bytecode*)

val _ = type_abbrev( "contab" , ``: (( conN id), num)fmap # (num # conN id) list # num``);
(*val cmap : contab -> Pmap.map (id conN) num*)
 val cmap_def = Define `
 (cmap (m,_,_) = m)`;


val _ = Hol_datatype `
 compiler_state =
  <| contab : contab
   ; renv : (string # num) list
   ; rmenv : (string, ( (string # num)list))fmap
   ; rsz : num
   ; rnext_label : num
   |>`;


(*val cpam : compiler_state -> list (num * id conN)*)
 val cpam_def = Define `
 (cpam s = ((case s.contab of (_,w,_) => w )))`;


val _ = Define `
 init_compiler_state =  
(<| contab := ( FUPDATE FEMPTY ( (Short ""), tuple_cn)
              ,[(tuple_cn,Short "")]
              ,3)
   ; renv := []
   ; rmenv := FEMPTY
   ; rsz := 0
   ; rnext_label := 0
   |>)`;


val _ = Define `
 (compile_Cexp rsz menv env nl Ce =  
(let (Ce,nl) = ( label_closures ( LENGTH env) nl Ce) in
  let cs = (<| out := []; next_label := nl |>) in
  let cs = ( emit cs [PushPtr (Addr 0); PushExc]) in
  let cs = ( compile_code_env menv cs Ce) in
  compile menv env TCNonTail (rsz +2) cs Ce))`;


 val number_constructors_defn = Hol_defn "number_constructors" `

(number_constructors _ [] ac = ac)
/\
(number_constructors mn ((c,_)::cs) ((m,w,n),ls) =  
(number_constructors mn cs (( FUPDATE  m ( (mk_id mn c), n), ((n,mk_id mn c) ::w), (n +1))
                            ,((CONCAT[id_to_string(mk_id mn c);" = <constructor>"]) ::ls))))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn number_constructors_defn;

 val compile_news_defn = Hol_defn "compile_news" `

(compile_news _ cs i [] = cs)
/\
(compile_news print cs i (v::vs) =  
(let cs = ( emit cs ( MAP Stack [Load 0; Load 0; El i])) in
  let cs = (if print then
      let cs = ( emit cs ( MAP PrintC (EXPLODE (CONCAT["val ";v;" = "])))) in
      emit cs [Stack(Load 0); Print]
    else cs) in
  let cs = ( emit cs [Stack (Store 1)]) in
  compile_news print cs (i +1) vs))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn compile_news_defn;

val _ = Define `
 (compile_fake_exp print rs vs e =  
(let m = (<| bvars := ( MAP FST rs.renv)
           ; mvars := ( (o_f) ( MAP FST) rs.rmenv)
           ; cnmap := ( cmap rs.contab)
           |>) in
  let Ce = ( exp_to_Cexp m (e (Con (Short "") ( MAP (\ v . Var (Short v)) vs)))) in
  let menv = ( (o_f) ( MAP SND) rs.rmenv) in
  let env = ( MAP ((o) CTDec SND) rs.renv) in
  let cs = ( compile_Cexp rs.rsz menv env rs.rnext_label Ce) in
  let cs = ( emit cs [PopExc; Stack (Pops 1)]) in
  let cs = ( compile_news print cs 0 vs) in
  let cs = ( emit cs [Stack Pop]) in
  (rs.contab
  , ZIP ( vs, ( GENLIST(\ i . rs.rsz +i)( LENGTH vs)))
  ,cs.next_label
  ,cs.out
  )))`;


 val dec_to_contab_def = Define `

(dec_to_contab mn ct (Dtype ts) = ( FOLDL (\ac p . 
  (case (ac ,p ) of ( ac , (_,_,cs) ) => number_constructors mn cs ac )) (ct,[]) ts))
/\
(dec_to_contab _ ct _ = (ct,[]))`;


 val decs_to_contab_defn = Hol_defn "decs_to_contab" `

(decs_to_contab mn ct [] = ct)
/\
(decs_to_contab mn ct (d::ds) = (decs_to_contab mn ( FST (dec_to_contab mn ct d)) ds))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn decs_to_contab_defn;

 val compile_dec_def = Define `

(compile_dec mn rs (Dtype ts) =  
(let (ct,ls) = ( dec_to_contab mn rs.contab (Dtype ts)) in
  (ct,[],rs.rnext_label
  ,(if (IS_NONE mn) then REVERSE( MAP PrintC (EXPLODE (CONCAT ( REVERSE ls)))) else []))))
/\
(compile_dec mn rs (Dletrec defs) =  
(let vs = ( MAP (\p . 
  (case (p ) of ( (n,_,_) ) => n )) defs) in
  compile_fake_exp (IS_NONE mn) rs vs (\ b . Letrec defs b)))
/\
(compile_dec mn rs (Dlet p e) =  
(let vs = ( pat_bindings p []) in
  compile_fake_exp (IS_NONE mn) rs vs (\ b . Mat e [(p,b)])))`;


 val compile_decs_defn = Hol_defn "compile_decs" `

(compile_decs _ [] ac = ac)
/\
(compile_decs mn (dec::decs) (rs,code) =  
(let (ct,env,nl,code') = ( compile_dec (SOME mn) rs dec) in
  compile_decs mn decs
    (( rs with<|
        contab := ct
      ; renv := env ++rs.renv
      ; rsz := rs.rsz + LENGTH env
      ; rnext_label := nl |>)
    ,(code' ++code))))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn compile_decs_defn;

 val compile_top_def = Define `

(compile_top rs (Tmod mn _ decs) =  
(let (mrs,code) = ( compile_decs mn decs (rs,[])) in
  let env = ( BUTLASTN ( LENGTH rs.renv) mrs.renv) in
  let str = ( CONCAT["structure ";mn;" = <structure>"]) in
  (( mrs with<|
      renv := rs.renv
    ; rmenv := FUPDATE  rs.rmenv ( mn, env) |>)
  ,( rs with<|
      contab := decs_to_contab (SOME mn) rs.contab decs
    ; rnext_label := mrs.rnext_label
    ; rmenv := FUPDATE  rs.rmenv ( mn, []) |>)
  ,(( REVERSE code) ++( MAP PrintC (EXPLODE str))))))
/\
(compile_top rs (Tdec dec) =  
(let (ct,env,nl,code) = ( compile_dec NONE rs dec) in
  (( rs with<|
      contab := ct
    ; renv := env ++rs.renv
    ; rsz := rs.rsz + LENGTH env
    ; rnext_label := nl |>)
  ,( rs with<| rnext_label := nl |>)
  , REVERSE code)))`;

val _ = export_theory()

