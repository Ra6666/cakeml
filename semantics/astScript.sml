(*Generated by Lem from ast.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory lem_pervasives_extraTheory libTheory namespaceTheory fpValTreeTheory fpSemTheory;

val _ = numLib.prefer_num();



local open integerTheory wordsTheory stringTheory namespaceTheory locationTheory in end;
val _ = new_theory "ast"
val _ = set_grammar_ancestry ["integer", "words", "string", "namespace", "location"];

(*
  Definition of CakeML abstract syntax (AST).
*)

(*open import Pervasives_extra*)
(*open import Pervasives*)
(*open import Lib*)
(*open import Namespace*)
(*open import FpValTree*)
(*open import FpSem*)

(* Literal constants *)
val _ = Hol_datatype `
 lit =
    IntLit of int
  | Char of char
  | StrLit of string
  | Word8 of word8
  | Word64 of word64`;


(* Built-in binary operations *)
val _ = Hol_datatype `
 opn = Plus | Minus | Times | Divide | Modulo`;

val _ = Hol_datatype `
 opb = Lt | Gt | Leq | Geq`;

val _ = Hol_datatype `
 opw = Andw | Orw | Xor | Add | Sub`;

val _ = Hol_datatype `
 shift = Lsl | Lsr | Asr | Ror`;


(* Module names *)
val _ = type_abbrev( "modN" , ``: string``);

(* Variable names *)
val _ = type_abbrev( "varN" , ``: string``);

(* Constructor names (from datatype definitions) *)
val _ = type_abbrev( "conN" , ``: string``);

(* Type names *)
val _ = type_abbrev( "typeN" , ``: string``);

(* Type variable names *)
val _ = type_abbrev( "tvarN" , ``: string``);

val _ = Hol_datatype `
 word_size = W8 | W64`;


val _ = Hol_datatype `
 op =
  (* Operations on integers *)
    Opn of opn
  | Opb of opb
  (* Operations on words *)
  | Opw of word_size => opw
  | Shift of word_size => shift => num
  | Equality
  (* FP operations *)
  | FP_cmp of fp_cmp
  | FP_pred of fp_pred
  | FP_uop of fp_uop
  | FP_bop of fp_bop
  | FP_top of fp_top
  | FP_sc of sc
  (* Function application *)
  | Opapp
  (* Reference operations *)
  | Opassign
  | Opref
  | Opderef
  (* Word8Array operations *)
  | Aw8alloc
  | Aw8sub
  | Aw8length
  | Aw8update
  (* Word/integer conversions *)
  | WordFromInt of word_size
  | WordToInt of word_size
  (* string/bytearray conversions *)
  | CopyStrStr
  | CopyStrAw8
  | CopyAw8Str
  | CopyAw8Aw8
  (* Char operations *)
  | Ord
  | Chr
  | Chopb of opb
  (* String operations *)
  | Implode
  | Explode
  | Strsub
  | Strlen
  | Strcat
  (* Vector operations *)
  | VfromList
  | Vsub
  | Vlength
  (* Array operations *)
  | Aalloc
  | AallocEmpty
  | Asub
  | Alength
  | Aupdate
  (* List operations *)
  | ListAppend
  (* Configure the GC *)
  | ConfigGC
  (* Call a given foreign function *)
  | FFI of string`;


(* Logical operations *)
val _ = Hol_datatype `
 lop =
    And
  | Or`;


(* Types *)
val _ = Hol_datatype `
 ast_t =
  (* Type variables that the user writes down ('a, 'b, etc.) *)
    Atvar of tvarN
  (* Function type *)
  | Atfun of ast_t => ast_t
  (* Tuple type *)
  | Attup of ast_t list
  (* Type constructor applications.
    0-ary type applications represent unparameterised types (e.g., num or string) *)
  | Atapp of ast_t list => (modN, typeN) id`;


(* Patterns *)
val _ = Hol_datatype `
 pat =
    Pany
  | Pvar of varN
  | Plit of lit
  (* Constructor applications.
     A Nothing constructor indicates a tuple pattern. *)
  | Pcon of  ( (modN, conN)id)option => pat list
  | Pref of pat
  | Ptannot of pat => ast_t`;


(* Expressions *)
val _ = Hol_datatype `
 exp =
    Raise of exp
  | Handle of exp => (pat # exp) list
  | Lit of lit
  (* Constructor application.
     A Nothing constructor indicates a tuple pattern. *)
  | Con of  ( (modN, conN)id)option => exp list
  | Var of (modN, varN) id
  | Fun of varN => exp
  (* Application of a primitive operator to arguments.
     Includes function application. *)
  | App of op => exp list
  (* Logical operations (and, or) *)
  | Log of lop => exp => exp
  | If of exp => exp => exp
  (* Pattern matching *)
  | Mat of exp => (pat # exp) list
  (* A let expression
     A Nothing value for the binding indicates that this is a
     sequencing expression, that is: (e1; e2). *)
  | Let of  varN option => exp => exp
  (* Local definition of (potentially) mutually recursive
     functions.
     The first varN is the function's name, and the second varN
     is its parameter. *)
  | Letrec of (varN # varN # exp) list => exp
  | Tannot of exp => ast_t
  (* Location annotated expressions, not expected in source programs *)
  | Lannot of exp => locs`;


val _ = type_abbrev( "type_def" , ``: ( tvarN list # typeN # (conN # ast_t list) list) list``);

(* Declarations *)
val _ = Hol_datatype `
 dec =
  (* Top-level bindings
   * The pattern allows several names to be bound at once *)
    Dlet of locs => pat => exp
  (* Mutually recursive function definition *)
  | Dletrec of locs => (varN # varN # exp) list
  (* Type definition
     Defines several data types, each of which has several
     named variants, which can in turn have several arguments.
   *)
  | Dtype of locs => type_def
  (* Type abbreviations *)
  | Dtabbrev of locs => tvarN list => typeN => ast_t
  (* New exceptions *)
  | Dexn of locs => conN => ast_t list
  (* Module *)
  | Dmod of modN => dec list
  (* Local: local part, visible part *)
  | Dlocal of dec list => dec list`;


(*
(* Specifications
   For giving the signature of a module *)
type spec =
  | Sval of varN * ast_t
  | Stype of type_def
  | Stabbrev of list tvarN * typeN * ast_t
  | Stype_opq of list tvarN * typeN
  | Sexn of conN * list ast_t

type specs = list spec

*)

(* Accumulates the bindings of a pattern *)
(*val pat_bindings : pat -> list varN -> list varN*)
 val pat_bindings_defn = Defn.Hol_multi_defns `

((pat_bindings:pat ->(string)list ->(string)list) Pany already_bound=
   already_bound)
/\
((pat_bindings:pat ->(string)list ->(string)list) (Pvar n) already_bound=
   (n::already_bound))
/\
((pat_bindings:pat ->(string)list ->(string)list) (Plit l) already_bound=
   already_bound)
/\
((pat_bindings:pat ->(string)list ->(string)list) (Pcon _ ps) already_bound=
   (pats_bindings ps already_bound))
/\
((pat_bindings:pat ->(string)list ->(string)list) (Pref p) already_bound=
   (pat_bindings p already_bound))
/\
((pat_bindings:pat ->(string)list ->(string)list) (Ptannot p _) already_bound=
   (pat_bindings p already_bound))
/\
((pats_bindings:(pat)list ->(string)list ->(string)list) [] already_bound=
   already_bound)
/\
((pats_bindings:(pat)list ->(string)list ->(string)list) (p::ps) already_bound=
   (pats_bindings ps (pat_bindings p already_bound)))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) pat_bindings_defn;
val _ = export_theory()

