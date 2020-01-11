
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline
open CheckInv

let _I = strc "I"
let _T = strc "T"
let _C = strc "C"
let _E = strc "E"
let _True = boolc true
let _False = boolc false

let types = [
  enum "state" [_I; _T; _C; _E];
  enum "client" (int_consts [1; 2]);
  enum "boolean" [_True; _False];
]



let vardefs = List.concat [
  [arrdef [("n", [paramdef "i0" "client"])] "state"];
  [arrdef [("x", [])] "boolean"]
]

let init = (parallel [(forStatement (assign (arr [("n", [paramref "i"])]) (const _I)) [paramdef "i" "client"]); (assign (global "x") (const (boolc true)))])

let n_Try =
  let name = "n_Try" in
  let params = [paramdef "i" "client"] in
  let formula = (eqn (var (arr [("n", [paramref "i"])])) (const _I)) in
  let statement = (assign (arr [("n", [paramref "i"])]) (const _T)) in
  rule name params formula statement

let n_Crit =
  let name = "n_Crit" in
  let params = [paramdef "i" "client"] in
  let formula = (andList [(eqn (var (arr [("n", [paramref "i"])])) (const _T)); (eqn (var (global "x")) (const (boolc true)))]) in
  let statement = (parallel [(assign (arr [("n", [paramref "i"])]) (const _C)); (assign (global "x") (const (boolc false)))]) in
  rule name params formula statement

let n_Exit =
  let name = "n_Exit" in
  let params = [paramdef "i" "client"] in
  let formula = (eqn (var (arr [("n", [paramref "i"])])) (const _C)) in
  let statement = (assign (arr [("n", [paramref "i"])]) (const _E)) in
  rule name params formula statement

let n_Idle =
  let name = "n_Idle" in
  let params = [paramdef "i" "client"] in
  let formula = (eqn (var (arr [("n", [paramref "i"])])) (const _E)) in
  let statement = (parallel [(assign (arr [("n", [paramref "i"])]) (const _I)); (assign (global "x") (const (boolc true)))]) in
  rule name params formula statement

let rules = [n_Try; n_Crit; n_Exit; n_Idle]

let n_coherence =
  let name = "n_coherence" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("n", [paramref "i"])])) (const _C)) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _C))))) in
  prop name params formula

 

let propertiesRef=ref [] 

	let preProcessProp p =
	let Prop(name,params,formula)=p in
	let ()=print_endline name in
	let ()=print_endline ("this is"^(ToStr.Debug.form_act  (Loach.Trans.trans_formula types formula))) in
	match formula with 
	
	|Imply(a,b) ->
		if (List.length params) =2
		then [Prop(name,params,b)]
		else [p]
	|_ ->[p]

let properties = [n_coherence;]


let protocol = {
  name = "n_mutualEx";
  types;
  vardefs;
  init;
  rules;
  properties;
}

let print_pair p=
	let (r, absOptions)=p in
	let Rule(rn,pdsr,g,act)=r in
	let ()=print_endline rn in
	let printOptionPair (opt,abs_is)=
		match opt with
		|Some((r,usedInvs))->
			let ()=print_endline (ToMurphi.rule_act r) in
			let tmp=List.map ~f:(fun (n,inv)->print_endline n) usedInvs in
			()  
		|None->() in
	List.map ~f:printOptionPair absOptions
(*let properties	=List.concat (List.map ~f:(preProcessProp) properties)*)

let () =    
	(*let localhost="192.168.1.37" in
  let a=CheckInv.startServer ~murphi:(In_channel.read_all "n_mutualEx.m")
    ~smv:(In_channel.read_all "mutualEx.smv") "mutualEx"  "mutualEx" 
    localhost localhost  ~types:types ~vardefs:vardefs  protocol in  *)
	
  let _smt_context = Smt.set_context "mutualEx" (ToStr.Smt2.context_of ~insym_types:[] ~types ~vardefs) in
	let ()=PublicVariables.enumStrings := PublicVariables.extract types in 
	let ()=propertiesRef:=TestParser.loop "mutualExInvs1.invs" () in
	let properties=List.concat (List.map ~f:(preProcessProp) (!propertiesRef)) in
	let paraRef= paramfix "i" "client" (Intc(3)) in
	
  let ()=Cmp.initInvs properties types  paraRef in
  let ()=Cmp.setPrules rules in
	(*  let results=Cmp.cmpOnPrs properties ~types:types  paraRef  [1;2] ~unAbstractedReqs:[pair;pair1]   [ ]  rules in*)
	let results=Cmp.cmpOnPrs properties ~types:types  paraRef  [1;2] ~unAbstractedReqs:[] [] rules in
	let ()=print_endline "----------------------\n" in
	let ()=print_endline "abstract rules\n" in
	(*let a=List.map ~f:(fun r -> print_pair r) (fst results) in
  let ()=print_endline "used invs\n" in*)
	let b=List.map ~f:(fun f -> print_endline ((fst f)^(ToStr.Debug.form_act (Trans.trans_formula ~types:types (snd f))))) (snd results) in
	
	let absProt=Cmp.cmpAbsProtGen properties ~types:types  paraRef   [1;2] ~unAbstractedReqs:[] [] rules  protocol in
	let ()=print_endline "the abstract model\n" in
	let ()=print_endline (ToMurphi.protocol_act absProt) in
	()

