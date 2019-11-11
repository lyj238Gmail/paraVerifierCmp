
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

let properties = [  n_coherence]
	

 
let printInvs invs =
	let Some(invIndPairs)=List.zip invs (Utils.up_to (List.length invs)) in
	List.map invIndPairs 
	~f:(fun (f,i) -> print_endline 
	(ToMurphi.prop_act (LoachGeneralize.concreteInv2ParamProp (Loach.Trans.invTrans_formula  f) i)))

let printNameInvs (name,invs)=
	let ()=print_endline name in
	let b=printInvs invs in
	()

let protocol = {
  name = "n_flashChou_without_nxt_home_126nLyj";
  types;
  vardefs;
  init;
  rules;
  properties;
}

open ExtractCharact
open CheckInv
let prot= Loach.Trans.act ~loach:protocol in  
	let host="192.168.1.37" in 
  let a=CheckInv.startServer ~murphi:(In_channel.read_all "n_mutualEx.m")
    ~smv:(In_channel.read_all "mutualEx.smv") "n_mutualEx"  "n_mutualEx" 
    host host ~types:types ~vardefs:vardefs protocol in
  let ()=print_endline "---refine5\n" in  
  let invs=( extract   prot) in
   let ()=print_endline (string_of_int (List.length invs)) in  
  (*let Some(invIndPairs)=List.zip invs (Utils.up_to (List.length invs)) in*)
  let b=printInvs invs in
  let c=extractSubFormsByRule prot in
  let d=List.map ~f:printNameInvs c in
  (*let b=List.map invIndPairs ~f:(fun (f,i) -> print_endline (ToMurphi.prop_act (LoachGeneralize.concreteInv2ParamProp (Loach.Trans.invTrans_formula  f) i)))  in *)
()
    
