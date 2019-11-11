
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

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
  let formula = (neg (eqn (param (paramref "i")) (param (paramref "j")))) in
  prop name params formula


let n_coherence =
  let name = "n_coherence" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("n", [paramref "i"])])) (const _C)) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _C))))) in
  prop name params formula

let n_1 =
  let name = "n_1" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (arr [("n", [paramref "i"])])) (const _I))); (neg (eqn (var (arr [("n", [paramref "i"])])) (const _T)))]) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _C))))) in
  prop name params formula

let n_2 =
  let name = "n_2" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (arr [("n", [paramref "i"])])) (const _I))); (neg (eqn (var (arr [("n", [paramref "i"])])) (const _T)))]) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _E))))) in
  prop name params formula

let n_3 =
  let name = "n_3" in
  let params = [paramdef "i" "client"] in
  let formula = (imply (andList [(neg (eqn (var (arr [("n", [paramref "i"])])) (const _I))); (neg (eqn (var (arr [("n", [paramref "i"])])) (const _T)))]) (eqn (var (global "x")) (const (boolc false)))) in
  prop name params formula

let n_4 =
  let name = "n_4" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("n", [paramref "i"])])) (const _C)) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _C))))) in
  prop name params formula

let n_5 =
  let name = "n_5" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("n", [paramref "i"])])) (const _C)) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _E))))) in
  prop name params formula

let n_6 =
  let name = "n_6" in
  let params = [paramdef "i" "client"] in
  let formula = (imply (eqn (var (arr [("n", [paramref "i"])])) (const _C)) (eqn (var (global "x")) (const (boolc false)))) in
  prop name params formula

let n_7 =
  let name = "n_7" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("n", [paramref "i"])])) (const _E)) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _C))))) in
  prop name params formula

let n_8 =
  let name = "n_8" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("n", [paramref "i"])])) (const _E)) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _E))))) in
  prop name params formula

let n_9 =
  let name = "n_9" in
  let params = [paramdef "i" "client"] in
  let formula = (imply (eqn (var (arr [("n", [paramref "i"])])) (const _E)) (eqn (var (global "x")) (const (boolc false)))) in
  prop name params formula

let n_10 =
  let name = "n_10" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("n", [paramref "i"])])) (const _I)); (eqn (var (arr [("n", [paramref "j"])])) (const _I))]) (eqn (var (global "x")) (const (boolc true))))) in
  prop name params formula

let n_11 =
  let name = "n_11" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("n", [paramref "i"])])) (const _I)); (eqn (var (arr [("n", [paramref "j"])])) (const _T))]) (eqn (var (global "x")) (const (boolc true))))) in
  prop name params formula

let n_12 =
  let name = "n_12" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("n", [paramref "i"])])) (const _I)); (eqn (var (global "x")) (const (boolc false)))]) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _I))))) in
  prop name params formula

let n_13 =
  let name = "n_13" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("n", [paramref "i"])])) (const _I)); (eqn (var (global "x")) (const (boolc false)))]) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _T))))) in
  prop name params formula

let n_14 =
  let name = "n_14" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("n", [paramref "i"])])) (const _T)); (eqn (var (arr [("n", [paramref "j"])])) (const _I))]) (eqn (var (global "x")) (const (boolc true))))) in
  prop name params formula

let n_15 =
  let name = "n_15" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (arr [("n", [paramref "j"])])) (const _T))); (neg (eqn (var (arr [("n", [paramref "j"])])) (const _I)))]) (neg (eqn (var (arr [("n", [paramref "i"])])) (const _C))))) in
  prop name params formula

let n_16 =
  let name = "n_16" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (arr [("n", [paramref "j"])])) (const _T))); (neg (eqn (var (arr [("n", [paramref "j"])])) (const _I)))]) (neg (eqn (var (arr [("n", [paramref "i"])])) (const _E))))) in
  prop name params formula

let n_17 =
  let name = "n_17" in
  let params = [paramdef "j" "client"] in
  let formula = (imply (andList [(neg (eqn (var (arr [("n", [paramref "j"])])) (const _T))); (neg (eqn (var (arr [("n", [paramref "j"])])) (const _I)))]) (eqn (var (global "x")) (const (boolc false)))) in
  prop name params formula

let n_18 =
  let name = "n_18" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("n", [paramref "j"])])) (const _C)) (neg (eqn (var (arr [("n", [paramref "i"])])) (const _C))))) in
  prop name params formula

let n_19 =
  let name = "n_19" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("n", [paramref "j"])])) (const _C)) (neg (eqn (var (arr [("n", [paramref "i"])])) (const _E))))) in
  prop name params formula

let n_20 =
  let name = "n_20" in
  let params = [paramdef "j" "client"] in
  let formula = (imply (eqn (var (arr [("n", [paramref "j"])])) (const _C)) (eqn (var (global "x")) (const (boolc false)))) in
  prop name params formula

let n_21 =
  let name = "n_21" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("n", [paramref "j"])])) (const _E)) (neg (eqn (var (arr [("n", [paramref "i"])])) (const _C))))) in
  prop name params formula

let n_22 =
  let name = "n_22" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("n", [paramref "j"])])) (const _E)) (neg (eqn (var (arr [("n", [paramref "i"])])) (const _E))))) in
  prop name params formula

let n_23 =
  let name = "n_23" in
  let params = [paramdef "j" "client"] in
  let formula = (imply (eqn (var (arr [("n", [paramref "j"])])) (const _E)) (eqn (var (global "x")) (const (boolc false)))) in
  prop name params formula

let n_24 =
  let name = "n_24" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("n", [paramref "j"])])) (const _T)); (eqn (var (arr [("n", [paramref "i"])])) (const _T))]) (eqn (var (global "x")) (const (boolc true))))) in
  prop name params formula

let n_25 =
  let name = "n_25" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "x")) (const (boolc false))); (eqn (var (arr [("n", [paramref "i"])])) (const _T))]) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _I))))) in
  prop name params formula

let n_26 =
  let name = "n_26" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "x")) (const (boolc false))); (eqn (var (arr [("n", [paramref "i"])])) (const _T))]) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _T))))) in
  prop name params formula

let n_27 =
  let name = "n_27" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "x")) (const (boolc false))); (eqn (var (arr [("n", [paramref "j"])])) (const _I))]) (neg (eqn (var (arr [("n", [paramref "i"])])) (const _I))))) in
  prop name params formula

let n_28 =
  let name = "n_28" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "x")) (const (boolc false))); (eqn (var (arr [("n", [paramref "j"])])) (const _I))]) (neg (eqn (var (arr [("n", [paramref "i"])])) (const _T))))) in
  prop name params formula

let n_29 =
  let name = "n_29" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "x")) (const (boolc false))); (eqn (var (arr [("n", [paramref "j"])])) (const _T))]) (neg (eqn (var (arr [("n", [paramref "i"])])) (const _I))))) in
  prop name params formula

let n_30 =
  let name = "n_30" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "x")) (const (boolc false))); (eqn (var (arr [("n", [paramref "j"])])) (const _T))]) (neg (eqn (var (arr [("n", [paramref "i"])])) (const _T))))) in
  prop name params formula

let n_31 =
  let name = "n_31" in
  let params = [paramdef "i" "client"] in
  let formula = (imply (eqn (var (global "x")) (const (boolc true))) (neg (eqn (var (arr [("n", [paramref "i"])])) (const _C)))) in
  prop name params formula

let n_32 =
  let name = "n_32" in
  let params = [paramdef "i" "client"] in
  let formula = (imply (eqn (var (global "x")) (const (boolc true))) (neg (eqn (var (arr [("n", [paramref "i"])])) (const _E)))) in
  prop name params formula

let n_33 =
  let name = "n_33" in
  let params = [paramdef "j" "client"] in
  let formula = (imply (eqn (var (global "x")) (const (boolc true))) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _C)))) in
  prop name params formula

let n_34 =
  let name = "n_34" in
  let params = [paramdef "j" "client"] in
  let formula = (imply (eqn (var (global "x")) (const (boolc true))) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _E)))) in
  prop name params formula

let properties = [n_coherence; n_1; n_2; n_3; n_4; n_5; n_6; n_7; n_8; n_9; n_10; n_11; n_12; n_13; n_14; n_15; n_16; n_17; n_18; n_19; n_20; n_21; n_22; n_23; n_24; n_25; n_26; n_27; n_28; n_29; n_30; n_31; n_32; n_33; n_34]

let protocol = {
  name = "n_testMutualEx";
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
    host host ~types:types ~vardefs:vardefs in
  let ()=print_endline "---refine5\n" in  
  let c=CheckInv.checkProps types  properties in
  (*let b=List.map ~f:(fun f -> print_endline (ToStr.Smv.form_act  f)) ( extract   prot) in *)
()

