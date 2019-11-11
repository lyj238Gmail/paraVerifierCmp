
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
  enum "client" (int_consts [1;2]);
  enum "boolean" [_True; _False];
]


let vardefs = List.concat [
  [arrdef [("n", [paramdef "i0" "client"])] "state"];
  [arrdef [("x", [])] "boolean"]
]
	
let n_test1 =
  let name = "n_test1" in
  let params = [] in
  let formula = (imply (eqn (var (arr [("n", [paramfix "i" "client" (Intc 1)])])) (const _C)) 
  (neg (eqn (var (arr [("n", [paramfix "j" "client" (Intc 2)])])) (const _C)))) in
  prop name params formula
  
(*let n_test1 =
  let name = "n_test1" in
  let params = [] in
  let formula = (imply (eqn (var (arr [("n", [paramfix "i" "client" (Intc 1)])])) (const _C)) 
  (neg (eqn (var (arr [("n", [paramfix "j" "client" (Intc 2)])])) (const _C)))) in
  prop name params formula  

startServer   ?(smv_escape=(fun inv_str -> inv_str))
    ?(smv="") ?(smv_ord="")   ?(murphi="")  murphiName smvName
    muServer smvServer ~types ~vardefs
*)

let properties = [  n_test1]
	
let invStr="(n_a[1] = C -> n_a[2] = C)"	
let prog ()=	
	let localhost="192.168.1.37" in
  let a=CheckInv.startServer ~murphi:(In_channel.read_all "n_mutualEx.m")
    ~smv:(In_channel.read_all "mutualEx.smv") 	"n_mutualEx"  "mutualEx" 
    localhost localhost ~types:types ~vardefs:vardefs in
 (* let b=CheckInv.checkInvStr invStr in*)
  let c=CheckInv.checkProps types  properties in
  ()
  
let ()= run_with_cmdline  prog
    
