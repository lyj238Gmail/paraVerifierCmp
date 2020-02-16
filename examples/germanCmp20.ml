 

(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _I = strc "I"
let _S = strc "S"
let _E = strc "E"
let _Empty = strc "Empty"
let _ReqS = strc "ReqS"
let _ReqE = strc "ReqE"
let _Inv = strc "Inv"
let _InvAck = strc "InvAck"
let _GntS = strc "GntS"
let _GntE = strc "GntE"
let _True = boolc true
let _False = boolc false

let types = [
  enum "CACHE_STATE" [_I; _S; _E];
  enum "MSG_CMD" [_Empty; _ReqS; _ReqE; _Inv; _InvAck; _GntS; _GntE];
  enum "NODE" (int_consts [1; 2]);
  enum "DATA" (int_consts [1; ]);
  enum "boolean" [_True; _False];
]

let _CACHE = List.concat [
  [arrdef [("State", [])] "CACHE_STATE"];
  [arrdef [("Data", [])] "DATA"]
]

let _MSG = List.concat [
  [arrdef [("Cmd", [])] "MSG_CMD"];
  [arrdef [("Data", [])] "DATA"]
]

let vardefs = List.concat [
  record_def "Cache" [paramdef "i0" "NODE"] _CACHE;
  record_def "Chan1" [paramdef "i1" "NODE"] _MSG;
  record_def "Chan2" [paramdef "i2" "NODE"] _MSG;
  record_def "Chan3" [paramdef "i3" "NODE"] _MSG;
  [arrdef [("InvSet", [paramdef "i4" "NODE"])] "boolean"];
  [arrdef [("ShrSet", [paramdef "i5" "NODE"])] "boolean"];
  [arrdef [("ExGntd", [])] "boolean"];
  [arrdef [("CurCmd", [])] "MSG_CMD"];
  [arrdef [("CurPtr", [])] "NODE"];
  [arrdef [("MemData", [])] "DATA"];
  [arrdef [("AuxData", [])] "DATA"]
]


let init = (parallel [(forStatement (parallel [(assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (record [arr [("Chan3", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (record [arr [("Cache", [paramref "i"])]; global "State"]) (const _I)); (assign (arr [("InvSet", [paramref "i"])]) (const (boolc false))); (assign (arr [("ShrSet", [paramref "i"])]) (const (boolc false)))]) [paramdef "i" "NODE"]); (assign (global "ExGntd") (const (boolc false))); (assign (global "CurCmd") (const _Empty)); (assign (global "MemData") (param (paramfix "d" "DATA" (intc 1)))); (assign (global "AuxData") (param (paramfix "d" "DATA" (intc 1))))])

let n_RecvGntE1 =
  let name = "n_RecvGntE1" in
  let params = [paramdef "i" "NODE"] in
  let formula = (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) in
  let statement = (parallel [(assign (record [arr [("Cache", [paramref "i"])]; global "State"]) (const _E)); (assign (record [arr [("Cache", [paramref "i"])]; global "Data"]) (var (record [arr [("Chan2", [paramref "i"])]; global "Data"]))); (assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Empty))]) in
  rule name params formula statement

let n_RecvGntS2 =
  let name = "n_RecvGntS2" in
  let params = [paramdef "i" "NODE"] in
  let formula = (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) in
  let statement = (parallel [(assign (record [arr [("Cache", [paramref "i"])]; global "State"]) (const _S)); (assign (record [arr [("Cache", [paramref "i"])]; global "Data"]) (var (record [arr [("Chan2", [paramref "i"])]; global "Data"]))); (assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Empty))]) in
  rule name params formula statement

let n_SendGntE3 =
  let name = "n_SendGntE3" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (global "CurCmd")) (const _ReqE)); (eqn (var (global "CurPtr")) (param (paramref "i")))]); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))]); (eqn (var (global "ExGntd")) (const (boolc false)))]); (forallFormula [paramdef "j" "NODE"] (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _GntE)); (assign (record [arr [("Chan2", [paramref "i"])]; global "Data"]) (var (global "MemData"))); (assign (arr [("ShrSet", [paramref "i"])]) (const (boolc true))); (assign (global "ExGntd") (const (boolc true))); (assign (global "CurCmd") (const _Empty))]) in
  rule name params formula statement

let n_SendGntS4 =
  let name = "n_SendGntS4" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (global "CurPtr")) (param (paramref "i")))]); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))]); (eqn (var (global "ExGntd")) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _GntS)); (assign (record [arr [("Chan2", [paramref "i"])]; global "Data"]) (var (global "MemData"))); (assign (arr [("ShrSet", [paramref "i"])]) (const (boolc true))); (assign (global "CurCmd") (const _Empty))]) in
  rule name params formula statement

let n_RecvInvAck5 =
  let name = "n_RecvInvAck5" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "ExGntd")) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [arr [("Chan3", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (arr [("ShrSet", [paramref "i"])]) (const (boolc false))); (assign (global "ExGntd") (const (boolc false))); (assign (global "MemData") (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])))]) in
  rule name params formula statement

let n_RecvInvAck6 =
  let name = "n_RecvInvAck6" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (global "ExGntd")) (const (boolc true))))]) in
  let statement = (parallel [(assign (record [arr [("Chan3", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (arr [("ShrSet", [paramref "i"])]) (const (boolc false)))]) in
  rule name params formula statement

let n_SendInvAck7 =
  let name = "n_SendInvAck7" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))]); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (record [arr [("Chan3", [paramref "i"])]; global "Cmd"]) (const _InvAck)); (assign (record [arr [("Chan3", [paramref "i"])]; global "Data"]) (var (record [arr [("Cache", [paramref "i"])]; global "Data"]))); (assign (record [arr [("Cache", [paramref "i"])]; global "State"]) (const _I))]) in
  rule name params formula statement

let n_SendInvAck8 =
  let name = "n_SendInvAck8" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))]); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (record [arr [("Chan3", [paramref "i"])]; global "Cmd"]) (const _InvAck)); (assign (record [arr [("Cache", [paramref "i"])]; global "State"]) (const _I))]) in
  rule name params formula statement

let n_SendInv9 =
  let name = "n_SendInv9" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]); (eqn (var (global "CurCmd")) (const _ReqE))]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Inv)); (assign (arr [("InvSet", [paramref "i"])]) (const (boolc false)))]) in
  rule name params formula statement

let n_SendInv10 =
  let name = "n_SendInv10" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]); (eqn (var (global "CurCmd")) (const _ReqS))]); (eqn (var (global "ExGntd")) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Inv)); (assign (arr [("InvSet", [paramref "i"])]) (const (boolc false)))]) in
  rule name params formula statement

let n_RecvReqE11 =
  let name = "n_RecvReqE11" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"])) (const _ReqE))]) in
  let statement = (parallel [(assign (global "CurCmd") (const _ReqE)); (assign (global "CurPtr") (param (paramref "i"))); (assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _Empty)); (forStatement (assign (arr [("InvSet", [paramref "j"])]) (var (arr [("ShrSet", [paramref "j"])]))) [paramdef "j" "NODE"])]) in
  rule name params formula statement

let n_RecvReqS12 =
  let name = "n_RecvReqS12" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"])) (const _ReqS))]) in
  let statement = (parallel [(assign (global "CurCmd") (const _ReqS)); (assign (global "CurPtr") (param (paramref "i"))); (assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _Empty)); (forStatement (assign (arr [("InvSet", [paramref "j"])]) (var (arr [("ShrSet", [paramref "j"])]))) [paramdef "j" "NODE"])]) in
  rule name params formula statement

let n_SendReqE13 =
  let name = "n_SendReqE13" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"])) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) in
  let statement = (assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _ReqE)) in
  rule name params formula statement

let n_SendReqE14 =
  let name = "n_SendReqE14" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"])) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))]) in
  let statement = (assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _ReqE)) in
  rule name params formula statement

let n_SendReqS15 =
  let name = "n_SendReqS15" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"])) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) in
  let statement = (assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _ReqS)) in
  rule name params formula statement

let n_Store =
  let name = "n_Store" in
  let params = [paramdef "i" "NODE"; paramdef "d" "DATA"] in
  let formula = (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) in
  let statement = (parallel [(assign (record [arr [("Cache", [paramref "i"])]; global "Data"]) (param (paramref "d"))); 
	(assign (global "AuxData") (param (paramref "d")))]) in
  rule name params formula statement

let rules = [n_RecvGntE1; n_RecvGntS2; n_SendGntE3; n_SendGntS4; n_RecvInvAck5; n_RecvInvAck6; n_SendInvAck7; n_SendInvAck8; n_SendInv9; n_SendInv10; n_RecvReqE11; n_RecvReqS12; n_SendReqE13; n_SendReqE14; n_SendReqS15; n_Store]
    
let n_CntrlProp1 =
  let name = "n_CntrlProp1" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (global "CurCmd")) (const _Empty)))]); (eqn (var (global "ExGntd")) (const (boolc true)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_DataProp =
  let name = "n_DataProp" in
  let params = [] in
  let formula = (andList [(imply (eqn (var (global "ExGntd")) (const (boolc false))) (eqn (var (global "MemData")) (var (global "AuxData")))); (forallFormula [paramdef "i" "NODE"] (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))))]) in
  prop name params formula

let n_CntrlProp =
  let name = "n_CntrlProp" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (andList [(imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))); (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)) (orList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]))])) in
  prop name params formula
(*let properties = [n_CntrlProp]*)

let n_CntrlProp =
  let name = "n_CntrlProp" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (andList [(imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))); (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)) (orList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]))])) in
  prop name params formula
  let name = "n_1194" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_DataProp =
  let name = "n_DataProp" in
  let params = [] in
  let formula = (andList [(imply (eqn (var (global "ExGntd")) (const (boolc false))) (eqn (var (global "MemData")) (var (global "AuxData")))); (forallFormula [paramdef "i" "NODE"] (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))))]) in
  prop name params formula

let properties=[]
 
let protocol = {
  name = "n_german";
  types;
  vardefs;
  init;
  rules;
  properties;
}
let preProcessProp p =
	let Prop(name,params,formula)=p in
	let ()=print_endline name in
	match formula with 
	
	|Imply(a,b) ->
		if (List.length params) =2
		then [Prop(name,params,b)]
		else [p]
	|_ ->[p]
		

  
module PropCmp=Comparator.Make(struct
	type t=Loach.prop
	let sexp_of_t p =Loach.sexp_of_prop p
	let t_of_sexp s=Loach.prop_of_sexp s
  let compare x y= 
  	let Prop(pn,pdfs,x)=x in	
  	let Prop(pn',pdfs',y)=y in	
  String.compare (ToMurphi.form_act x) (ToMurphi.form_act y) 
    
end) 

let paramDef2ParamRef pdf=
	let Paramdef(strn,tn)=pdf in
	Paramref(strn)
	
let reviseProperty p=	
	let Prop(name,params,formula)=p in
 
	if (List.length params =2) then 
		let prefs=List.map ~f:paramDef2ParamRef params in
		let Some(p1)=List.nth prefs 0 in
		let Some(p2)=List.nth prefs 1 in
		let neqf=neg (eqn (param p1) (param p2)) in		
		let formula=Imply( neqf ,formula) in
		 Prop(name,params,formula)
	else p

let printInvs invs =
	let Some(invIndPairs)=List.zip invs (Utils.up_to (List.length invs)) in
	let props=List.map invIndPairs 
	~f:(fun (f,i) ->   
	(  (LoachGeneralize.concreteInv2ParamProp f i))) in
	let props=	Set.to_list (Set.of_list props ~comparator: PropCmp.comparator) in 
	let props=List.map ~f:reviseProperty props in
	let b=List.map ~f:(fun p -> print_endline (ToMurphi.prop_act p)) props in
	()

let printNameInvs (name,invs)=
	let ()=print_endline ("setOfPreOf"^name) in
	let b=printInvs invs in
	()

let propertiesRef=ref [] 
	
open LoachGeneralize
open CheckInv
let  () =  
  let tmp=Client.Smt2.host := UnixLabels.inet_addr_of_string  "192.168.20.15" in
	let tmp=Client.Murphi.host := UnixLabels.inet_addr_of_string  "192.168.20.15" in
  let _smt_context = Smt.set_context "german20" (ToStr.Smt2.context_of ~insym_types:[] ~types ~vardefs) in
  let ()=Generalize.zero_special:=true in
  let ()=PublicVariables.enumStrings := PublicVariables.extract types in 
  let ()=propertiesRef:=TestParser.loop "Inv_german.m" () in
   let properties=List.concat (List.map ~f:(preProcessProp) (!propertiesRef)) in
  let k=List.map ~f:(fun p -> print_endline (ToMurphi.prop_act p))  properties in
  	let paraRef= paramfix "i" "NODE" (Intc(3)) in	
	let dparaDef=paramdef "d" "DATA"  in
	let pair=("n_Store",[dparaDef]) in
  let ()=Cmp.initInvs properties types  paraRef in
  let ()=Cmp.setPrules rules in
  
	Cmp.cmpGenChk properties ~types:types  paraRef   [1;2] ~unAbstractedReqs:[pair] [] rules  protocol ["NODE";"DATA"] [global "CurPtr"]
