 

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

let n_Store =
  let name = "n_Store" in
  let params = [paramdef "i" "NODE"; paramdef "d" "DATA"] in
  let formula = (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) in
  let statement = (parallel [(assign (record [arr [("Cache", [paramref "i"])]; global "Data"]) (param (paramref "d"))); (assign (global "AuxData") (param (paramref "d")))]) in
  rule name params formula statement

let n_SendReqS =
  let name = "n_SendReqS" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"])) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) in
  let statement = (assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _ReqS)) in
  rule name params formula statement

let n_SendReqE =
  let name = "n_SendReqE" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"])) (const _Empty)); (orList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))])]) in
  let statement = (assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _ReqE)) in
  rule name params formula statement

let n_RecvReqS =
  let name = "n_RecvReqS" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"])) (const _ReqS))]) in
  let statement = (parallel [(assign (global "CurCmd") (const _ReqS)); (assign (global "CurPtr") (param (paramref "i"))); (assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _Empty)); (forStatement (assign (arr [("InvSet", [paramref "j"])]) (var (arr [("ShrSet", [paramref "j"])]))) [paramdef "j" "NODE"])]) in
  rule name params formula statement

let n_RecvReqE =
  let name = "n_RecvReqE" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"])) (const _ReqE))]) in
  let statement = (parallel [(assign (global "CurCmd") (const _ReqE)); (assign (global "CurPtr") (param (paramref "i"))); (assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _Empty)); (forStatement (assign (arr [("InvSet", [paramref "j"])]) (var (arr [("ShrSet", [paramref "j"])]))) [paramdef "j" "NODE"])]) in
  rule name params formula statement

let n_SendInv =
  let name = "n_SendInv" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]); (orList [(eqn (var (global "CurCmd")) (const _ReqE)); (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (global "ExGntd")) (const (boolc true)))])])]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Inv)); (assign (arr [("InvSet", [paramref "i"])]) (const (boolc false)))]) in
  rule name params formula statement

let n_SendInvAck =
  let name = "n_SendInvAck" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (record [arr [("Chan3", [paramref "i"])]; global "Cmd"]) (const _InvAck)); (ifStatement (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (assign (record [arr [("Chan3", [paramref "i"])]; global "Data"]) (var (record [arr [("Cache", [paramref "i"])]; global "Data"])))); (assign (record [arr [("Cache", [paramref "i"])]; global "State"]) (const _I))]) in
  rule name params formula statement

let n_RecvInvAck =
  let name = "n_RecvInvAck" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (global "CurCmd")) (const _Empty)))]) in
  let statement = (parallel [(assign (record [arr [("Chan3", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (arr [("ShrSet", [paramref "i"])]) (const (boolc false))); (ifStatement (eqn (var (global "ExGntd")) (const (boolc true))) (parallel [(assign (global "ExGntd") (const (boolc false))); (assign (global "MemData") (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])))]))]) in
  rule name params formula statement

let n_SendGntS =
  let name = "n_SendGntS" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (global "CurPtr")) (param (paramref "i")))]); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))]); (eqn (var (global "ExGntd")) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _GntS)); (assign (record [arr [("Chan2", [paramref "i"])]; global "Data"]) (var (global "MemData"))); (assign (arr [("ShrSet", [paramref "i"])]) (const (boolc true))); (assign (global "CurCmd") (const _Empty))]) in
  rule name params formula statement

let n_SendGntE =
  let name = "n_SendGntE" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (global "CurCmd")) (const _ReqE)); (eqn (var (global "CurPtr")) (param (paramref "i")))]); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))]); (eqn (var (global "ExGntd")) (const (boolc false)))]); (forallFormula [paramdef "j" "NODE"] (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _GntE)); (assign (record [arr [("Chan2", [paramref "i"])]; global "Data"]) (var (global "MemData"))); (assign (arr [("ShrSet", [paramref "i"])]) (const (boolc true))); (assign (global "ExGntd") (const (boolc true))); (assign (global "CurCmd") (const _Empty))]) in
  rule name params formula statement

let n_RecvGntS =
  let name = "n_RecvGntS" in
  let params = [paramdef "i" "NODE"] in
  let formula = (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) in
  let statement = (parallel [(assign (record [arr [("Cache", [paramref "i"])]; global "State"]) (const _S)); (assign (record [arr [("Cache", [paramref "i"])]; global "Data"]) (var (record [arr [("Chan2", [paramref "i"])]; global "Data"]))); (assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Empty))]) in
  rule name params formula statement

let n_RecvGntE =
  let name = "n_RecvGntE" in
  let params = [paramdef "i" "NODE"] in
  let formula = (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) in
  let statement = (parallel [(assign (record [arr [("Cache", [paramref "i"])]; global "State"]) (const _E)); (assign (record [arr [("Cache", [paramref "i"])]; global "Data"]) (var (record [arr [("Chan2", [paramref "i"])]; global "Data"]))); (assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Empty))]) in
  rule name params formula statement

let rules = [n_Store; n_SendReqS; n_SendReqE; n_RecvReqS; n_RecvReqE; n_SendInv; n_SendInvAck; n_RecvInvAck; n_SendGntS; n_SendGntE; n_RecvGntS; n_RecvGntE]

let n_CntrlProp =
  let name = "n_CntrlProp" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula =   (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_DataProp =
  let name = "n_DataProp" in
  let params = [] in
  let formula = (andList [(imply (eqn (var (global "ExGntd")) (const (boolc false))) (eqn (var (global "MemData")) (var (global "AuxData")))); (forallFormula [paramdef "i" "NODE"] (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))))]) in
  prop name params formula
  
let n_RecvInvAck1 =
  let name = "n_RecvInvAck1" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(neg (eqn (var (global "CurCmd")) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]); (eqn (var (global "ExGntd")) (const (boolc true)))]) in
  let statement = (parallel [(assign (arr [("ShrSet", [paramref "i"])]) (const (boolc false))); (assign (global "ExGntd") (const (boolc false))); (assign (global "MemData") (var (record [arr [("Chan3", [paramref "i"])]; global "Data"]))); (assign (record [arr [("Chan3", [paramref "i"])]; global "Cmd"]) (const _Empty))]) in
  rule name params formula statement

let n_RecvInvAck2 =
  let name = "n_RecvInvAck2" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(neg (eqn (var (global "CurCmd")) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]); (eqn (var (global "ExGntd")) (const (boolc false)))]) in
  let statement = (parallel [(assign (arr [("ShrSet", [paramref "i"])]) (const (boolc false))); (assign (record [arr [("Chan3", [paramref "i"])]; global "Cmd"]) (const _Empty))]) in
  rule name params formula statement
  
    
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

let n_1 =
  let name = "n_1" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_2 =
  let name = "n_2" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_3 =
  let name = "n_3" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_4 =
  let name = "n_4" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_5 =
  let name = "n_5" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_6 =
  let name = "n_6" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_7 =
  let name = "n_7" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_8 =
  let name = "n_8" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_9 =
  let name = "n_9" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_10 =
  let name = "n_10" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_11 =
  let name = "n_11" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_12 =
  let name = "n_12" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_13 =
  let name = "n_13" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_14 =
  let name = "n_14" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_15 =
  let name = "n_15" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_16 =
  let name = "n_16" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_17 =
  let name = "n_17" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_18 =
  let name = "n_18" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_19 =
  let name = "n_19" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_20 =
  let name = "n_20" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_21 =
  let name = "n_21" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_22 =
  let name = "n_22" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_23 =
  let name = "n_23" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_24 =
  let name = "n_24" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_25 =
  let name = "n_25" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))) in
  prop name params formula

let n_26 =
  let name = "n_26" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_27 =
  let name = "n_27" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))) in
  prop name params formula

let n_28 =
  let name = "n_28" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))) in
  prop name params formula

let n_29 =
  let name = "n_29" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_30 =
  let name = "n_30" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_31 =
  let name = "n_31" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_32 =
  let name = "n_32" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_33 =
  let name = "n_33" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_34 =
  let name = "n_34" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_35 =
  let name = "n_35" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_36 =
  let name = "n_36" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_37 =
  let name = "n_37" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_38 =
  let name = "n_38" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_39 =
  let name = "n_39" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_40 =
  let name = "n_40" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_41 =
  let name = "n_41" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_42 =
  let name = "n_42" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_43 =
  let name = "n_43" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_44 =
  let name = "n_44" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_45 =
  let name = "n_45" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_46 =
  let name = "n_46" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_47 =
  let name = "n_47" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_48 =
  let name = "n_48" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_49 =
  let name = "n_49" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_50 =
  let name = "n_50" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_51 =
  let name = "n_51" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_52 =
  let name = "n_52" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_53 =
  let name = "n_53" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_54 =
  let name = "n_54" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_55 =
  let name = "n_55" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "CurCmd")) (const _ReqE)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_56 =
  let name = "n_56" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "CurCmd")) (const _ReqE)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_57 =
  let name = "n_57" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "CurCmd")) (const _ReqE)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_58 =
  let name = "n_58" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))) in
  prop name params formula

let n_59 =
  let name = "n_59" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_60 =
  let name = "n_60" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_61 =
  let name = "n_61" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_62 =
  let name = "n_62" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_63 =
  let name = "n_63" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_64 =
  let name = "n_64" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_65 =
  let name = "n_65" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_66 =
  let name = "n_66" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_67 =
  let name = "n_67" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))) in
  prop name params formula

let n_68 =
  let name = "n_68" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))) in
  prop name params formula

let n_69 =
  let name = "n_69" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_70 =
  let name = "n_70" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_71 =
  let name = "n_71" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_72 =
  let name = "n_72" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_73 =
  let name = "n_73" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_74 =
  let name = "n_74" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_75 =
  let name = "n_75" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_76 =
  let name = "n_76" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_77 =
  let name = "n_77" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_78 =
  let name = "n_78" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_79 =
  let name = "n_79" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_80 =
  let name = "n_80" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_81 =
  let name = "n_81" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_82 =
  let name = "n_82" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_83 =
  let name = "n_83" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_84 =
  let name = "n_84" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))) in
  prop name params formula

let n_85 =
  let name = "n_85" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_86 =
  let name = "n_86" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_87 =
  let name = "n_87" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_88 =
  let name = "n_88" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_89 =
  let name = "n_89" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_90 =
  let name = "n_90" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_91 =
  let name = "n_91" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_92 =
  let name = "n_92" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_93 =
  let name = "n_93" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_94 =
  let name = "n_94" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_95 =
  let name = "n_95" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_96 =
  let name = "n_96" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_97 =
  let name = "n_97" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_98 =
  let name = "n_98" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_99 =
  let name = "n_99" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_100 =
  let name = "n_100" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_101 =
  let name = "n_101" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_102 =
  let name = "n_102" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_103 =
  let name = "n_103" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_104 =
  let name = "n_104" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_105 =
  let name = "n_105" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_106 =
  let name = "n_106" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_107 =
  let name = "n_107" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_108 =
  let name = "n_108" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_109 =
  let name = "n_109" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_110 =
  let name = "n_110" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_111 =
  let name = "n_111" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_112 =
  let name = "n_112" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_113 =
  let name = "n_113" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_114 =
  let name = "n_114" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_115 =
  let name = "n_115" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_116 =
  let name = "n_116" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_117 =
  let name = "n_117" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_118 =
  let name = "n_118" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_119 =
  let name = "n_119" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_120 =
  let name = "n_120" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_121 =
  let name = "n_121" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_122 =
  let name = "n_122" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_123 =
  let name = "n_123" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_124 =
  let name = "n_124" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_125 =
  let name = "n_125" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_126 =
  let name = "n_126" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_127 =
  let name = "n_127" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_128 =
  let name = "n_128" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_129 =
  let name = "n_129" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_130 =
  let name = "n_130" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_131 =
  let name = "n_131" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_132 =
  let name = "n_132" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_133 =
  let name = "n_133" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_134 =
  let name = "n_134" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_135 =
  let name = "n_135" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_136 =
  let name = "n_136" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_137 =
  let name = "n_137" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_138 =
  let name = "n_138" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_139 =
  let name = "n_139" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_140 =
  let name = "n_140" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_141 =
  let name = "n_141" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_142 =
  let name = "n_142" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_143 =
  let name = "n_143" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_144 =
  let name = "n_144" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_145 =
  let name = "n_145" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_146 =
  let name = "n_146" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_147 =
  let name = "n_147" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))) in
  prop name params formula

let n_148 =
  let name = "n_148" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_149 =
  let name = "n_149" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_150 =
  let name = "n_150" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_151 =
  let name = "n_151" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_152 =
  let name = "n_152" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_153 =
  let name = "n_153" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_154 =
  let name = "n_154" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_155 =
  let name = "n_155" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_156 =
  let name = "n_156" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_157 =
  let name = "n_157" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_158 =
  let name = "n_158" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_159 =
  let name = "n_159" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_160 =
  let name = "n_160" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_161 =
  let name = "n_161" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_162 =
  let name = "n_162" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_163 =
  let name = "n_163" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_164 =
  let name = "n_164" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_165 =
  let name = "n_165" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_166 =
  let name = "n_166" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_167 =
  let name = "n_167" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_168 =
  let name = "n_168" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_169 =
  let name = "n_169" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_170 =
  let name = "n_170" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_171 =
  let name = "n_171" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_172 =
  let name = "n_172" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_173 =
  let name = "n_173" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_174 =
  let name = "n_174" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE))) in
  prop name params formula

let n_175 =
  let name = "n_175" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))) in
  prop name params formula

let n_176 =
  let name = "n_176" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_177 =
  let name = "n_177" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_178 =
  let name = "n_178" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_179 =
  let name = "n_179" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_180 =
  let name = "n_180" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_181 =
  let name = "n_181" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_182 =
  let name = "n_182" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_183 =
  let name = "n_183" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_184 =
  let name = "n_184" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_185 =
  let name = "n_185" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_186 =
  let name = "n_186" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_187 =
  let name = "n_187" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_188 =
  let name = "n_188" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_189 =
  let name = "n_189" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_190 =
  let name = "n_190" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_191 =
  let name = "n_191" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_192 =
  let name = "n_192" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_193 =
  let name = "n_193" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_194 =
  let name = "n_194" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_195 =
  let name = "n_195" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_196 =
  let name = "n_196" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_197 =
  let name = "n_197" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_198 =
  let name = "n_198" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_199 =
  let name = "n_199" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_200 =
  let name = "n_200" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_201 =
  let name = "n_201" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_202 =
  let name = "n_202" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_203 =
  let name = "n_203" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_204 =
  let name = "n_204" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_205 =
  let name = "n_205" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_206 =
  let name = "n_206" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_207 =
  let name = "n_207" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_208 =
  let name = "n_208" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_209 =
  let name = "n_209" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_210 =
  let name = "n_210" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_211 =
  let name = "n_211" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_212 =
  let name = "n_212" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_213 =
  let name = "n_213" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_214 =
  let name = "n_214" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_215 =
  let name = "n_215" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_216 =
  let name = "n_216" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_217 =
  let name = "n_217" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_218 =
  let name = "n_218" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_219 =
  let name = "n_219" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_220 =
  let name = "n_220" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_221 =
  let name = "n_221" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_222 =
  let name = "n_222" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_223 =
  let name = "n_223" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_224 =
  let name = "n_224" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_225 =
  let name = "n_225" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_226 =
  let name = "n_226" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_227 =
  let name = "n_227" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_228 =
  let name = "n_228" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))) in
  prop name params formula

let n_229 =
  let name = "n_229" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_230 =
  let name = "n_230" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_231 =
  let name = "n_231" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_232 =
  let name = "n_232" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_233 =
  let name = "n_233" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_234 =
  let name = "n_234" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))) in
  prop name params formula

let n_235 =
  let name = "n_235" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))) in
  prop name params formula

let n_236 =
  let name = "n_236" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_237 =
  let name = "n_237" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_238 =
  let name = "n_238" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_239 =
  let name = "n_239" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_240 =
  let name = "n_240" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_241 =
  let name = "n_241" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_242 =
  let name = "n_242" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_243 =
  let name = "n_243" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_244 =
  let name = "n_244" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_245 =
  let name = "n_245" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_246 =
  let name = "n_246" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_247 =
  let name = "n_247" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_248 =
  let name = "n_248" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_249 =
  let name = "n_249" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_250 =
  let name = "n_250" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_251 =
  let name = "n_251" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_252 =
  let name = "n_252" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_253 =
  let name = "n_253" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_254 =
  let name = "n_254" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_255 =
  let name = "n_255" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_256 =
  let name = "n_256" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_257 =
  let name = "n_257" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE))) in
  prop name params formula

let n_258 =
  let name = "n_258" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_259 =
  let name = "n_259" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_260 =
  let name = "n_260" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_261 =
  let name = "n_261" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_262 =
  let name = "n_262" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_263 =
  let name = "n_263" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_264 =
  let name = "n_264" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_265 =
  let name = "n_265" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_266 =
  let name = "n_266" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_267 =
  let name = "n_267" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_268 =
  let name = "n_268" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_269 =
  let name = "n_269" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_270 =
  let name = "n_270" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_271 =
  let name = "n_271" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_272 =
  let name = "n_272" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_273 =
  let name = "n_273" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_274 =
  let name = "n_274" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_275 =
  let name = "n_275" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_276 =
  let name = "n_276" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_277 =
  let name = "n_277" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_278 =
  let name = "n_278" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_279 =
  let name = "n_279" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_280 =
  let name = "n_280" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_281 =
  let name = "n_281" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_282 =
  let name = "n_282" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_283 =
  let name = "n_283" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_284 =
  let name = "n_284" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_285 =
  let name = "n_285" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_286 =
  let name = "n_286" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_287 =
  let name = "n_287" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_288 =
  let name = "n_288" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_289 =
  let name = "n_289" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_290 =
  let name = "n_290" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))) in
  prop name params formula

let n_291 =
  let name = "n_291" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_292 =
  let name = "n_292" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_293 =
  let name = "n_293" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_294 =
  let name = "n_294" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_295 =
  let name = "n_295" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_296 =
  let name = "n_296" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_297 =
  let name = "n_297" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_298 =
  let name = "n_298" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_299 =
  let name = "n_299" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_300 =
  let name = "n_300" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_301 =
  let name = "n_301" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_302 =
  let name = "n_302" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_303 =
  let name = "n_303" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_304 =
  let name = "n_304" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_305 =
  let name = "n_305" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_306 =
  let name = "n_306" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_307 =
  let name = "n_307" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_308 =
  let name = "n_308" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_309 =
  let name = "n_309" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_310 =
  let name = "n_310" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_311 =
  let name = "n_311" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_312 =
  let name = "n_312" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_313 =
  let name = "n_313" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_314 =
  let name = "n_314" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_315 =
  let name = "n_315" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_316 =
  let name = "n_316" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_317 =
  let name = "n_317" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_318 =
  let name = "n_318" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_319 =
  let name = "n_319" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_320 =
  let name = "n_320" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_321 =
  let name = "n_321" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_322 =
  let name = "n_322" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_323 =
  let name = "n_323" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_324 =
  let name = "n_324" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_325 =
  let name = "n_325" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_326 =
  let name = "n_326" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_327 =
  let name = "n_327" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_328 =
  let name = "n_328" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_329 =
  let name = "n_329" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_330 =
  let name = "n_330" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_331 =
  let name = "n_331" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_332 =
  let name = "n_332" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_333 =
  let name = "n_333" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_334 =
  let name = "n_334" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_335 =
  let name = "n_335" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_336 =
  let name = "n_336" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_337 =
  let name = "n_337" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_338 =
  let name = "n_338" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_339 =
  let name = "n_339" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_340 =
  let name = "n_340" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_341 =
  let name = "n_341" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_342 =
  let name = "n_342" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_343 =
  let name = "n_343" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_344 =
  let name = "n_344" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_345 =
  let name = "n_345" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_346 =
  let name = "n_346" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_347 =
  let name = "n_347" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_348 =
  let name = "n_348" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_349 =
  let name = "n_349" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_350 =
  let name = "n_350" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_351 =
  let name = "n_351" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_352 =
  let name = "n_352" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_353 =
  let name = "n_353" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_354 =
  let name = "n_354" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_355 =
  let name = "n_355" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_356 =
  let name = "n_356" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_357 =
  let name = "n_357" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_358 =
  let name = "n_358" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_359 =
  let name = "n_359" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_360 =
  let name = "n_360" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_361 =
  let name = "n_361" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_362 =
  let name = "n_362" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_363 =
  let name = "n_363" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_364 =
  let name = "n_364" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_365 =
  let name = "n_365" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_366 =
  let name = "n_366" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_367 =
  let name = "n_367" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_368 =
  let name = "n_368" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_369 =
  let name = "n_369" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_370 =
  let name = "n_370" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_371 =
  let name = "n_371" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_372 =
  let name = "n_372" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_373 =
  let name = "n_373" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_374 =
  let name = "n_374" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_375 =
  let name = "n_375" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_376 =
  let name = "n_376" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))) in
  prop name params formula

let n_377 =
  let name = "n_377" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_378 =
  let name = "n_378" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_379 =
  let name = "n_379" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_380 =
  let name = "n_380" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_381 =
  let name = "n_381" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_382 =
  let name = "n_382" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_383 =
  let name = "n_383" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_384 =
  let name = "n_384" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_385 =
  let name = "n_385" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_386 =
  let name = "n_386" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_387 =
  let name = "n_387" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_388 =
  let name = "n_388" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_389 =
  let name = "n_389" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_390 =
  let name = "n_390" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_391 =
  let name = "n_391" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_392 =
  let name = "n_392" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_393 =
  let name = "n_393" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_394 =
  let name = "n_394" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) in
  prop name params formula

let n_395 =
  let name = "n_395" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_396 =
  let name = "n_396" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_397 =
  let name = "n_397" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_398 =
  let name = "n_398" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_399 =
  let name = "n_399" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_400 =
  let name = "n_400" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_401 =
  let name = "n_401" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_402 =
  let name = "n_402" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_403 =
  let name = "n_403" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_404 =
  let name = "n_404" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_405 =
  let name = "n_405" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_406 =
  let name = "n_406" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_407 =
  let name = "n_407" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_408 =
  let name = "n_408" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_409 =
  let name = "n_409" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_410 =
  let name = "n_410" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_411 =
  let name = "n_411" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_412 =
  let name = "n_412" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_413 =
  let name = "n_413" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_414 =
  let name = "n_414" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_415 =
  let name = "n_415" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (global "CurCmd")) (const _Empty))) in
  prop name params formula

let n_416 =
  let name = "n_416" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_417 =
  let name = "n_417" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_418 =
  let name = "n_418" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) in
  prop name params formula

let n_419 =
  let name = "n_419" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_420 =
  let name = "n_420" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_421 =
  let name = "n_421" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_422 =
  let name = "n_422" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_423 =
  let name = "n_423" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_424 =
  let name = "n_424" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_425 =
  let name = "n_425" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_426 =
  let name = "n_426" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_427 =
  let name = "n_427" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_428 =
  let name = "n_428" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_429 =
  let name = "n_429" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_430 =
  let name = "n_430" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_431 =
  let name = "n_431" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_432 =
  let name = "n_432" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_433 =
  let name = "n_433" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_434 =
  let name = "n_434" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_435 =
  let name = "n_435" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_436 =
  let name = "n_436" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_437 =
  let name = "n_437" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_438 =
  let name = "n_438" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_439 =
  let name = "n_439" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_440 =
  let name = "n_440" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_441 =
  let name = "n_441" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_442 =
  let name = "n_442" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_443 =
  let name = "n_443" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_444 =
  let name = "n_444" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_445 =
  let name = "n_445" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_446 =
  let name = "n_446" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_447 =
  let name = "n_447" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_448 =
  let name = "n_448" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_449 =
  let name = "n_449" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_450 =
  let name = "n_450" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_451 =
  let name = "n_451" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_452 =
  let name = "n_452" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_453 =
  let name = "n_453" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_454 =
  let name = "n_454" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_455 =
  let name = "n_455" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_456 =
  let name = "n_456" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_457 =
  let name = "n_457" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_458 =
  let name = "n_458" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_459 =
  let name = "n_459" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_460 =
  let name = "n_460" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_461 =
  let name = "n_461" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_462 =
  let name = "n_462" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_463 =
  let name = "n_463" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_464 =
  let name = "n_464" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_465 =
  let name = "n_465" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_466 =
  let name = "n_466" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_467 =
  let name = "n_467" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_468 =
  let name = "n_468" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_469 =
  let name = "n_469" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_470 =
  let name = "n_470" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_471 =
  let name = "n_471" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_472 =
  let name = "n_472" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_473 =
  let name = "n_473" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_474 =
  let name = "n_474" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_475 =
  let name = "n_475" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_476 =
  let name = "n_476" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_477 =
  let name = "n_477" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_478 =
  let name = "n_478" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (eqn (var (global "CurCmd")) (const _ReqE))) in
  prop name params formula

let n_479 =
  let name = "n_479" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_480 =
  let name = "n_480" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_481 =
  let name = "n_481" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_482 =
  let name = "n_482" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_483 =
  let name = "n_483" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_484 =
  let name = "n_484" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_485 =
  let name = "n_485" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_486 =
  let name = "n_486" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_487 =
  let name = "n_487" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_488 =
  let name = "n_488" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_489 =
  let name = "n_489" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_490 =
  let name = "n_490" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_491 =
  let name = "n_491" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_492 =
  let name = "n_492" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_493 =
  let name = "n_493" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_494 =
  let name = "n_494" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_495 =
  let name = "n_495" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_496 =
  let name = "n_496" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_497 =
  let name = "n_497" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_498 =
  let name = "n_498" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_499 =
  let name = "n_499" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_500 =
  let name = "n_500" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_501 =
  let name = "n_501" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_502 =
  let name = "n_502" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_503 =
  let name = "n_503" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_504 =
  let name = "n_504" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_505 =
  let name = "n_505" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_506 =
  let name = "n_506" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_507 =
  let name = "n_507" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_508 =
  let name = "n_508" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_509 =
  let name = "n_509" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_510 =
  let name = "n_510" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_511 =
  let name = "n_511" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_512 =
  let name = "n_512" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_513 =
  let name = "n_513" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_514 =
  let name = "n_514" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_515 =
  let name = "n_515" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_516 =
  let name = "n_516" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_517 =
  let name = "n_517" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_518 =
  let name = "n_518" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_519 =
  let name = "n_519" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_520 =
  let name = "n_520" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_521 =
  let name = "n_521" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_522 =
  let name = "n_522" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_523 =
  let name = "n_523" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_524 =
  let name = "n_524" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_525 =
  let name = "n_525" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_526 =
  let name = "n_526" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_527 =
  let name = "n_527" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_528 =
  let name = "n_528" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_529 =
  let name = "n_529" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_530 =
  let name = "n_530" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_531 =
  let name = "n_531" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_532 =
  let name = "n_532" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_533 =
  let name = "n_533" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_534 =
  let name = "n_534" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))) in
  prop name params formula

let n_535 =
  let name = "n_535" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_536 =
  let name = "n_536" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_537 =
  let name = "n_537" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_538 =
  let name = "n_538" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_539 =
  let name = "n_539" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_540 =
  let name = "n_540" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_541 =
  let name = "n_541" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_542 =
  let name = "n_542" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_543 =
  let name = "n_543" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_544 =
  let name = "n_544" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_545 =
  let name = "n_545" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_546 =
  let name = "n_546" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))) in
  prop name params formula

let n_547 =
  let name = "n_547" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))) in
  prop name params formula

let n_548 =
  let name = "n_548" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_549 =
  let name = "n_549" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_550 =
  let name = "n_550" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_551 =
  let name = "n_551" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_552 =
  let name = "n_552" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_553 =
  let name = "n_553" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_554 =
  let name = "n_554" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (global "CurCmd")) (const _ReqE))) in
  prop name params formula

let n_555 =
  let name = "n_555" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_556 =
  let name = "n_556" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_557 =
  let name = "n_557" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_558 =
  let name = "n_558" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_559 =
  let name = "n_559" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_560 =
  let name = "n_560" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_561 =
  let name = "n_561" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_562 =
  let name = "n_562" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_563 =
  let name = "n_563" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_564 =
  let name = "n_564" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))) in
  prop name params formula

let n_565 =
  let name = "n_565" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_566 =
  let name = "n_566" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_567 =
  let name = "n_567" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_568 =
  let name = "n_568" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_569 =
  let name = "n_569" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_570 =
  let name = "n_570" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_571 =
  let name = "n_571" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_572 =
  let name = "n_572" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_573 =
  let name = "n_573" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_574 =
  let name = "n_574" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_575 =
  let name = "n_575" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_576 =
  let name = "n_576" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_577 =
  let name = "n_577" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_578 =
  let name = "n_578" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_579 =
  let name = "n_579" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_580 =
  let name = "n_580" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_581 =
  let name = "n_581" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_582 =
  let name = "n_582" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_583 =
  let name = "n_583" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_584 =
  let name = "n_584" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_585 =
  let name = "n_585" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_586 =
  let name = "n_586" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_587 =
  let name = "n_587" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_588 =
  let name = "n_588" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_589 =
  let name = "n_589" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_590 =
  let name = "n_590" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_591 =
  let name = "n_591" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_592 =
  let name = "n_592" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_593 =
  let name = "n_593" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))) in
  prop name params formula

let n_594 =
  let name = "n_594" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_595 =
  let name = "n_595" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_596 =
  let name = "n_596" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_597 =
  let name = "n_597" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_598 =
  let name = "n_598" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_599 =
  let name = "n_599" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_600 =
  let name = "n_600" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_601 =
  let name = "n_601" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_602 =
  let name = "n_602" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_603 =
  let name = "n_603" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_604 =
  let name = "n_604" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_605 =
  let name = "n_605" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_606 =
  let name = "n_606" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_607 =
  let name = "n_607" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_608 =
  let name = "n_608" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_609 =
  let name = "n_609" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_610 =
  let name = "n_610" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_611 =
  let name = "n_611" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_612 =
  let name = "n_612" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_613 =
  let name = "n_613" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_614 =
  let name = "n_614" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_615 =
  let name = "n_615" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_616 =
  let name = "n_616" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_617 =
  let name = "n_617" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_618 =
  let name = "n_618" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_619 =
  let name = "n_619" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_620 =
  let name = "n_620" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_621 =
  let name = "n_621" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_622 =
  let name = "n_622" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_623 =
  let name = "n_623" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_624 =
  let name = "n_624" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_625 =
  let name = "n_625" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_626 =
  let name = "n_626" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_627 =
  let name = "n_627" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_628 =
  let name = "n_628" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_629 =
  let name = "n_629" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_630 =
  let name = "n_630" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_631 =
  let name = "n_631" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_632 =
  let name = "n_632" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_633 =
  let name = "n_633" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_634 =
  let name = "n_634" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_635 =
  let name = "n_635" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_636 =
  let name = "n_636" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_637 =
  let name = "n_637" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_638 =
  let name = "n_638" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "CurCmd")) (const _ReqE)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_639 =
  let name = "n_639" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "CurCmd")) (const _ReqE)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_640 =
  let name = "n_640" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "CurCmd")) (const _ReqE)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_641 =
  let name = "n_641" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_642 =
  let name = "n_642" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_643 =
  let name = "n_643" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_644 =
  let name = "n_644" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_645 =
  let name = "n_645" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_646 =
  let name = "n_646" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_647 =
  let name = "n_647" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_648 =
  let name = "n_648" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_649 =
  let name = "n_649" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_650 =
  let name = "n_650" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_651 =
  let name = "n_651" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_652 =
  let name = "n_652" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_653 =
  let name = "n_653" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_654 =
  let name = "n_654" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_655 =
  let name = "n_655" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_656 =
  let name = "n_656" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_657 =
  let name = "n_657" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_658 =
  let name = "n_658" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_659 =
  let name = "n_659" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_660 =
  let name = "n_660" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_661 =
  let name = "n_661" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_662 =
  let name = "n_662" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_663 =
  let name = "n_663" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_664 =
  let name = "n_664" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_665 =
  let name = "n_665" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_666 =
  let name = "n_666" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_667 =
  let name = "n_667" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_668 =
  let name = "n_668" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_669 =
  let name = "n_669" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))) in
  prop name params formula

let n_670 =
  let name = "n_670" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_671 =
  let name = "n_671" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_672 =
  let name = "n_672" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_673 =
  let name = "n_673" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_674 =
  let name = "n_674" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_675 =
  let name = "n_675" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_676 =
  let name = "n_676" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_677 =
  let name = "n_677" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_678 =
  let name = "n_678" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_679 =
  let name = "n_679" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_680 =
  let name = "n_680" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_681 =
  let name = "n_681" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_682 =
  let name = "n_682" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_683 =
  let name = "n_683" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_684 =
  let name = "n_684" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_685 =
  let name = "n_685" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_686 =
  let name = "n_686" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_687 =
  let name = "n_687" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_688 =
  let name = "n_688" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_689 =
  let name = "n_689" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_690 =
  let name = "n_690" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_691 =
  let name = "n_691" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_692 =
  let name = "n_692" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_693 =
  let name = "n_693" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_694 =
  let name = "n_694" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "CurCmd")) (const _Empty))) in
  prop name params formula

let n_695 =
  let name = "n_695" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_696 =
  let name = "n_696" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_697 =
  let name = "n_697" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_698 =
  let name = "n_698" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_699 =
  let name = "n_699" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_700 =
  let name = "n_700" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) in
  prop name params formula

let n_701 =
  let name = "n_701" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_702 =
  let name = "n_702" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_703 =
  let name = "n_703" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_704 =
  let name = "n_704" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_705 =
  let name = "n_705" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_706 =
  let name = "n_706" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_707 =
  let name = "n_707" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_708 =
  let name = "n_708" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_709 =
  let name = "n_709" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_710 =
  let name = "n_710" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_711 =
  let name = "n_711" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_712 =
  let name = "n_712" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_713 =
  let name = "n_713" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_714 =
  let name = "n_714" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_715 =
  let name = "n_715" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_716 =
  let name = "n_716" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_717 =
  let name = "n_717" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_718 =
  let name = "n_718" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_719 =
  let name = "n_719" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_720 =
  let name = "n_720" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_721 =
  let name = "n_721" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_722 =
  let name = "n_722" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_723 =
  let name = "n_723" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_724 =
  let name = "n_724" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_725 =
  let name = "n_725" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_726 =
  let name = "n_726" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_727 =
  let name = "n_727" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) in
  prop name params formula

let n_728 =
  let name = "n_728" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_729 =
  let name = "n_729" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_730 =
  let name = "n_730" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_731 =
  let name = "n_731" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_732 =
  let name = "n_732" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_733 =
  let name = "n_733" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_734 =
  let name = "n_734" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_735 =
  let name = "n_735" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "CurCmd")) (const _Empty))) in
  prop name params formula

let n_736 =
  let name = "n_736" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_737 =
  let name = "n_737" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_738 =
  let name = "n_738" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_739 =
  let name = "n_739" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_740 =
  let name = "n_740" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_741 =
  let name = "n_741" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_742 =
  let name = "n_742" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_743 =
  let name = "n_743" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_744 =
  let name = "n_744" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_745 =
  let name = "n_745" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_746 =
  let name = "n_746" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_747 =
  let name = "n_747" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_748 =
  let name = "n_748" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_749 =
  let name = "n_749" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_750 =
  let name = "n_750" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_751 =
  let name = "n_751" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_752 =
  let name = "n_752" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_753 =
  let name = "n_753" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_754 =
  let name = "n_754" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_755 =
  let name = "n_755" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_756 =
  let name = "n_756" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_757 =
  let name = "n_757" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_758 =
  let name = "n_758" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_759 =
  let name = "n_759" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_760 =
  let name = "n_760" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_761 =
  let name = "n_761" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_762 =
  let name = "n_762" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_763 =
  let name = "n_763" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_764 =
  let name = "n_764" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_765 =
  let name = "n_765" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_766 =
  let name = "n_766" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (global "CurCmd")) (const _ReqE))) in
  prop name params formula

let n_767 =
  let name = "n_767" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_768 =
  let name = "n_768" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_769 =
  let name = "n_769" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_770 =
  let name = "n_770" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_771 =
  let name = "n_771" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_772 =
  let name = "n_772" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_773 =
  let name = "n_773" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_774 =
  let name = "n_774" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_775 =
  let name = "n_775" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_776 =
  let name = "n_776" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_777 =
  let name = "n_777" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_778 =
  let name = "n_778" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_779 =
  let name = "n_779" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_780 =
  let name = "n_780" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_781 =
  let name = "n_781" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_782 =
  let name = "n_782" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_783 =
  let name = "n_783" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_784 =
  let name = "n_784" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_785 =
  let name = "n_785" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))) in
  prop name params formula

let n_786 =
  let name = "n_786" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))) in
  prop name params formula

let n_787 =
  let name = "n_787" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_788 =
  let name = "n_788" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_789 =
  let name = "n_789" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))) in
  prop name params formula

let n_790 =
  let name = "n_790" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_791 =
  let name = "n_791" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_792 =
  let name = "n_792" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))) in
  prop name params formula

let n_793 =
  let name = "n_793" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_794 =
  let name = "n_794" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_795 =
  let name = "n_795" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_796 =
  let name = "n_796" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_797 =
  let name = "n_797" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_798 =
  let name = "n_798" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) in
  prop name params formula

let n_799 =
  let name = "n_799" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_800 =
  let name = "n_800" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_801 =
  let name = "n_801" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_802 =
  let name = "n_802" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_803 =
  let name = "n_803" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_804 =
  let name = "n_804" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_805 =
  let name = "n_805" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_806 =
  let name = "n_806" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_807 =
  let name = "n_807" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_808 =
  let name = "n_808" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_809 =
  let name = "n_809" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_810 =
  let name = "n_810" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_811 =
  let name = "n_811" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_812 =
  let name = "n_812" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_813 =
  let name = "n_813" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_814 =
  let name = "n_814" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_815 =
  let name = "n_815" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_816 =
  let name = "n_816" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_817 =
  let name = "n_817" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_818 =
  let name = "n_818" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_819 =
  let name = "n_819" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_820 =
  let name = "n_820" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) in
  prop name params formula

let n_821 =
  let name = "n_821" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_822 =
  let name = "n_822" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_823 =
  let name = "n_823" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))) in
  prop name params formula

let n_824 =
  let name = "n_824" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))) in
  prop name params formula

let n_825 =
  let name = "n_825" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_826 =
  let name = "n_826" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_827 =
  let name = "n_827" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_828 =
  let name = "n_828" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_829 =
  let name = "n_829" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_830 =
  let name = "n_830" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_831 =
  let name = "n_831" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_832 =
  let name = "n_832" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_833 =
  let name = "n_833" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) in
  prop name params formula

let n_834 =
  let name = "n_834" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_835 =
  let name = "n_835" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))) in
  prop name params formula

let n_836 =
  let name = "n_836" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_837 =
  let name = "n_837" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_838 =
  let name = "n_838" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_839 =
  let name = "n_839" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_840 =
  let name = "n_840" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "CurCmd")) (const _Empty))) in
  prop name params formula

let n_841 =
  let name = "n_841" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_842 =
  let name = "n_842" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_843 =
  let name = "n_843" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_844 =
  let name = "n_844" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_845 =
  let name = "n_845" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_846 =
  let name = "n_846" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_847 =
  let name = "n_847" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_848 =
  let name = "n_848" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_849 =
  let name = "n_849" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_850 =
  let name = "n_850" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_851 =
  let name = "n_851" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_852 =
  let name = "n_852" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_853 =
  let name = "n_853" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_854 =
  let name = "n_854" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_855 =
  let name = "n_855" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_856 =
  let name = "n_856" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_857 =
  let name = "n_857" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_858 =
  let name = "n_858" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_859 =
  let name = "n_859" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_860 =
  let name = "n_860" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_861 =
  let name = "n_861" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_862 =
  let name = "n_862" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_863 =
  let name = "n_863" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_864 =
  let name = "n_864" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_865 =
  let name = "n_865" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_866 =
  let name = "n_866" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_867 =
  let name = "n_867" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_868 =
  let name = "n_868" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_869 =
  let name = "n_869" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_870 =
  let name = "n_870" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_871 =
  let name = "n_871" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_872 =
  let name = "n_872" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_873 =
  let name = "n_873" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_874 =
  let name = "n_874" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_875 =
  let name = "n_875" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_876 =
  let name = "n_876" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_877 =
  let name = "n_877" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_878 =
  let name = "n_878" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_879 =
  let name = "n_879" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_880 =
  let name = "n_880" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_881 =
  let name = "n_881" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_882 =
  let name = "n_882" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_883 =
  let name = "n_883" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_884 =
  let name = "n_884" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_885 =
  let name = "n_885" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_886 =
  let name = "n_886" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_887 =
  let name = "n_887" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_888 =
  let name = "n_888" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_889 =
  let name = "n_889" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_890 =
  let name = "n_890" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_891 =
  let name = "n_891" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_892 =
  let name = "n_892" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_893 =
  let name = "n_893" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_894 =
  let name = "n_894" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_895 =
  let name = "n_895" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_896 =
  let name = "n_896" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_897 =
  let name = "n_897" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_898 =
  let name = "n_898" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_899 =
  let name = "n_899" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_900 =
  let name = "n_900" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_901 =
  let name = "n_901" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_902 =
  let name = "n_902" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_903 =
  let name = "n_903" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_904 =
  let name = "n_904" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_905 =
  let name = "n_905" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_906 =
  let name = "n_906" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_907 =
  let name = "n_907" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (global "CurCmd")) (const _ReqE))) in
  prop name params formula

let n_908 =
  let name = "n_908" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_909 =
  let name = "n_909" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_910 =
  let name = "n_910" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_911 =
  let name = "n_911" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_912 =
  let name = "n_912" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_913 =
  let name = "n_913" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_914 =
  let name = "n_914" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_915 =
  let name = "n_915" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_916 =
  let name = "n_916" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_917 =
  let name = "n_917" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_918 =
  let name = "n_918" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_919 =
  let name = "n_919" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_920 =
  let name = "n_920" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_921 =
  let name = "n_921" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_922 =
  let name = "n_922" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_923 =
  let name = "n_923" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_924 =
  let name = "n_924" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_925 =
  let name = "n_925" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_926 =
  let name = "n_926" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_927 =
  let name = "n_927" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) in
  prop name params formula

let n_928 =
  let name = "n_928" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_929 =
  let name = "n_929" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_930 =
  let name = "n_930" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_931 =
  let name = "n_931" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_932 =
  let name = "n_932" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_933 =
  let name = "n_933" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_934 =
  let name = "n_934" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_935 =
  let name = "n_935" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_936 =
  let name = "n_936" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_937 =
  let name = "n_937" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_938 =
  let name = "n_938" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_939 =
  let name = "n_939" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_940 =
  let name = "n_940" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_941 =
  let name = "n_941" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_942 =
  let name = "n_942" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_943 =
  let name = "n_943" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_944 =
  let name = "n_944" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_945 =
  let name = "n_945" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_946 =
  let name = "n_946" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_947 =
  let name = "n_947" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_948 =
  let name = "n_948" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_949 =
  let name = "n_949" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_950 =
  let name = "n_950" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_951 =
  let name = "n_951" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_952 =
  let name = "n_952" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_953 =
  let name = "n_953" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_954 =
  let name = "n_954" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_955 =
  let name = "n_955" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_956 =
  let name = "n_956" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_957 =
  let name = "n_957" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_958 =
  let name = "n_958" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_959 =
  let name = "n_959" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_960 =
  let name = "n_960" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_961 =
  let name = "n_961" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_962 =
  let name = "n_962" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_963 =
  let name = "n_963" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_964 =
  let name = "n_964" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_965 =
  let name = "n_965" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_966 =
  let name = "n_966" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_967 =
  let name = "n_967" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_968 =
  let name = "n_968" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_969 =
  let name = "n_969" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_970 =
  let name = "n_970" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_971 =
  let name = "n_971" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_972 =
  let name = "n_972" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_973 =
  let name = "n_973" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_974 =
  let name = "n_974" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_975 =
  let name = "n_975" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_976 =
  let name = "n_976" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_977 =
  let name = "n_977" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_978 =
  let name = "n_978" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_979 =
  let name = "n_979" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_980 =
  let name = "n_980" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_981 =
  let name = "n_981" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_982 =
  let name = "n_982" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_983 =
  let name = "n_983" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_984 =
  let name = "n_984" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_985 =
  let name = "n_985" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (global "CurCmd")) (const _ReqE))) in
  prop name params formula

let n_986 =
  let name = "n_986" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_987 =
  let name = "n_987" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_988 =
  let name = "n_988" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_989 =
  let name = "n_989" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_990 =
  let name = "n_990" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_991 =
  let name = "n_991" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_992 =
  let name = "n_992" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_993 =
  let name = "n_993" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_994 =
  let name = "n_994" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_995 =
  let name = "n_995" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_996 =
  let name = "n_996" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) in
  prop name params formula

let n_997 =
  let name = "n_997" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_998 =
  let name = "n_998" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_999 =
  let name = "n_999" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1000 =
  let name = "n_1000" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1001 =
  let name = "n_1001" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1002 =
  let name = "n_1002" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_1003 =
  let name = "n_1003" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1004 =
  let name = "n_1004" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1005 =
  let name = "n_1005" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_1006 =
  let name = "n_1006" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1007 =
  let name = "n_1007" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1008 =
  let name = "n_1008" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1009 =
  let name = "n_1009" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1010 =
  let name = "n_1010" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_1011 =
  let name = "n_1011" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1012 =
  let name = "n_1012" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1013 =
  let name = "n_1013" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1014 =
  let name = "n_1014" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1015 =
  let name = "n_1015" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1016 =
  let name = "n_1016" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1017 =
  let name = "n_1017" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_1018 =
  let name = "n_1018" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1019 =
  let name = "n_1019" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1020 =
  let name = "n_1020" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1021 =
  let name = "n_1021" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1022 =
  let name = "n_1022" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))) in
  prop name params formula

let n_1023 =
  let name = "n_1023" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1024 =
  let name = "n_1024" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1025 =
  let name = "n_1025" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1026 =
  let name = "n_1026" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1027 =
  let name = "n_1027" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1028 =
  let name = "n_1028" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1029 =
  let name = "n_1029" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_1030 =
  let name = "n_1030" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1031 =
  let name = "n_1031" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1032 =
  let name = "n_1032" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1033 =
  let name = "n_1033" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1034 =
  let name = "n_1034" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1035 =
  let name = "n_1035" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1036 =
  let name = "n_1036" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1037 =
  let name = "n_1037" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1038 =
  let name = "n_1038" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1039 =
  let name = "n_1039" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1040 =
  let name = "n_1040" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1041 =
  let name = "n_1041" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1042 =
  let name = "n_1042" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1043 =
  let name = "n_1043" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1044 =
  let name = "n_1044" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1045 =
  let name = "n_1045" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1046 =
  let name = "n_1046" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1047 =
  let name = "n_1047" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1048 =
  let name = "n_1048" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1049 =
  let name = "n_1049" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1050 =
  let name = "n_1050" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1051 =
  let name = "n_1051" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1052 =
  let name = "n_1052" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1053 =
  let name = "n_1053" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1054 =
  let name = "n_1054" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1055 =
  let name = "n_1055" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1056 =
  let name = "n_1056" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1057 =
  let name = "n_1057" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1058 =
  let name = "n_1058" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1059 =
  let name = "n_1059" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1060 =
  let name = "n_1060" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_1061 =
  let name = "n_1061" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (global "CurCmd")) (const _ReqE))) in
  prop name params formula

let n_1062 =
  let name = "n_1062" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1063 =
  let name = "n_1063" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1064 =
  let name = "n_1064" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1065 =
  let name = "n_1065" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_1066 =
  let name = "n_1066" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1067 =
  let name = "n_1067" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1068 =
  let name = "n_1068" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1069 =
  let name = "n_1069" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_1070 =
  let name = "n_1070" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1071 =
  let name = "n_1071" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1072 =
  let name = "n_1072" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1073 =
  let name = "n_1073" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1074 =
  let name = "n_1074" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1075 =
  let name = "n_1075" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1076 =
  let name = "n_1076" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_1077 =
  let name = "n_1077" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1078 =
  let name = "n_1078" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1079 =
  let name = "n_1079" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1080 =
  let name = "n_1080" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1081 =
  let name = "n_1081" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1082 =
  let name = "n_1082" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1083 =
  let name = "n_1083" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1084 =
  let name = "n_1084" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1085 =
  let name = "n_1085" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1086 =
  let name = "n_1086" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1087 =
  let name = "n_1087" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_1088 =
  let name = "n_1088" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1089 =
  let name = "n_1089" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1090 =
  let name = "n_1090" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1091 =
  let name = "n_1091" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_1092 =
  let name = "n_1092" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1093 =
  let name = "n_1093" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1094 =
  let name = "n_1094" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1095 =
  let name = "n_1095" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1096 =
  let name = "n_1096" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1097 =
  let name = "n_1097" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1098 =
  let name = "n_1098" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_1099 =
  let name = "n_1099" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1100 =
  let name = "n_1100" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_1101 =
  let name = "n_1101" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1102 =
  let name = "n_1102" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1103 =
  let name = "n_1103" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1104 =
  let name = "n_1104" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1105 =
  let name = "n_1105" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1106 =
  let name = "n_1106" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_1107 =
  let name = "n_1107" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1108 =
  let name = "n_1108" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1109 =
  let name = "n_1109" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1110 =
  let name = "n_1110" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1111 =
  let name = "n_1111" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1112 =
  let name = "n_1112" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1113 =
  let name = "n_1113" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1114 =
  let name = "n_1114" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1115 =
  let name = "n_1115" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1116 =
  let name = "n_1116" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1117 =
  let name = "n_1117" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))) in
  prop name params formula

let n_1118 =
  let name = "n_1118" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1119 =
  let name = "n_1119" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1120 =
  let name = "n_1120" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1121 =
  let name = "n_1121" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1122 =
  let name = "n_1122" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1123 =
  let name = "n_1123" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1124 =
  let name = "n_1124" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_1125 =
  let name = "n_1125" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData"))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1126 =
  let name = "n_1126" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1127 =
  let name = "n_1127" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1128 =
  let name = "n_1128" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1129 =
  let name = "n_1129" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _Empty))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1130 =
  let name = "n_1130" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1131 =
  let name = "n_1131" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _Empty))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1132 =
  let name = "n_1132" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1133 =
  let name = "n_1133" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1134 =
  let name = "n_1134" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1135 =
  let name = "n_1135" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1136 =
  let name = "n_1136" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1137 =
  let name = "n_1137" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1138 =
  let name = "n_1138" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1139 =
  let name = "n_1139" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1140 =
  let name = "n_1140" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1141 =
  let name = "n_1141" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1142 =
  let name = "n_1142" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1143 =
  let name = "n_1143" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1144 =
  let name = "n_1144" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1145 =
  let name = "n_1145" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1146 =
  let name = "n_1146" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1147 =
  let name = "n_1147" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1148 =
  let name = "n_1148" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1149 =
  let name = "n_1149" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1150 =
  let name = "n_1150" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1151 =
  let name = "n_1151" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1152 =
  let name = "n_1152" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1153 =
  let name = "n_1153" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1154 =
  let name = "n_1154" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1155 =
  let name = "n_1155" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1156 =
  let name = "n_1156" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1157 =
  let name = "n_1157" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1158 =
  let name = "n_1158" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))) in
  prop name params formula

let n_1159 =
  let name = "n_1159" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1160 =
  let name = "n_1160" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1161 =
  let name = "n_1161" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1162 =
  let name = "n_1162" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1163 =
  let name = "n_1163" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1164 =
  let name = "n_1164" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1165 =
  let name = "n_1165" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1166 =
  let name = "n_1166" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1167 =
  let name = "n_1167" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1168 =
  let name = "n_1168" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1169 =
  let name = "n_1169" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1170 =
  let name = "n_1170" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1171 =
  let name = "n_1171" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1172 =
  let name = "n_1172" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1173 =
  let name = "n_1173" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1174 =
  let name = "n_1174" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1175 =
  let name = "n_1175" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1176 =
  let name = "n_1176" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1177 =
  let name = "n_1177" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1178 =
  let name = "n_1178" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1179 =
  let name = "n_1179" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))) in
  prop name params formula

let n_1180 =
  let name = "n_1180" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1181 =
  let name = "n_1181" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1182 =
  let name = "n_1182" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1183 =
  let name = "n_1183" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1184 =
  let name = "n_1184" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1185 =
  let name = "n_1185" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1186 =
  let name = "n_1186" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1187 =
  let name = "n_1187" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1188 =
  let name = "n_1188" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1189 =
  let name = "n_1189" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1190 =
  let name = "n_1190" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1191 =
  let name = "n_1191" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1192 =
  let name = "n_1192" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1193 =
  let name = "n_1193" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1194 =
  let name = "n_1194" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1195 =
  let name = "n_1195" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1196 =
  let name = "n_1196" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1197 =
  let name = "n_1197" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1198 =
  let name = "n_1198" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1199 =
  let name = "n_1199" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1200 =
  let name = "n_1200" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1201 =
  let name = "n_1201" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1202 =
  let name = "n_1202" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1203 =
  let name = "n_1203" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1204 =
  let name = "n_1204" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1205 =
  let name = "n_1205" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1206 =
  let name = "n_1206" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1207 =
  let name = "n_1207" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1208 =
  let name = "n_1208" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1209 =
  let name = "n_1209" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1210 =
  let name = "n_1210" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1211 =
  let name = "n_1211" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1212 =
  let name = "n_1212" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1213 =
  let name = "n_1213" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1214 =
  let name = "n_1214" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1215 =
  let name = "n_1215" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1216 =
  let name = "n_1216" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1217 =
  let name = "n_1217" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1218 =
  let name = "n_1218" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1219 =
  let name = "n_1219" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1220 =
  let name = "n_1220" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1221 =
  let name = "n_1221" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1222 =
  let name = "n_1222" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1223 =
  let name = "n_1223" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1224 =
  let name = "n_1224" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1225 =
  let name = "n_1225" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1226 =
  let name = "n_1226" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1227 =
  let name = "n_1227" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1228 =
  let name = "n_1228" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1229 =
  let name = "n_1229" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1230 =
  let name = "n_1230" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1231 =
  let name = "n_1231" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1232 =
  let name = "n_1232" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1233 =
  let name = "n_1233" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1234 =
  let name = "n_1234" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1235 =
  let name = "n_1235" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1236 =
  let name = "n_1236" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1237 =
  let name = "n_1237" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1238 =
  let name = "n_1238" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1239 =
  let name = "n_1239" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1240 =
  let name = "n_1240" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (global "CurCmd")) (const _ReqS)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1241 =
  let name = "n_1241" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (global "CurCmd")) (const _ReqS)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1242 =
  let name = "n_1242" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (global "CurCmd")) (const _ReqS)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1243 =
  let name = "n_1243" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (global "CurCmd")) (const _ReqS)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1244 =
  let name = "n_1244" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (global "CurCmd")) (const _ReqS)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1245 =
  let name = "n_1245" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (global "CurCmd")) (const _ReqS)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1246 =
  let name = "n_1246" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (global "CurCmd")) (const _ReqS)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1247 =
  let name = "n_1247" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (global "CurCmd")) (const _ReqS)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1248 =
  let name = "n_1248" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (global "CurCmd")) (const _ReqS)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1249 =
  let name = "n_1249" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (neg (eqn (var (global "CurCmd")) (const _ReqS)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1250 =
  let name = "n_1250" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1251 =
  let name = "n_1251" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1252 =
  let name = "n_1252" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1253 =
  let name = "n_1253" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1254 =
  let name = "n_1254" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1255 =
  let name = "n_1255" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1256 =
  let name = "n_1256" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1257 =
  let name = "n_1257" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1258 =
  let name = "n_1258" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1259 =
  let name = "n_1259" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1260 =
  let name = "n_1260" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1261 =
  let name = "n_1261" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1262 =
  let name = "n_1262" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1263 =
  let name = "n_1263" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1264 =
  let name = "n_1264" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1265 =
  let name = "n_1265" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1266 =
  let name = "n_1266" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1267 =
  let name = "n_1267" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1268 =
  let name = "n_1268" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1269 =
  let name = "n_1269" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1270 =
  let name = "n_1270" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "CurCmd")) (const _ReqE))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1271 =
  let name = "n_1271" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1272 =
  let name = "n_1272" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1273 =
  let name = "n_1273" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1274 =
  let name = "n_1274" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1275 =
  let name = "n_1275" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1276 =
  let name = "n_1276" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1277 =
  let name = "n_1277" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1278 =
  let name = "n_1278" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1279 =
  let name = "n_1279" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1280 =
  let name = "n_1280" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1281 =
  let name = "n_1281" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1282 =
  let name = "n_1282" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1283 =
  let name = "n_1283" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))) in
  prop name params formula

let n_1284 =
  let name = "n_1284" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1285 =
  let name = "n_1285" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1286 =
  let name = "n_1286" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1287 =
  let name = "n_1287" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1288 =
  let name = "n_1288" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1289 =
  let name = "n_1289" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1290 =
  let name = "n_1290" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1291 =
  let name = "n_1291" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1292 =
  let name = "n_1292" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1293 =
  let name = "n_1293" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1294 =
  let name = "n_1294" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1295 =
  let name = "n_1295" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1296 =
  let name = "n_1296" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1297 =
  let name = "n_1297" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1298 =
  let name = "n_1298" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1299 =
  let name = "n_1299" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1300 =
  let name = "n_1300" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1301 =
  let name = "n_1301" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1302 =
  let name = "n_1302" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1303 =
  let name = "n_1303" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1304 =
  let name = "n_1304" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1305 =
  let name = "n_1305" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1306 =
  let name = "n_1306" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1307 =
  let name = "n_1307" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1308 =
  let name = "n_1308" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1309 =
  let name = "n_1309" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1310 =
  let name = "n_1310" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))) in
  prop name params formula

let n_1311 =
  let name = "n_1311" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1312 =
  let name = "n_1312" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1313 =
  let name = "n_1313" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1314 =
  let name = "n_1314" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1315 =
  let name = "n_1315" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1316 =
  let name = "n_1316" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1317 =
  let name = "n_1317" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1318 =
  let name = "n_1318" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))) in
  prop name params formula

let n_1319 =
  let name = "n_1319" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1320 =
  let name = "n_1320" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1321 =
  let name = "n_1321" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1322 =
  let name = "n_1322" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1323 =
  let name = "n_1323" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1324 =
  let name = "n_1324" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1325 =
  let name = "n_1325" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1326 =
  let name = "n_1326" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1327 =
  let name = "n_1327" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1328 =
  let name = "n_1328" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1329 =
  let name = "n_1329" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_1330 =
  let name = "n_1330" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1331 =
  let name = "n_1331" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_1332 =
  let name = "n_1332" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1333 =
  let name = "n_1333" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1334 =
  let name = "n_1334" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1335 =
  let name = "n_1335" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1336 =
  let name = "n_1336" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1337 =
  let name = "n_1337" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1338 =
  let name = "n_1338" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1339 =
  let name = "n_1339" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1340 =
  let name = "n_1340" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1341 =
  let name = "n_1341" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1342 =
  let name = "n_1342" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1343 =
  let name = "n_1343" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1344 =
  let name = "n_1344" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1345 =
  let name = "n_1345" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1346 =
  let name = "n_1346" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1347 =
  let name = "n_1347" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1348 =
  let name = "n_1348" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1349 =
  let name = "n_1349" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1350 =
  let name = "n_1350" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1351 =
  let name = "n_1351" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1352 =
  let name = "n_1352" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1353 =
  let name = "n_1353" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))) in
  prop name params formula

let n_1354 =
  let name = "n_1354" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1355 =
  let name = "n_1355" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1356 =
  let name = "n_1356" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1357 =
  let name = "n_1357" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))) in
  prop name params formula

let n_1358 =
  let name = "n_1358" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1359 =
  let name = "n_1359" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1360 =
  let name = "n_1360" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1361 =
  let name = "n_1361" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1362 =
  let name = "n_1362" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1363 =
  let name = "n_1363" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_1364 =
  let name = "n_1364" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1365 =
  let name = "n_1365" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_1366 =
  let name = "n_1366" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1367 =
  let name = "n_1367" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1368 =
  let name = "n_1368" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1369 =
  let name = "n_1369" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1370 =
  let name = "n_1370" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1371 =
  let name = "n_1371" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1372 =
  let name = "n_1372" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1373 =
  let name = "n_1373" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1374 =
  let name = "n_1374" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1375 =
  let name = "n_1375" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1376 =
  let name = "n_1376" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1377 =
  let name = "n_1377" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1378 =
  let name = "n_1378" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1379 =
  let name = "n_1379" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1380 =
  let name = "n_1380" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1381 =
  let name = "n_1381" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1382 =
  let name = "n_1382" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1383 =
  let name = "n_1383" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1384 =
  let name = "n_1384" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1385 =
  let name = "n_1385" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1386 =
  let name = "n_1386" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1387 =
  let name = "n_1387" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1388 =
  let name = "n_1388" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1389 =
  let name = "n_1389" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1390 =
  let name = "n_1390" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1391 =
  let name = "n_1391" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1392 =
  let name = "n_1392" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1393 =
  let name = "n_1393" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _Empty)); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1394 =
  let name = "n_1394" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (global "CurCmd")) (const _Empty)) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1395 =
  let name = "n_1395" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (global "CurCmd")) (const _Empty)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1396 =
  let name = "n_1396" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (global "CurCmd")) (const _Empty)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1397 =
  let name = "n_1397" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (global "CurCmd")) (const _Empty)) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1398 =
  let name = "n_1398" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (global "CurCmd")) (const _Empty)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1399 =
  let name = "n_1399" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (global "CurCmd")) (const _Empty)) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1400 =
  let name = "n_1400" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (global "CurCmd")) (const _Empty)) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1401 =
  let name = "n_1401" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (global "CurCmd")) (const _Empty)) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1402 =
  let name = "n_1402" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (global "CurCmd")) (const _Empty)) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1403 =
  let name = "n_1403" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (global "CurCmd")) (const _Empty)) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1404 =
  let name = "n_1404" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqE)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1405 =
  let name = "n_1405" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqE)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1406 =
  let name = "n_1406" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqE)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1407 =
  let name = "n_1407" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqE)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1408 =
  let name = "n_1408" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqE)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1409 =
  let name = "n_1409" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqE)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1410 =
  let name = "n_1410" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1411 =
  let name = "n_1411" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1412 =
  let name = "n_1412" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1413 =
  let name = "n_1413" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1414 =
  let name = "n_1414" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1415 =
  let name = "n_1415" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1416 =
  let name = "n_1416" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1417 =
  let name = "n_1417" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1418 =
  let name = "n_1418" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1419 =
  let name = "n_1419" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1420 =
  let name = "n_1420" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1421 =
  let name = "n_1421" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1422 =
  let name = "n_1422" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1423 =
  let name = "n_1423" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1424 =
  let name = "n_1424" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1425 =
  let name = "n_1425" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1426 =
  let name = "n_1426" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1427 =
  let name = "n_1427" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1428 =
  let name = "n_1428" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1429 =
  let name = "n_1429" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1430 =
  let name = "n_1430" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1431 =
  let name = "n_1431" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1432 =
  let name = "n_1432" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1433 =
  let name = "n_1433" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))) in
  prop name params formula

let n_1434 =
  let name = "n_1434" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1435 =
  let name = "n_1435" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1436 =
  let name = "n_1436" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1437 =
  let name = "n_1437" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1438 =
  let name = "n_1438" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1439 =
  let name = "n_1439" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1440 =
  let name = "n_1440" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1441 =
  let name = "n_1441" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1442 =
  let name = "n_1442" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1443 =
  let name = "n_1443" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1444 =
  let name = "n_1444" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1445 =
  let name = "n_1445" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1446 =
  let name = "n_1446" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1447 =
  let name = "n_1447" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1448 =
  let name = "n_1448" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1449 =
  let name = "n_1449" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1450 =
  let name = "n_1450" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1451 =
  let name = "n_1451" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1452 =
  let name = "n_1452" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1453 =
  let name = "n_1453" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1454 =
  let name = "n_1454" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1455 =
  let name = "n_1455" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1456 =
  let name = "n_1456" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1457 =
  let name = "n_1457" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1458 =
  let name = "n_1458" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1459 =
  let name = "n_1459" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1460 =
  let name = "n_1460" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1461 =
  let name = "n_1461" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1462 =
  let name = "n_1462" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1463 =
  let name = "n_1463" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1464 =
  let name = "n_1464" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1465 =
  let name = "n_1465" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1466 =
  let name = "n_1466" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1467 =
  let name = "n_1467" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1468 =
  let name = "n_1468" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1469 =
  let name = "n_1469" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1470 =
  let name = "n_1470" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1471 =
  let name = "n_1471" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1472 =
  let name = "n_1472" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1473 =
  let name = "n_1473" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1474 =
  let name = "n_1474" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1475 =
  let name = "n_1475" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1476 =
  let name = "n_1476" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1477 =
  let name = "n_1477" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1478 =
  let name = "n_1478" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1479 =
  let name = "n_1479" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1480 =
  let name = "n_1480" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1481 =
  let name = "n_1481" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1482 =
  let name = "n_1482" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))) in
  prop name params formula

let n_1483 =
  let name = "n_1483" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))) in
  prop name params formula

let n_1484 =
  let name = "n_1484" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1485 =
  let name = "n_1485" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1486 =
  let name = "n_1486" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1487 =
  let name = "n_1487" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1488 =
  let name = "n_1488" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1489 =
  let name = "n_1489" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1490 =
  let name = "n_1490" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1491 =
  let name = "n_1491" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1492 =
  let name = "n_1492" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1493 =
  let name = "n_1493" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1494 =
  let name = "n_1494" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))) in
  prop name params formula

let n_1495 =
  let name = "n_1495" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))) in
  prop name params formula

let n_1496 =
  let name = "n_1496" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1497 =
  let name = "n_1497" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1498 =
  let name = "n_1498" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1499 =
  let name = "n_1499" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1500 =
  let name = "n_1500" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_1501 =
  let name = "n_1501" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE))) in
  prop name params formula

let n_1502 =
  let name = "n_1502" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1503 =
  let name = "n_1503" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1504 =
  let name = "n_1504" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1505 =
  let name = "n_1505" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1506 =
  let name = "n_1506" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1507 =
  let name = "n_1507" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1508 =
  let name = "n_1508" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1509 =
  let name = "n_1509" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1510 =
  let name = "n_1510" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1511 =
  let name = "n_1511" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_1512 =
  let name = "n_1512" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE))) in
  prop name params formula

let n_1513 =
  let name = "n_1513" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1514 =
  let name = "n_1514" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1515 =
  let name = "n_1515" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1516 =
  let name = "n_1516" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1517 =
  let name = "n_1517" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1518 =
  let name = "n_1518" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1519 =
  let name = "n_1519" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1520 =
  let name = "n_1520" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1521 =
  let name = "n_1521" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1522 =
  let name = "n_1522" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1523 =
  let name = "n_1523" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1524 =
  let name = "n_1524" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1525 =
  let name = "n_1525" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1526 =
  let name = "n_1526" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1527 =
  let name = "n_1527" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1528 =
  let name = "n_1528" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1529 =
  let name = "n_1529" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1530 =
  let name = "n_1530" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (global "ExGntd")) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1531 =
  let name = "n_1531" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (global "ExGntd")) (const (boolc false))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1532 =
  let name = "n_1532" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (global "ExGntd")) (const (boolc false))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1533 =
  let name = "n_1533" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (global "ExGntd")) (const (boolc false))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1534 =
  let name = "n_1534" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (global "ExGntd")) (const (boolc false))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1535 =
  let name = "n_1535" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (global "ExGntd")) (const (boolc false))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1536 =
  let name = "n_1536" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (global "ExGntd")) (const (boolc false))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1537 =
  let name = "n_1537" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (global "ExGntd")) (const (boolc false))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1538 =
  let name = "n_1538" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (global "ExGntd")) (const (boolc false))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1539 =
  let name = "n_1539" in
  let params = [] in
  let formula = (imply (eqn (var (global "ExGntd")) (const (boolc false))) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1540 =
  let name = "n_1540" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1541 =
  let name = "n_1541" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1542 =
  let name = "n_1542" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1543 =
  let name = "n_1543" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1544 =
  let name = "n_1544" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1545 =
  let name = "n_1545" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1546 =
  let name = "n_1546" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1547 =
  let name = "n_1547" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1548 =
  let name = "n_1548" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1549 =
  let name = "n_1549" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1550 =
  let name = "n_1550" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1551 =
  let name = "n_1551" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1552 =
  let name = "n_1552" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1553 =
  let name = "n_1553" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1554 =
  let name = "n_1554" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1555 =
  let name = "n_1555" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1556 =
  let name = "n_1556" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1557 =
  let name = "n_1557" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1558 =
  let name = "n_1558" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1559 =
  let name = "n_1559" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1560 =
  let name = "n_1560" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1561 =
  let name = "n_1561" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1562 =
  let name = "n_1562" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1563 =
  let name = "n_1563" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1564 =
  let name = "n_1564" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1565 =
  let name = "n_1565" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1566 =
  let name = "n_1566" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1567 =
  let name = "n_1567" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1568 =
  let name = "n_1568" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1569 =
  let name = "n_1569" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1570 =
  let name = "n_1570" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1571 =
  let name = "n_1571" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_1572 =
  let name = "n_1572" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (global "CurCmd")) (const _Empty))) in
  prop name params formula

let n_1573 =
  let name = "n_1573" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1574 =
  let name = "n_1574" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1575 =
  let name = "n_1575" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1576 =
  let name = "n_1576" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1577 =
  let name = "n_1577" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1578 =
  let name = "n_1578" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))) in
  prop name params formula

let n_1579 =
  let name = "n_1579" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1580 =
  let name = "n_1580" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1581 =
  let name = "n_1581" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1582 =
  let name = "n_1582" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1583 =
  let name = "n_1583" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_1584 =
  let name = "n_1584" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "CurCmd")) (const _Empty))) in
  prop name params formula

let n_1585 =
  let name = "n_1585" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1586 =
  let name = "n_1586" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1587 =
  let name = "n_1587" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1588 =
  let name = "n_1588" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1589 =
  let name = "n_1589" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1590 =
  let name = "n_1590" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1591 =
  let name = "n_1591" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1592 =
  let name = "n_1592" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1593 =
  let name = "n_1593" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1594 =
  let name = "n_1594" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1595 =
  let name = "n_1595" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1596 =
  let name = "n_1596" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1597 =
  let name = "n_1597" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1598 =
  let name = "n_1598" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1599 =
  let name = "n_1599" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1600 =
  let name = "n_1600" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1601 =
  let name = "n_1601" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1602 =
  let name = "n_1602" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1603 =
  let name = "n_1603" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1604 =
  let name = "n_1604" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1605 =
  let name = "n_1605" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1606 =
  let name = "n_1606" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1607 =
  let name = "n_1607" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1608 =
  let name = "n_1608" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1609 =
  let name = "n_1609" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1610 =
  let name = "n_1610" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1611 =
  let name = "n_1611" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1612 =
  let name = "n_1612" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1613 =
  let name = "n_1613" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1614 =
  let name = "n_1614" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1615 =
  let name = "n_1615" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1616 =
  let name = "n_1616" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1617 =
  let name = "n_1617" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1618 =
  let name = "n_1618" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1619 =
  let name = "n_1619" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1620 =
  let name = "n_1620" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1621 =
  let name = "n_1621" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1622 =
  let name = "n_1622" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1623 =
  let name = "n_1623" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1624 =
  let name = "n_1624" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1625 =
  let name = "n_1625" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1626 =
  let name = "n_1626" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1627 =
  let name = "n_1627" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1628 =
  let name = "n_1628" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1629 =
  let name = "n_1629" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1630 =
  let name = "n_1630" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1631 =
  let name = "n_1631" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1632 =
  let name = "n_1632" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1633 =
  let name = "n_1633" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1634 =
  let name = "n_1634" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))) in
  prop name params formula

let n_1635 =
  let name = "n_1635" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1636 =
  let name = "n_1636" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1637 =
  let name = "n_1637" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1638 =
  let name = "n_1638" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1639 =
  let name = "n_1639" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1640 =
  let name = "n_1640" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1641 =
  let name = "n_1641" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1642 =
  let name = "n_1642" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1643 =
  let name = "n_1643" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1644 =
  let name = "n_1644" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1645 =
  let name = "n_1645" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_1646 =
  let name = "n_1646" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1647 =
  let name = "n_1647" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1648 =
  let name = "n_1648" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_1649 =
  let name = "n_1649" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1650 =
  let name = "n_1650" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1651 =
  let name = "n_1651" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))) in
  prop name params formula

let n_1652 =
  let name = "n_1652" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1653 =
  let name = "n_1653" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1654 =
  let name = "n_1654" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1655 =
  let name = "n_1655" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1656 =
  let name = "n_1656" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1657 =
  let name = "n_1657" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1658 =
  let name = "n_1658" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1659 =
  let name = "n_1659" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (global "CurCmd")) (const _ReqS)))) in
  prop name params formula

let n_1660 =
  let name = "n_1660" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1661 =
  let name = "n_1661" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1662 =
  let name = "n_1662" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1663 =
  let name = "n_1663" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1664 =
  let name = "n_1664" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1665 =
  let name = "n_1665" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_1666 =
  let name = "n_1666" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_1667 =
  let name = "n_1667" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1668 =
  let name = "n_1668" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1669 =
  let name = "n_1669" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1670 =
  let name = "n_1670" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1671 =
  let name = "n_1671" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))) in
  prop name params formula

let n_1672 =
  let name = "n_1672" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1673 =
  let name = "n_1673" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1674 =
  let name = "n_1674" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1675 =
  let name = "n_1675" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1676 =
  let name = "n_1676" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1677 =
  let name = "n_1677" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1678 =
  let name = "n_1678" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1679 =
  let name = "n_1679" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1680 =
  let name = "n_1680" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1681 =
  let name = "n_1681" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1682 =
  let name = "n_1682" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1683 =
  let name = "n_1683" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1684 =
  let name = "n_1684" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1685 =
  let name = "n_1685" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1686 =
  let name = "n_1686" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1687 =
  let name = "n_1687" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1688 =
  let name = "n_1688" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1689 =
  let name = "n_1689" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1690 =
  let name = "n_1690" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))) in
  prop name params formula

let n_1691 =
  let name = "n_1691" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1692 =
  let name = "n_1692" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1693 =
  let name = "n_1693" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1694 =
  let name = "n_1694" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1695 =
  let name = "n_1695" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1696 =
  let name = "n_1696" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1697 =
  let name = "n_1697" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1698 =
  let name = "n_1698" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1699 =
  let name = "n_1699" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1700 =
  let name = "n_1700" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1701 =
  let name = "n_1701" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1702 =
  let name = "n_1702" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1703 =
  let name = "n_1703" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1704 =
  let name = "n_1704" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1705 =
  let name = "n_1705" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1706 =
  let name = "n_1706" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1707 =
  let name = "n_1707" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1708 =
  let name = "n_1708" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1709 =
  let name = "n_1709" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1710 =
  let name = "n_1710" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1711 =
  let name = "n_1711" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1712 =
  let name = "n_1712" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1713 =
  let name = "n_1713" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))) in
  prop name params formula

let n_1714 =
  let name = "n_1714" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1715 =
  let name = "n_1715" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1716 =
  let name = "n_1716" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1717 =
  let name = "n_1717" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1718 =
  let name = "n_1718" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1719 =
  let name = "n_1719" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1720 =
  let name = "n_1720" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1721 =
  let name = "n_1721" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1722 =
  let name = "n_1722" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1723 =
  let name = "n_1723" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1724 =
  let name = "n_1724" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1725 =
  let name = "n_1725" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1726 =
  let name = "n_1726" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1727 =
  let name = "n_1727" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1728 =
  let name = "n_1728" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1729 =
  let name = "n_1729" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1730 =
  let name = "n_1730" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1731 =
  let name = "n_1731" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1732 =
  let name = "n_1732" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1733 =
  let name = "n_1733" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1734 =
  let name = "n_1734" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1735 =
  let name = "n_1735" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1736 =
  let name = "n_1736" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1737 =
  let name = "n_1737" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1738 =
  let name = "n_1738" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1739 =
  let name = "n_1739" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1740 =
  let name = "n_1740" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1741 =
  let name = "n_1741" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1742 =
  let name = "n_1742" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1743 =
  let name = "n_1743" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1744 =
  let name = "n_1744" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1745 =
  let name = "n_1745" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1746 =
  let name = "n_1746" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1747 =
  let name = "n_1747" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1748 =
  let name = "n_1748" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1749 =
  let name = "n_1749" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))) in
  prop name params formula

let n_1750 =
  let name = "n_1750" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1751 =
  let name = "n_1751" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))) in
  prop name params formula

let n_1752 =
  let name = "n_1752" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1753 =
  let name = "n_1753" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1754 =
  let name = "n_1754" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1755 =
  let name = "n_1755" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1756 =
  let name = "n_1756" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1757 =
  let name = "n_1757" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1758 =
  let name = "n_1758" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1759 =
  let name = "n_1759" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1760 =
  let name = "n_1760" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(neg (eqn (var (global "MemData")) (var (global "AuxData")))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1761 =
  let name = "n_1761" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (global "MemData")) (var (global "AuxData")))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1762 =
  let name = "n_1762" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (global "MemData")) (var (global "AuxData")))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1763 =
  let name = "n_1763" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (global "MemData")) (var (global "AuxData")))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1764 =
  let name = "n_1764" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (neg (eqn (var (global "MemData")) (var (global "AuxData")))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1765 =
  let name = "n_1765" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (global "MemData")) (var (global "AuxData")))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1766 =
  let name = "n_1766" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (var (global "MemData")) (var (global "AuxData")))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1767 =
  let name = "n_1767" in
  let params = [] in
  let formula = (imply (neg (eqn (var (global "MemData")) (var (global "AuxData")))) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1768 =
  let name = "n_1768" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1769 =
  let name = "n_1769" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1770 =
  let name = "n_1770" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1771 =
  let name = "n_1771" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1772 =
  let name = "n_1772" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1773 =
  let name = "n_1773" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1774 =
  let name = "n_1774" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1775 =
  let name = "n_1775" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1776 =
  let name = "n_1776" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1777 =
  let name = "n_1777" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1778 =
  let name = "n_1778" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1779 =
  let name = "n_1779" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1780 =
  let name = "n_1780" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1781 =
  let name = "n_1781" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1782 =
  let name = "n_1782" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1783 =
  let name = "n_1783" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1784 =
  let name = "n_1784" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1785 =
  let name = "n_1785" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1786 =
  let name = "n_1786" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1787 =
  let name = "n_1787" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1788 =
  let name = "n_1788" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1789 =
  let name = "n_1789" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1790 =
  let name = "n_1790" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1791 =
  let name = "n_1791" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1792 =
  let name = "n_1792" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1793 =
  let name = "n_1793" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1794 =
  let name = "n_1794" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1795 =
  let name = "n_1795" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1796 =
  let name = "n_1796" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1797 =
  let name = "n_1797" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1798 =
  let name = "n_1798" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1799 =
  let name = "n_1799" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1800 =
  let name = "n_1800" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1801 =
  let name = "n_1801" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1802 =
  let name = "n_1802" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1803 =
  let name = "n_1803" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1804 =
  let name = "n_1804" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1805 =
  let name = "n_1805" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1806 =
  let name = "n_1806" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1807 =
  let name = "n_1807" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1808 =
  let name = "n_1808" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1809 =
  let name = "n_1809" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1810 =
  let name = "n_1810" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1811 =
  let name = "n_1811" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1812 =
  let name = "n_1812" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1813 =
  let name = "n_1813" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1814 =
  let name = "n_1814" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1815 =
  let name = "n_1815" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1816 =
  let name = "n_1816" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1817 =
  let name = "n_1817" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1818 =
  let name = "n_1818" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1819 =
  let name = "n_1819" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1820 =
  let name = "n_1820" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1821 =
  let name = "n_1821" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1822 =
  let name = "n_1822" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1823 =
  let name = "n_1823" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1824 =
  let name = "n_1824" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1825 =
  let name = "n_1825" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1826 =
  let name = "n_1826" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1827 =
  let name = "n_1827" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_1828 =
  let name = "n_1828" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1829 =
  let name = "n_1829" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1830 =
  let name = "n_1830" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1831 =
  let name = "n_1831" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1832 =
  let name = "n_1832" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_1833 =
  let name = "n_1833" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1834 =
  let name = "n_1834" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1835 =
  let name = "n_1835" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1836 =
  let name = "n_1836" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1837 =
  let name = "n_1837" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1838 =
  let name = "n_1838" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1839 =
  let name = "n_1839" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1840 =
  let name = "n_1840" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1841 =
  let name = "n_1841" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1842 =
  let name = "n_1842" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1843 =
  let name = "n_1843" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1844 =
  let name = "n_1844" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1845 =
  let name = "n_1845" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1846 =
  let name = "n_1846" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1847 =
  let name = "n_1847" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1848 =
  let name = "n_1848" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1849 =
  let name = "n_1849" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1850 =
  let name = "n_1850" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1851 =
  let name = "n_1851" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1852 =
  let name = "n_1852" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1853 =
  let name = "n_1853" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1854 =
  let name = "n_1854" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1855 =
  let name = "n_1855" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1856 =
  let name = "n_1856" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1857 =
  let name = "n_1857" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1858 =
  let name = "n_1858" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1859 =
  let name = "n_1859" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1860 =
  let name = "n_1860" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1861 =
  let name = "n_1861" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1862 =
  let name = "n_1862" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1863 =
  let name = "n_1863" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1864 =
  let name = "n_1864" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1865 =
  let name = "n_1865" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1866 =
  let name = "n_1866" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1867 =
  let name = "n_1867" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "CurCmd")) (const _ReqE)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1868 =
  let name = "n_1868" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "CurCmd")) (const _ReqE)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1869 =
  let name = "n_1869" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "CurCmd")) (const _ReqE)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1870 =
  let name = "n_1870" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _Empty))]) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S))))) in
  prop name params formula

let n_1871 =
  let name = "n_1871" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1872 =
  let name = "n_1872" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _Empty))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1873 =
  let name = "n_1873" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1874 =
  let name = "n_1874" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (global "ExGntd")) (const (boolc false)))) in
  prop name params formula

let n_1875 =
  let name = "n_1875" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1876 =
  let name = "n_1876" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (global "MemData")) (var (global "AuxData")))) in
  prop name params formula

let n_1877 =
  let name = "n_1877" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1878 =
  let name = "n_1878" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _Empty))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1879 =
  let name = "n_1879" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1880 =
  let name = "n_1880" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1881 =
  let name = "n_1881" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1882 =
  let name = "n_1882" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1883 =
  let name = "n_1883" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1884 =
  let name = "n_1884" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1885 =
  let name = "n_1885" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1886 =
  let name = "n_1886" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1887 =
  let name = "n_1887" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1888 =
  let name = "n_1888" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1889 =
  let name = "n_1889" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1890 =
  let name = "n_1890" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1891 =
  let name = "n_1891" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1892 =
  let name = "n_1892" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1893 =
  let name = "n_1893" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1894 =
  let name = "n_1894" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1895 =
  let name = "n_1895" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1896 =
  let name = "n_1896" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1897 =
  let name = "n_1897" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1898 =
  let name = "n_1898" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1899 =
  let name = "n_1899" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1900 =
  let name = "n_1900" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1901 =
  let name = "n_1901" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1902 =
  let name = "n_1902" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))) in
  prop name params formula

let n_1903 =
  let name = "n_1903" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))))) in
  prop name params formula

let n_1904 =
  let name = "n_1904" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1905 =
  let name = "n_1905" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1906 =
  let name = "n_1906" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1907 =
  let name = "n_1907" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1908 =
  let name = "n_1908" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1909 =
  let name = "n_1909" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))); (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1910 =
  let name = "n_1910" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1911 =
  let name = "n_1911" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1912 =
  let name = "n_1912" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1913 =
  let name = "n_1913" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_1914 =
  let name = "n_1914" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1915 =
  let name = "n_1915" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1916 =
  let name = "n_1916" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1917 =
  let name = "n_1917" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1918 =
  let name = "n_1918" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_1919 =
  let name = "n_1919" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1920 =
  let name = "n_1920" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1921 =
  let name = "n_1921" in
  let params = [paramdef "i" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))) in
  prop name params formula

let n_1922 =
  let name = "n_1922" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1923 =
  let name = "n_1923" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1924 =
  let name = "n_1924" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1925 =
  let name = "n_1925" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1926 =
  let name = "n_1926" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1927 =
  let name = "n_1927" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1928 =
  let name = "n_1928" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1929 =
  let name = "n_1929" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1930 =
  let name = "n_1930" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1931 =
  let name = "n_1931" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1932 =
  let name = "n_1932" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1933 =
  let name = "n_1933" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1934 =
  let name = "n_1934" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1935 =
  let name = "n_1935" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1936 =
  let name = "n_1936" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1937 =
  let name = "n_1937" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1938 =
  let name = "n_1938" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1939 =
  let name = "n_1939" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1940 =
  let name = "n_1940" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1941 =
  let name = "n_1941" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1942 =
  let name = "n_1942" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1943 =
  let name = "n_1943" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1944 =
  let name = "n_1944" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1945 =
  let name = "n_1945" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1946 =
  let name = "n_1946" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1947 =
  let name = "n_1947" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1948 =
  let name = "n_1948" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1949 =
  let name = "n_1949" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1950 =
  let name = "n_1950" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1951 =
  let name = "n_1951" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1952 =
  let name = "n_1952" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1953 =
  let name = "n_1953" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1954 =
  let name = "n_1954" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_1955 =
  let name = "n_1955" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1956 =
  let name = "n_1956" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1957 =
  let name = "n_1957" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1958 =
  let name = "n_1958" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_1959 =
  let name = "n_1959" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1960 =
  let name = "n_1960" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1961 =
  let name = "n_1961" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_1962 =
  let name = "n_1962" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_1963 =
  let name = "n_1963" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_1964 =
  let name = "n_1964" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1965 =
  let name = "n_1965" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_1966 =
  let name = "n_1966" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1967 =
  let name = "n_1967" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_1968 =
  let name = "n_1968" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_1969 =
  let name = "n_1969" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_1970 =
  let name = "n_1970" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) in
  prop name params formula

let n_1971 =
  let name = "n_1971" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_1972 =
  let name = "n_1972" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_1973 =
  let name = "n_1973" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1974 =
  let name = "n_1974" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_1975 =
  let name = "n_1975" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1976 =
  let name = "n_1976" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_1977 =
  let name = "n_1977" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_1978 =
  let name = "n_1978" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_1979 =
  let name = "n_1979" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1980 =
  let name = "n_1980" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1981 =
  let name = "n_1981" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1982 =
  let name = "n_1982" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_1983 =
  let name = "n_1983" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1984 =
  let name = "n_1984" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1985 =
  let name = "n_1985" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1986 =
  let name = "n_1986" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1987 =
  let name = "n_1987" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1988 =
  let name = "n_1988" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_1989 =
  let name = "n_1989" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_1990 =
  let name = "n_1990" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1991 =
  let name = "n_1991" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])) (var (global "AuxData")))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_1992 =
  let name = "n_1992" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1993 =
  let name = "n_1993" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1994 =
  let name = "n_1994" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1995 =
  let name = "n_1995" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_1996 =
  let name = "n_1996" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (neg (eqn (var (global "CurCmd")) (const _ReqS))))) in
  prop name params formula

let n_1997 =
  let name = "n_1997" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "CurCmd")) (const _ReqE)))) in
  prop name params formula

let n_1998 =
  let name = "n_1998" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_1999 =
  let name = "n_1999" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_2000 =
  let name = "n_2000" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_2001 =
  let name = "n_2001" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _ReqS))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_2002 =
  let name = "n_2002" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (global "CurCmd")) (const _ReqS))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_2003 =
  let name = "n_2003" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_2004 =
  let name = "n_2004" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_2005 =
  let name = "n_2005" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_2006 =
  let name = "n_2006" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_2007 =
  let name = "n_2007" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_2008 =
  let name = "n_2008" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_2009 =
  let name = "n_2009" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_2010 =
  let name = "n_2010" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_2011 =
  let name = "n_2011" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (global "ExGntd")) (const (boolc false)))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_2012 =
  let name = "n_2012" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS))))) in
  prop name params formula

let n_2013 =
  let name = "n_2013" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_2014 =
  let name = "n_2014" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_2015 =
  let name = "n_2015" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_2016 =
  let name = "n_2016" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)))) in
  prop name params formula

let n_2017 =
  let name = "n_2017" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv))))) in
  prop name params formula

let n_2018 =
  let name = "n_2018" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_2019 =
  let name = "n_2019" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))))) in
  prop name params formula

let n_2020 =
  let name = "n_2020" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty)))) in
  prop name params formula

let n_2021 =
  let name = "n_2021" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (neg (eqn (var (global "CurCmd")) (const _Empty)))) in
  prop name params formula

let n_2022 =
  let name = "n_2022" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("InvSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_2023 =
  let name = "n_2023" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false))))) in
  prop name params formula

let n_2024 =
  let name = "n_2024" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (neg (eqn (var (global "MemData")) (var (global "AuxData"))))]) (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc true))))) in
  prop name params formula

let n_2025 =
  let name = "n_2025" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (neg (eqn (var (global "CurCmd")) (const _Empty))))) in
  prop name params formula

let n_2026 =
  let name = "n_2026" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (eqn (var (global "ExGntd")) (const (boolc false))))) in
  prop name params formula

let n_2027 =
  let name = "n_2027" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (andList [(eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))); (eqn (var (arr [("ShrSet", [paramref "i"])])) (const (boolc false)))]) (eqn (var (global "MemData")) (var (global "AuxData"))))) in
  prop name params formula

let n_2028 =
  let name = "n_2028" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_2029 =
  let name = "n_2029" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E)))) in
  prop name params formula

let n_2030 =
  let name = "n_2030" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _S)))) in
  prop name params formula

let n_2031 =
  let name = "n_2031" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I))) in
  prop name params formula

let n_2032 =
  let name = "n_2032" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE))))) in
  prop name params formula

let n_2033 =
  let name = "n_2033" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntE)))) in
  prop name params formula

let n_2034 =
  let name = "n_2034" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _GntS)))) in
  prop name params formula

let n_2035 =
  let name = "n_2035" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Inv)))) in
  prop name params formula

let n_2036 =
  let name = "n_2036" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (eqn (var (record [arr [("Chan2", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_2037 =
  let name = "n_2037" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (neg (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _InvAck)))) in
  prop name params formula

let n_2038 =
  let name = "n_2038" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (eqn (var (record [arr [("Chan3", [paramref "j"])]; global "Cmd"])) (const _Empty))) in
  prop name params formula

let n_2039 =
  let name = "n_2039" in
  let params = [paramdef "j" "NODE"] in
  let formula = (imply (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc true))) (eqn (var (arr [("InvSet", [paramref "j"])])) (const (boolc true)))) in
  prop name params formula

let n_DataProp =
  let name = "n_DataProp" in
  let params = [] in
  let formula = (andList [(imply (eqn (var (global "ExGntd")) (const (boolc false))) (eqn (var (global "MemData")) (var (global "AuxData")))); (forallFormula [paramdef "i" "NODE"] (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))))]) in
  prop name params formula

let properties = [ n_1; n_2; n_3; n_4; n_5; n_6; n_7; n_8; n_9; n_10; n_11; n_12; n_13; n_14; n_15; n_16; n_17; n_18; n_19; n_20; n_21; n_22; n_23; n_24; n_25; n_26; n_27; n_28; n_29; n_30; n_31; n_32; n_33; n_34; n_35; n_36; n_37; n_38; n_39; n_40; n_41; n_42; n_43; n_44; n_45; n_46; n_47; n_48; n_49; n_50; n_51; n_52; n_53; n_54; n_55; n_56; n_57; n_58; n_59; n_60; n_61; n_62; n_63; n_64; n_65; n_66; n_67; n_68; n_69; n_70; n_71; n_72; n_73; n_74; n_75; n_76; n_77; n_78; n_79; n_80; n_81; n_82; n_83; n_84; n_85; n_86; n_87; n_88; n_89; n_90; n_91; n_92; n_93; n_94; n_95; n_96; n_97; n_98; n_99; n_100; n_101; n_102; n_103; n_104; n_105; n_106; n_107; n_108; n_109; n_110; n_111; n_112; n_113; n_114; n_115; n_116; n_117; n_118; n_119; n_120; n_121; n_122; n_123; n_124; n_125; n_126; n_127; n_128; n_129; n_130; n_131; n_132; n_133; n_134; n_135; n_136; n_137; n_138; n_139; n_140; n_141; n_142; n_143; n_144; n_145; n_146; n_147; n_148; n_149; n_150; n_151; n_152; n_153; n_154; n_155; n_156; n_157; n_158; n_159; n_160; n_161; n_162; n_163; n_164; n_165; n_166; n_167; n_168; n_169; n_170; n_171; n_172; n_173; n_174; n_175; n_176; n_177; n_178; n_179; n_180; n_181; n_182; n_183; n_184; n_185; n_186; n_187; n_188; n_189; n_190; n_191; n_192; n_193; n_194; n_195; n_196; n_197; n_198; n_199; n_200; n_201; n_202; n_203; n_204; n_205; n_206; n_207; n_208; n_209; n_210; n_211; n_212; n_213; n_214; n_215; n_216; n_217; n_218; n_219; n_220; n_221; n_222; n_223; n_224; n_225; n_226; n_227; n_228; n_229; n_230; n_231; n_232; n_233; n_234; n_235; n_236; n_237; n_238; n_239; n_240; n_241; n_242; n_243; n_244; n_245; n_246; n_247; n_248; n_249; n_250; n_251; n_252; n_253; n_254; n_255; n_256; n_257; n_258; n_259; n_260; n_261; n_262; n_263; n_264; n_265; n_266; n_267; n_268; n_269; n_270; n_271; n_272; n_273; n_274; n_275; n_276; n_277; n_278; n_279; n_280; n_281; n_282; n_283; n_284; n_285; n_286; n_287; n_288; n_289; n_290; n_291; n_292; n_293; n_294; n_295; n_296; n_297; n_298; n_299; n_300; n_301; n_302; n_303; n_304; n_305; n_306; n_307; n_308; n_309; n_310; n_311; n_312; n_313; n_314; n_315; n_316; n_317; n_318; n_319; n_320; n_321; n_322; n_323; n_324; n_325; n_326; n_327; n_328; n_329; n_330; n_331; n_332; n_333; n_334; n_335; n_336; n_337; n_338; n_339; n_340; n_341; n_342; n_343; n_344; n_345; n_346; n_347; n_348; n_349; n_350; n_351; n_352; n_353; n_354; n_355; n_356; n_357; n_358; n_359; n_360; n_361; n_362; n_363; n_364; n_365; n_366; n_367; n_368; n_369; n_370; n_371; n_372; n_373; n_374; n_375; n_376; n_377; n_378; n_379; n_380; n_381; n_382; n_383; n_384; n_385; n_386; n_387; n_388; n_389; n_390; n_391; n_392; n_393; n_394; n_395; n_396; n_397; n_398; n_399; n_400; n_401; n_402; n_403; n_404; n_405; n_406; n_407; n_408; n_409; n_410; n_411; n_412; n_413; n_414; n_415; n_416; n_417; n_418; n_419; n_420; n_421; n_422; n_423; n_424; n_425; n_426; n_427; n_428; n_429; n_430; n_431; n_432; n_433; n_434; n_435; n_436; n_437; n_438; n_439; n_440; n_441; n_442; n_443; n_444; n_445; n_446; n_447; n_448; n_449; n_450; n_451; n_452; n_453; n_454; n_455; n_456; n_457; n_458; n_459; n_460; n_461; n_462; n_463; n_464; n_465; n_466; n_467; n_468; n_469; n_470; n_471; n_472; n_473; n_474; n_475; n_476; n_477; n_478; n_479; n_480; n_481; n_482; n_483; n_484; n_485; n_486; n_487; n_488; n_489; n_490; n_491; n_492; n_493; n_494; n_495; n_496; n_497; n_498; n_499; n_500; n_501; n_502; n_503; n_504; n_505; n_506; n_507; n_508; n_509; n_510; n_511; n_512; n_513; n_514; n_515; n_516; n_517; n_518; n_519; n_520; n_521; n_522; n_523; n_524; n_525; n_526; n_527; n_528; n_529; n_530; n_531; n_532; n_533; n_534; n_535; n_536; n_537; n_538; n_539; n_540; n_541; n_542; n_543; n_544; n_545; n_546; n_547; n_548; n_549; n_550; n_551; n_552; n_553; n_554; n_555; n_556; n_557; n_558; n_559; n_560; n_561; n_562; n_563; n_564; n_565; n_566; n_567; n_568; n_569; n_570; n_571; n_572; n_573; n_574; n_575; n_576; n_577; n_578; n_579; n_580; n_581; n_582; n_583; n_584; n_585; n_586; n_587; n_588; n_589; n_590; n_591; n_592; n_593; n_594; n_595; n_596; n_597; n_598; n_599; n_600; n_601; n_602; n_603; n_604; n_605; n_606; n_607; n_608; n_609; n_610; n_611; n_612; n_613; n_614; n_615; n_616; n_617; n_618; n_619; n_620; n_621; n_622; n_623; n_624; n_625; n_626; n_627; n_628; n_629; n_630; n_631; n_632; n_633; n_634; n_635; n_636; n_637; n_638; n_639; n_640; n_641; n_642; n_643; n_644; n_645; n_646; n_647; n_648; n_649; n_650; n_651; n_652; n_653; n_654; n_655; n_656; n_657; n_658; n_659; n_660; n_661; n_662; n_663; n_664; n_665; n_666; n_667; n_668; n_669; n_670; n_671; n_672; n_673; n_674; n_675; n_676; n_677; n_678; n_679; n_680; n_681; n_682; n_683; n_684; n_685; n_686; n_687; n_688; n_689; n_690; n_691; n_692; n_693; n_694; n_695; n_696; n_697; n_698; n_699; n_700; n_701; n_702; n_703; n_704; n_705; n_706; n_707; n_708; n_709; n_710; n_711; n_712; n_713; n_714; n_715; n_716; n_717; n_718; n_719; n_720; n_721; n_722; n_723; n_724; n_725; n_726; n_727; n_728; n_729; n_730; n_731; n_732; n_733; n_734; n_735; n_736; n_737; n_738; n_739; n_740; n_741; n_742; n_743; n_744; n_745; n_746; n_747; n_748; n_749; n_750; n_751; n_752; n_753; n_754; n_755; n_756; n_757; n_758; n_759; n_760; n_761; n_762; n_763; n_764; n_765; n_766; n_767; n_768; n_769; n_770; n_771; n_772; n_773; n_774; n_775; n_776; n_777; n_778; n_779; n_780; n_781; n_782; n_783; n_784; n_785; n_786; n_787; n_788; n_789; n_790; n_791; n_792; n_793; n_794; n_795; n_796; n_797; n_798; n_799; n_800; n_801; n_802; n_803; n_804; n_805; n_806; n_807; n_808; n_809; n_810; n_811; n_812; n_813; n_814; n_815; n_816; n_817; n_818; n_819; n_820; n_821; n_822; n_823; n_824; n_825; n_826; n_827; n_828; n_829; n_830; n_831; n_832; n_833; n_834; n_835; n_836; n_837; n_838; n_839; n_840; n_841; n_842; n_843; n_844; n_845; n_846; n_847; n_848; n_849; n_850; n_851; n_852; n_853; n_854; n_855; n_856; n_857; n_858; n_859; n_860; n_861; n_862; n_863; n_864; n_865; n_866; n_867; n_868; n_869; n_870; n_871; n_872; n_873; n_874; n_875; n_876; n_877; n_878; n_879; n_880; n_881; n_882; n_883; n_884; n_885; n_886; n_887; n_888; n_889; n_890; n_891; n_892; n_893; n_894; n_895; n_896; n_897; n_898; n_899; n_900; n_901; n_902; n_903; n_904; n_905; n_906; n_907; n_908; n_909; n_910; n_911; n_912; n_913; n_914; n_915; n_916; n_917; n_918; n_919; n_920; n_921; n_922; n_923; n_924; n_925; n_926; n_927; n_928; n_929; n_930; n_931; n_932; n_933; n_934; n_935; n_936; n_937; n_938; n_939; n_940; n_941; n_942; n_943; n_944; n_945; n_946; n_947; n_948; n_949; n_950; n_951; n_952; n_953; n_954; n_955; n_956; n_957; n_958; n_959; n_960; n_961; n_962; n_963; n_964; n_965; n_966; n_967; n_968; n_969; n_970; n_971; n_972; n_973; n_974; n_975; n_976; n_977; n_978; n_979; n_980; n_981; n_982; n_983; n_984; n_985; n_986; n_987; n_988; n_989; n_990; n_991; n_992; n_993; n_994; n_995; n_996; n_997; n_998; n_999; n_1000; n_1001; n_1002; n_1003; n_1004; n_1005; n_1006; n_1007; n_1008; n_1009; n_1010; n_1011; n_1012; n_1013; n_1014; n_1015; n_1016; n_1017; n_1018; n_1019; n_1020; n_1021; n_1022; n_1023; n_1024; n_1025; n_1026; n_1027; n_1028; n_1029; n_1030; n_1031; n_1032; n_1033; n_1034; n_1035; n_1036; n_1037; n_1038; n_1039; n_1040; n_1041; n_1042; n_1043; n_1044; n_1045; n_1046; n_1047; n_1048; n_1049; n_1050; n_1051; n_1052; n_1053; n_1054; n_1055; n_1056; n_1057; n_1058; n_1059; n_1060; n_1061; n_1062; n_1063; n_1064; n_1065; n_1066; n_1067; n_1068; n_1069; n_1070; n_1071; n_1072; n_1073; n_1074; n_1075; n_1076; n_1077; n_1078; n_1079; n_1080; n_1081; n_1082; n_1083; n_1084; n_1085; n_1086; n_1087; n_1088; n_1089; n_1090; n_1091; n_1092; n_1093; n_1094; n_1095; n_1096; n_1097; n_1098; n_1099; n_1100; n_1101; n_1102; n_1103; n_1104; n_1105; n_1106; n_1107; n_1108; n_1109; n_1110; n_1111; n_1112; n_1113; n_1114; n_1115; n_1116; n_1117; n_1118; n_1119; n_1120; n_1121; n_1122; n_1123; n_1124; n_1125; n_1126; n_1127; n_1128; n_1129; n_1130; n_1131; n_1132; n_1133; n_1134; n_1135; n_1136; n_1137; n_1138; n_1139; n_1140; n_1141; n_1142; n_1143; n_1144; n_1145; n_1146; n_1147; n_1148; n_1149; n_1150; n_1151; n_1152; n_1153; n_1154; n_1155; n_1156; n_1157; n_1158; n_1159; n_1160; n_1161; n_1162; n_1163; n_1164; n_1165; n_1166; n_1167; n_1168; n_1169; n_1170; n_1171; n_1172; n_1173; n_1174; n_1175; n_1176; n_1177; n_1178; n_1179; n_1180; n_1181; n_1182; n_1183; n_1184; n_1185; n_1186; n_1187; n_1188; n_1189; n_1190; n_1191; n_1192; n_1193; n_1194; n_1195; n_1196; n_1197; n_1198; n_1199; n_1200; n_1201; n_1202; n_1203; n_1204; n_1205; n_1206; n_1207; n_1208; n_1209; n_1210; n_1211; n_1212; n_1213; n_1214; n_1215; n_1216; n_1217; n_1218; n_1219; n_1220; n_1221; n_1222; n_1223; n_1224; n_1225; n_1226; n_1227; n_1228; n_1229; n_1230; n_1231; n_1232; n_1233; n_1234; n_1235; n_1236; n_1237; n_1238; n_1239; n_1240; n_1241; n_1242; n_1243; n_1244; n_1245; n_1246; n_1247; n_1248; n_1249; n_1250; n_1251; n_1252; n_1253; n_1254; n_1255; n_1256; n_1257; n_1258; n_1259; n_1260; n_1261; n_1262; n_1263; n_1264; n_1265; n_1266; n_1267; n_1268; n_1269; n_1270; n_1271; n_1272; n_1273; n_1274; n_1275; n_1276; n_1277; n_1278; n_1279; n_1280; n_1281; n_1282; n_1283; n_1284; n_1285; n_1286; n_1287; n_1288; n_1289; n_1290; n_1291; n_1292; n_1293; n_1294; n_1295; n_1296; n_1297; n_1298; n_1299; n_1300; n_1301; n_1302; n_1303; n_1304; n_1305; n_1306; n_1307; n_1308; n_1309; n_1310; n_1311; n_1312; n_1313; n_1314; n_1315; n_1316; n_1317; n_1318; n_1319; n_1320; n_1321; n_1322; n_1323; n_1324; n_1325; n_1326; n_1327; n_1328; n_1329; n_1330; n_1331; n_1332; n_1333; n_1334; n_1335; n_1336; n_1337; n_1338; n_1339; n_1340; n_1341; n_1342; n_1343; n_1344; n_1345; n_1346; n_1347; n_1348; n_1349; n_1350; n_1351; n_1352; n_1353; n_1354; n_1355; n_1356; n_1357; n_1358; n_1359; n_1360; n_1361; n_1362; n_1363; n_1364; n_1365; n_1366; n_1367; n_1368; n_1369; n_1370; n_1371; n_1372; n_1373; n_1374; n_1375; n_1376; n_1377; n_1378; n_1379; n_1380; n_1381; n_1382; n_1383; n_1384; n_1385; n_1386; n_1387; n_1388; n_1389; n_1390; n_1391; n_1392; n_1393; n_1394; n_1395; n_1396; n_1397; n_1398; n_1399; n_1400; n_1401; n_1402; n_1403; n_1404; n_1405; n_1406; n_1407; n_1408; n_1409; n_1410; n_1411; n_1412; n_1413; n_1414; n_1415; n_1416; n_1417; n_1418; n_1419; n_1420; n_1421; n_1422; n_1423; n_1424; n_1425; n_1426; n_1427; n_1428; n_1429; n_1430; n_1431; n_1432; n_1433; n_1434; n_1435; n_1436; n_1437; n_1438; n_1439; n_1440; n_1441; n_1442; n_1443; n_1444; n_1445; n_1446; n_1447; n_1448; n_1449; n_1450; n_1451; n_1452; n_1453; n_1454; n_1455; n_1456; n_1457; n_1458; n_1459; n_1460; n_1461; n_1462; n_1463; n_1464; n_1465; n_1466; n_1467; n_1468; n_1469; n_1470; n_1471; n_1472; n_1473; n_1474; n_1475; n_1476; n_1477; n_1478; n_1479; n_1480; n_1481; n_1482; n_1483; n_1484; n_1485; n_1486; n_1487; n_1488; n_1489; n_1490; n_1491; n_1492; n_1493; n_1494; n_1495; n_1496; n_1497; n_1498; n_1499; n_1500; n_1501; n_1502; n_1503; n_1504; n_1505; n_1506; n_1507; n_1508; n_1509; n_1510; n_1511; n_1512; n_1513; n_1514; n_1515; n_1516; n_1517; n_1518; n_1519; n_1520; n_1521; n_1522; n_1523; n_1524; n_1525; n_1526; n_1527; n_1528; n_1529; n_1530; n_1531; n_1532; n_1533; n_1534; n_1535; n_1536; n_1537; n_1538; n_1539; n_1540; n_1541; n_1542; n_1543; n_1544; n_1545; n_1546; n_1547; n_1548; n_1549; n_1550; n_1551; n_1552; n_1553; n_1554; n_1555; n_1556; n_1557; n_1558; n_1559; n_1560; n_1561; n_1562; n_1563; n_1564; n_1565; n_1566; n_1567; n_1568; n_1569; n_1570; n_1571; n_1572; n_1573; n_1574; n_1575; n_1576; n_1577; n_1578; n_1579; n_1580; n_1581; n_1582; n_1583; n_1584; n_1585; n_1586; n_1587; n_1588; n_1589; n_1590; n_1591; n_1592; n_1593; n_1594; n_1595; n_1596; n_1597; n_1598; n_1599; n_1600; n_1601; n_1602; n_1603; n_1604; n_1605; n_1606; n_1607; n_1608; n_1609; n_1610; n_1611; n_1612; n_1613; n_1614; n_1615; n_1616; n_1617; n_1618; n_1619; n_1620; n_1621; n_1622; n_1623; n_1624; n_1625; n_1626; n_1627; n_1628; n_1629; n_1630; n_1631; n_1632; n_1633; n_1634; n_1635; n_1636; n_1637; n_1638; n_1639; n_1640; n_1641; n_1642; n_1643; n_1644; n_1645; n_1646; n_1647; n_1648; n_1649; n_1650; n_1651; n_1652; n_1653; n_1654; n_1655; n_1656; n_1657; n_1658; n_1659; n_1660; n_1661; n_1662; n_1663; n_1664; n_1665; n_1666; n_1667; n_1668; n_1669; n_1670; n_1671; n_1672; n_1673; n_1674; n_1675; n_1676; n_1677; n_1678; n_1679; n_1680; n_1681; n_1682; n_1683; n_1684; n_1685; n_1686; n_1687; n_1688; n_1689; n_1690; n_1691; n_1692; n_1693; n_1694; n_1695; n_1696; n_1697; n_1698; n_1699; n_1700; n_1701; n_1702; n_1703; n_1704; n_1705; n_1706; n_1707; n_1708; n_1709; n_1710; n_1711; n_1712; n_1713; n_1714; n_1715; n_1716; n_1717; n_1718; n_1719; n_1720; n_1721; n_1722; n_1723; n_1724; n_1725; n_1726; n_1727; n_1728; n_1729; n_1730; n_1731; n_1732; n_1733; n_1734; n_1735; n_1736; n_1737; n_1738; n_1739; n_1740; n_1741; n_1742; n_1743; n_1744; n_1745; n_1746; n_1747; n_1748; n_1749; n_1750; n_1751; n_1752; n_1753; n_1754; n_1755; n_1756; n_1757; n_1758; n_1759; n_1760; n_1761; n_1762; n_1763; n_1764; n_1765; n_1766; n_1767; n_1768; n_1769; n_1770; n_1771; n_1772; n_1773; n_1774; n_1775; n_1776; n_1777; n_1778; n_1779; n_1780; n_1781; n_1782; n_1783; n_1784; n_1785; n_1786; n_1787; n_1788; n_1789; n_1790; n_1791; n_1792; n_1793; n_1794; n_1795; n_1796; n_1797; n_1798; n_1799; n_1800; n_1801; n_1802; n_1803; n_1804; n_1805; n_1806; n_1807; n_1808; n_1809; n_1810; n_1811; n_1812; n_1813; n_1814; n_1815; n_1816; n_1817; n_1818; n_1819; n_1820; n_1821; n_1822; n_1823; n_1824; n_1825; n_1826; n_1827; n_1828; n_1829; n_1830; n_1831; n_1832; n_1833; n_1834; n_1835; n_1836; n_1837; n_1838; n_1839; n_1840; n_1841; n_1842; n_1843; n_1844; n_1845; n_1846; n_1847; n_1848; n_1849; n_1850; n_1851; n_1852; n_1853; n_1854; n_1855; n_1856; n_1857; n_1858; n_1859; n_1860; n_1861; n_1862; n_1863; n_1864; n_1865; n_1866; n_1867; n_1868; n_1869; n_1870; n_1871; n_1872; n_1873; n_1874; n_1875; n_1876; n_1877; n_1878; n_1879; n_1880; n_1881; n_1882; n_1883; n_1884; n_1885; n_1886; n_1887; n_1888; n_1889; n_1890; n_1891; n_1892; n_1893; n_1894; n_1895; n_1896; n_1897; n_1898; n_1899; n_1900; n_1901; n_1902; n_1903; n_1904; n_1905; n_1906; n_1907; n_1908; n_1909; n_1910; n_1911; n_1912; n_1913; n_1914; n_1915; n_1916; n_1917; n_1918; n_1919; n_1920; n_1921; n_1922; n_1923; n_1924; n_1925; n_1926; n_1927; n_1928; n_1929; n_1930; n_1931; n_1932; n_1933; n_1934; n_1935; n_1936; n_1937; n_1938; n_1939; n_1940; n_1941; n_1942; n_1943; n_1944; n_1945; n_1946; n_1947; n_1948; n_1949; n_1950; n_1951; n_1952; n_1953; n_1954; n_1955; n_1956; n_1957; n_1958; n_1959; n_1960; n_1961; n_1962; n_1963; n_1964; n_1965; n_1966; n_1967; n_1968; n_1969; n_1970; n_1971; n_1972; n_1973; n_1974; n_1975; n_1976; n_1977; n_1978; n_1979; n_1980; n_1981; n_1982; n_1983; n_1984; n_1985; n_1986; n_1987; n_1988; n_1989; n_1990; n_1991; n_1992; n_1993; n_1994; n_1995; n_1996; n_1997; n_1998; n_1999; n_2000; n_2001; n_2002; n_2003; n_2004; n_2005; n_2006; n_2007; n_2008; n_2009; n_2010; n_2011; n_2012; n_2013; n_2014; n_2015; n_2016; n_2017; n_2018; n_2019; n_2020; n_2021; n_2022; n_2023; n_2024; n_2025; n_2026; n_2027; n_2028; n_2029; n_2030; n_2031; n_2032; n_2033; n_2034; n_2035; n_2036; n_2037; n_2038; n_2039]
(*let properties = [n_CntrlProp; n_CntrlProp1; n_DataProp]*)


(*let properties = [n_CntrlProp]*)

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
		
let properties	=List.concat (List.map ~f:(preProcessProp) properties)

let () =    
	 
	let paraRef= paramfix "i" "NODE" (Intc(3)) in
	let results=Cmp.cmpOnPrs properties ~types:types  paraRef  [1;2] ~unAbstractedReqs:[] rules in
	let ()=print_endline "----------------------/n" in
	let a=List.map ~f:(fun  r -> print_endline (ToMurphi.rule_act r)) (fst results) in
	let b=List.map ~f:(fun  r -> print_endline (ToStr.Smv.form_act (Trans.trans_formula ~types:types r))) (snd results) in
	()
(*open ExtractCharact
open CheckInv
let () =  
   
	 
	let paraRef= paramfix "src0" "NODE" (Intc(3)) in
	 
	let ()=print_endline "---refine2\n" in
	let rules=CMP.cmp properties ~types:types  paraRef  [1;2] ~unAbstractedParas:[] n_SendReqS in
	let b=List.map ~f:(fun  r -> print_endline (ToMurphi.rule_act r)) (fst rules) in
	let ()=print_endline "---refine3\n" in
	let paraRef= paramfix "src0" "NODE" (Intc(3)) in
	let rules=CMP.cmp properties ~types:types  paraRef  [1;2] ~unAbstractedParas:[] n_RecvInvAck1 in
	let a=List.map ~f:(fun  r -> print_endline (ToMurphi.rule_act r)) (fst rules) in
	let b=List.map ~f:(fun  r -> print_endline (ToStr.Smv.form_act (Trans.trans_formula ~types:types r))) (snd rules) in
	let prot= Loach.Trans.act ~loach:protocol in  
	let host="192.168.1.37" in 
  let a=CheckInv.startServer ~murphi:(In_channel.read_all "n_german.m")
    ~smv:(In_channel.read_all "german.smv") "n_german"  "n_german" 
    host host ~types:types ~vardefs:vardefs in
  let ()=print_endline "---refine5\n" in  
  let b=List.map ~f:(fun f -> print_endline (ToStr.Smv.form_act  f)) ( extract   prot) in   

*)
