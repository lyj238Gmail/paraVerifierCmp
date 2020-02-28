
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _CACHE_I = strc "CACHE_I"
let _CACHE_S = strc "CACHE_S"
let _CACHE_E = strc "CACHE_E"
let _NODE_None = strc "NODE_None"
let _NODE_Get = strc "NODE_Get"
let _NODE_GetX = strc "NODE_GetX"
let _UNI_None = strc "UNI_None"
let _UNI_Get = strc "UNI_Get"
let _UNI_GetX = strc "UNI_GetX"
let _UNI_Put = strc "UNI_Put"
let _UNI_PutX = strc "UNI_PutX"
let _UNI_Nak = strc "UNI_Nak"
let _INV_None = strc "INV_None"
let _INV_Inv = strc "INV_Inv"
let _INV_InvAck = strc "INV_InvAck"
let _RP_None = strc "RP_None"
let _RP_Replace = strc "RP_Replace"
let _WB_None = strc "WB_None"
let _WB_Wb = strc "WB_Wb"
let _SHWB_None = strc "SHWB_None"
let _SHWB_ShWb = strc "SHWB_ShWb"
let _SHWB_FAck = strc "SHWB_FAck"
let _NAKC_None = strc "NAKC_None"
let _NAKC_Nakc = strc "NAKC_Nakc"
let _True = boolc true
let _False = boolc false

let types = [
  enum "CACHE_STATE" [_CACHE_I; _CACHE_S; _CACHE_E];
  enum "NODE_CMD" [_NODE_None; _NODE_Get; _NODE_GetX];
  enum "UNI_CMD" [_UNI_None; _UNI_Get; _UNI_GetX; _UNI_Put; _UNI_PutX; _UNI_Nak];
  enum "INV_CMD" [_INV_None; _INV_Inv; _INV_InvAck];
  enum "RP_CMD" [_RP_None; _RP_Replace];
  enum "WB_CMD" [_WB_None; _WB_Wb];
  enum "SHWB_CMD" [_SHWB_None; _SHWB_ShWb; _SHWB_FAck];
  enum "NAKC_CMD" [_NAKC_None; _NAKC_Nakc];
  enum "NODE" (int_consts [1; 2]);
  enum "DATA" (int_consts [1; 2]);
  enum "boolean" [_True; _False];
]

let _NODE_STATE = List.concat [
  [arrdef [("ProcCmd", [])] "NODE_CMD"];
  [arrdef [("InvMarked", [])] "boolean"];
  [arrdef [("CacheState", [])] "CACHE_STATE"];
  [arrdef [("CacheData", [])] "DATA"]
]


let _DIR_STATE = List.concat [
  [arrdef [("Pending", [])] "boolean"];
  [arrdef [("Local", [])] "boolean"];
  [arrdef [("Dirty", [])] "boolean"];
  [arrdef [("HeadVld", [])] "boolean"];
  [arrdef [("HeadPtr", [])] "NODE"];
  [arrdef [("ShrVld", [])] "boolean"];
  [arrdef [("ShrSet", [])] "boolean"];
  [arrdef [("InvSet", [])] "boolean"];
  [arrdef [("HomeHeadPtr", [])] "boolean"];
  [arrdef [("HomeShrSet", [])] "boolean"];
  [arrdef [("HomeInvSet", [])] "boolean"]
]
let _UNI_MSG = List.concat [
  [arrdef [("Cmd", [])] "UNI_CMD"];
  [arrdef [("Proc", [])] "NODE"];
  [arrdef [("HomeProc", [])] "boolean"];
  [arrdef [("Data", [])] "DATA"]
]

let _INV_MSG = List.concat [
  [arrdef [("Cmd", [])] "INV_CMD"]
]

let _RP_MSG = List.concat [
  [arrdef [("Cmd", [])] "RP_CMD"]
]

let _WB_MSG = List.concat [
  [arrdef [("Cmd", [])] "WB_CMD"];
  [arrdef [("Proc", [])] "NODE"];
  [arrdef [("HomeProc", [])] "boolean"];
  [arrdef [("Data", [])] "DATA"]
]

let _SHWB_MSG = List.concat [
  [arrdef [("Cmd", [])] "SHWB_CMD"];
  [arrdef [("Proc", [])] "NODE"];
  [arrdef [("HomeProc", [])] "boolean"];
  [arrdef [("Data", [])] "DATA"]
]

let _NAKC_MSG = List.concat [
  [arrdef [("Cmd", [])] "NAKC_CMD"]
]

let _STATE = List.concat [
record_def "Proc" [paramdef "i2" "NODE"] _NODE_STATE;
  record_def "Dir" [] _DIR_STATE;
  [arrdef [("MemData", [])] "DATA"];
  record_def "UniMsg" [paramdef "i2" "NODE"] _UNI_MSG;
  record_def "InvMsg" [paramdef "i3" "NODE"] _INV_MSG;
  record_def "RpMsg" [paramdef "i4" "NODE"] _RP_MSG;
  record_def "WbMsg" [] _WB_MSG;
  record_def "ShWbMsg" [] _SHWB_MSG;
  record_def "NakcMsg" [] _NAKC_MSG;
  record_def "HomeProc" [] _NODE_STATE;
  record_def "HomeUniMsg" [] _UNI_MSG;
  record_def "HomeInvMsg" [] _INV_MSG;
  record_def "HomeRpMsg" [] _RP_MSG;
  [arrdef [("CurrData", [])] "DATA"]
]

let vardefs = List.concat [
  record_def "Sta" [] _STATE
]

let init = (parallel [(assign (record [global "Sta"; global "MemData"]) (param (paramfix "d" "DATA" (intc 1)))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramfix "h" "NODE" (intc 1)))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (assign (record [global "Sta"; global "WbMsg"; global "Cmd"]) (const _WB_None)); (assign (record [global "Sta"; global "WbMsg"; global "Proc"]) (param (paramfix "h" "NODE" (intc 1)))); (assign (record [global "Sta"; global "WbMsg"; global "HomeProc"]) (const (boolc true))); (assign (record [global "Sta"; global "WbMsg"; global "Data"]) (param (paramfix "d" "DATA" (intc 1)))); (assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_None)); (assign (record [global "Sta"; global "ShWbMsg"; global "Proc"]) (param (paramfix "h" "NODE" (intc 1)))); (assign (record [global "Sta"; global "ShWbMsg"; global "HomeProc"]) (const (boolc true))); (assign (record [global "Sta"; global "ShWbMsg"; global "Data"]) (param (paramfix "d" "DATA" (intc 1)))); (assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_None)); (forStatement (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "CacheData"]) (param (paramfix "d" "DATA" (intc 1)))); (assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "p"])]; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "p"])]; global "Proc"]) (param (paramfix "h" "NODE" (intc 1)))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "p"])]; global "HomeProc"]) (const (boolc true))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "p"])]; global "Data"]) (param (paramfix "d" "DATA" (intc 1)))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("RpMsg", [paramref "p"])]; global "Cmd"]) (const _RP_None))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "HomeProc"; global "CacheData"]) (param (paramfix "d" "DATA" (intc 1)))); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Proc"]) (param (paramfix "h" "NODE" (intc 1)))); (assign (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeUniMsg"; global "Data"]) (param (paramfix "d" "DATA" (intc 1)))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; global "HomeRpMsg"; global "Cmd"]) (const _RP_None)); (assign (record [global "Sta"; global "CurrData"]) (param (paramfix "d" "DATA" (intc 1))))])

let n_NI_Replace3 =
  let name = "n_NI_Replace3" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)); (eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"]) (const _RP_None)); (assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "src"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_Replace4 =
  let name = "n_NI_Replace4" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)); (eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _False))]) in
  let statement = (assign (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"]) (const _RP_None)) in
  rule name params formula statement

let n_NI_InvAck_311 =
  let name = "n_NI_InvAck_311" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("InvMsg", [paramref "src"])]; global "Cmd"])) (const _INV_InvAck)); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeInvSet"])) (const (boolc false)))]); (forallFormula [paramdef "p" "NODE"] (orList [(eqn (param (paramref "p")) (param (paramref "src"))); (eqn (var (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]])) (const (boolc false)))]))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("InvMsg", [paramref "src"])]; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_InvAck_212 =
  let name = "n_NI_InvAck_212" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("InvMsg", [paramref "src"])]; global "Cmd"])) (const _INV_InvAck)); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeInvSet"])) (const (boolc false)))]); (forallFormula [paramdef "p" "NODE"] (orList [(eqn (param (paramref "p")) (param (paramref "src"))); (eqn (var (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]])) (const (boolc false)))]))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("InvMsg", [paramref "src"])]; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_InvAck_113 =
  let name = "n_NI_InvAck_113" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("InvMsg", [paramref "src"])]; global "Cmd"])) (const _INV_InvAck)); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeInvSet"])) (const (boolc false)))]); (forallFormula [paramdef "p" "NODE"] (orList [(eqn (param (paramref "p")) (param (paramref "src"))); (eqn (var (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]])) (const (boolc false)))]))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("InvMsg", [paramref "src"])]; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_InvAck_exists14 =
  let name = "n_NI_InvAck_exists14" in
  let params = [paramdef "dst" "NODE"; paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("InvMsg", [paramref "src"])]; global "Cmd"])) (const _INV_InvAck)); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]])) (const (boolc true)))]); (neg (eqn (param (paramref "dst")) (param (paramref "src"))))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "dst"])]])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("InvMsg", [paramref "src"])]; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_InvAck_exists_Home15 =
  let name = "n_NI_InvAck_exists_Home15" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("InvMsg", [paramref "src"])]; global "Cmd"])) (const _INV_InvAck)); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeInvSet"])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("InvMsg", [paramref "src"])]; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_Inv16 =
  let name = "n_NI_Inv16" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("InvMsg", [paramref "dst"])]; global "Cmd"])) (const _INV_Inv)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"])) (const _NODE_Get))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("InvMsg", [paramref "dst"])]; global "Cmd"]) (const _INV_InvAck)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "InvMarked"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Inv17 =
  let name = "n_NI_Inv17" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("InvMsg", [paramref "dst"])]; global "Cmd"])) (const _INV_Inv)); (neg (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"])) (const _NODE_Get)))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("InvMsg", [paramref "dst"])]; global "Cmd"]) (const _INV_InvAck)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Remote_PutX18 =
  let name = "n_NI_Remote_PutX18" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"])) (const _UNI_PutX)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"])) (const _NODE_GetX))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_E)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheData"]) (var (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Data"])))]) in
  rule name params formula statement

let n_NI_Remote_Put20 =
  let name = "n_NI_Remote_Put20" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"])) (const _UNI_Put)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "InvMarked"])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Remote_Put21 =
  let name = "n_NI_Remote_Put21" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"])) (const _UNI_Put)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "InvMarked"])) (const _False))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_S)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheData"]) (var (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Data"])))]) in
  rule name params formula statement

let n_NI_Remote_GetX_PutX_Home24 =
  let name = "n_NI_Remote_GetX_PutX_Home24" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Data"]) (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheData"])))]) in
  rule name params formula statement

let n_NI_Remote_GetX_PutX25 =
  let name = "n_NI_Remote_GetX_PutX25" in
  let params = [paramdef "dst" "NODE"; paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(neg (eqn (param (paramref "src")) (param (paramref "dst")))); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheData"]))); (assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_FAck)); (assign (record [global "Sta"; global "ShWbMsg"; global "Proc"]) (param (paramref "src"))); (assign (record [global "Sta"; global "ShWbMsg"; global "HomeProc"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_Remote_GetX_Nak_Home26 =
  let name = "n_NI_Remote_GetX_Nak_Home26" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"])) (const (boolc false)))]); (neg (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_Nakc))]) in
  rule name params formula statement

let n_NI_Remote_GetX_Nak27 =
  let name = "n_NI_Remote_GetX_Nak27" in
  let params = [paramdef "dst" "NODE"; paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(neg (eqn (param (paramref "src")) (param (paramref "dst")))); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const (boolc false)))]); (neg (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E)))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"]) (param (paramref "dst"))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_Nakc))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_1128 =
  let name = "n_NI_Local_GetX_PutX_1128" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "HomeProc"; global "CacheData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_1029 =
  let name = "n_NI_Local_GetX_PutX_1029" in
  let params = [paramdef "dst" "NODE"; paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "dst"])]])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_10_Home30 =
  let name = "n_NI_Local_GetX_PutX_10_Home30" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeShrSet"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_931 =
  let name = "n_NI_Local_GetX_PutX_931" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]); (neg (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src"))))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_932 =
  let name = "n_NI_Local_GetX_PutX_932" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_8_NODE_Get33 =
  let name = "n_NI_Local_GetX_PutX_8_NODE_Get33" in
  let params = [paramdef "dst" "NODE"; paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "dst"])]])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_834 =
  let name = "n_NI_Local_GetX_PutX_834" in
  let params = [paramdef "dst" "NODE"; paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "dst"])]])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (neg (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_8_Home_NODE_Get35 =
  let name = "n_NI_Local_GetX_PutX_8_Home_NODE_Get35" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeShrSet"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_8_Home36 =
  let name = "n_NI_Local_GetX_PutX_8_Home36" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeShrSet"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (neg (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_7_NODE_Get37 =
  let name = "n_NI_Local_GetX_PutX_7_NODE_Get37" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]); (neg (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src"))))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_7_NODE_Get38 =
  let name = "n_NI_Local_GetX_PutX_7_NODE_Get38" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_739 =
  let name = "n_NI_Local_GetX_PutX_739" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]); (neg (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src"))))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (neg (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_740 =
  let name = "n_NI_Local_GetX_PutX_740" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (neg (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_641 =
  let name = "n_NI_Local_GetX_PutX_641" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeShrSet"])) (const (boolc false)))]); (forallFormula [paramdef "p" "NODE"] (imply (neg (eqn (param (paramref "p")) (param (paramref "src")))) (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const (boolc false)))))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_542 =
  let name = "n_NI_Local_GetX_PutX_542" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeShrSet"])) (const (boolc false)))]); (forallFormula [paramdef "p" "NODE"] (imply (neg (eqn (param (paramref "p")) (param (paramref "src")))) (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const (boolc false)))))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (neg (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_443 =
  let name = "n_NI_Local_GetX_PutX_443" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeShrSet"])) (const (boolc false)))]); (forallFormula [paramdef "p" "NODE"] (imply (neg (eqn (param (paramref "p")) (param (paramref "src")))) (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const (boolc false)))))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_344 =
  let name = "n_NI_Local_GetX_PutX_344" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_245 =
  let name = "n_NI_Local_GetX_PutX_245" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (neg (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX_146 =
  let name = "n_NI_Local_GetX_PutX_146" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Local_GetX_GetX47 =
  let name = "n_NI_Local_GetX_GetX47" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]); (neg (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src"))))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_GetX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"]) (var (record [global "Sta"; global "Dir"; global "HeadPtr"]))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])))]) in
  rule name params formula statement

let n_NI_Local_GetX_GetX48 =
  let name = "n_NI_Local_GetX_GetX48" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_GetX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"]) (var (record [global "Sta"; global "Dir"; global "HeadPtr"]))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])))]) in
  rule name params formula statement

let n_NI_Local_GetX_Nak49 =
  let name = "n_NI_Local_GetX_Nak49" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Local_GetX_Nak50 =
  let name = "n_NI_Local_GetX_Nak50" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (neg (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E)))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Local_GetX_Nak51 =
  let name = "n_NI_Local_GetX_Nak51" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Remote_Get_Put_Home52 =
  let name = "n_NI_Remote_Get_Put_Home52" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_S)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_Put)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Data"]) (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheData"])))]) in
  rule name params formula statement

let n_NI_Remote_Get_Put53 =
  let name = "n_NI_Remote_Get_Put53" in
  let params = [paramdef "dst" "NODE"; paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(neg (eqn (param (paramref "src")) (param (paramref "dst")))); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_S)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Put)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheData"]))); (assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_ShWb)); (assign (record [global "Sta"; global "ShWbMsg"; global "Proc"]) (param (paramref "src"))); (assign (record [global "Sta"; global "ShWbMsg"; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "ShWbMsg"; global "Data"]) (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheData"])))]) in
  rule name params formula statement

let n_NI_Remote_Get_Nak_Home54 =
  let name = "n_NI_Remote_Get_Nak_Home54" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"])) (const (boolc false)))]); (neg (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_Nakc))]) in
  rule name params formula statement

let n_NI_Remote_Get_Nak55 =
  let name = "n_NI_Remote_Get_Nak55" in
  let params = [paramdef "dst" "NODE"; paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(neg (eqn (param (paramref "src")) (param (paramref "dst")))); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const (boolc false)))]); (neg (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E)))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"]) (param (paramref "dst"))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_Nakc))]) in
  rule name params formula statement

let n_NI_Local_Get_Put_Dirty56 =
  let name = "n_NI_Local_Get_Put_Dirty56" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (neg (eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "MemData"]) (var (record [global "Sta"; global "HomeProc"; global "CacheData"]))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_S)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Put)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "HomeProc"; global "CacheData"])))]) in
  rule name params formula statement

let n_NI_Local_Get_Put57 =
  let name = "n_NI_Local_Get_Put57" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (neg (eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Put)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_NI_Local_Get_Put_Head58 =
  let name = "n_NI_Local_Get_Put_Head58" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (neg (eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "src"])]]) (const (boolc true))); (forStatement (ifelseStatement (eqn (param (paramref "p")) (param (paramref "src"))) (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))) (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])))) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (var (record [global "Sta"; global "Dir"; global "HomeShrSet"]))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Put)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Data"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_NI_Local_Get_Get59 =
  let name = "n_NI_Local_Get_Get59" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (neg (eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]); (neg (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src"))))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Get)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"]) (var (record [global "Sta"; global "Dir"; global "HeadPtr"]))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])))]) in
  rule name params formula statement

let n_NI_Local_Get_Get60 =
  let name = "n_NI_Local_Get_Get60" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (neg (eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Get)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"]) (var (record [global "Sta"; global "Dir"; global "HeadPtr"]))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])))]) in
  rule name params formula statement

let n_NI_Local_Get_Nak61 =
  let name = "n_NI_Local_Get_Nak61" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (neg (eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Local_Get_Nak62 =
  let name = "n_NI_Local_Get_Nak62" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (neg (eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc true)))]); (neg (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E)))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Local_Get_Nak63 =
  let name = "n_NI_Local_Get_Nak63" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (neg (eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (const (boolc true)))]) in
  rule name params formula statement

let n_NI_Nak66 =
  let name = "n_NI_Nak66" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"])) (const _UNI_Nak)) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "InvMarked"]) (const (boolc false)))]) in
  rule name params formula statement

let n_PI_Remote_Replace68 =
  let name = "n_PI_Remote_Replace68" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "CacheState"])) (const _CACHE_S))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"]) (const _RP_Replace))]) in
  rule name params formula statement

let n_PI_Remote_PutX71 =
  let name = "n_PI_Remote_PutX71" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "WbMsg"; global "Cmd"]) (const _WB_Wb)); (assign (record [global "Sta"; global "WbMsg"; global "Proc"]) (param (paramref "dst"))); (assign (record [global "Sta"; global "WbMsg"; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "WbMsg"; global "Data"]) (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheData"])))]) in
  rule name params formula statement

let n_PI_Remote_GetX80 =
  let name = "n_PI_Remote_GetX80" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "CacheState"])) (const _CACHE_I))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "ProcCmd"]) (const _NODE_GetX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_GetX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (const (boolc true)))]) in
  rule name params formula statement

let n_PI_Remote_Get84 =
  let name = "n_PI_Remote_Get84" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "CacheState"])) (const _CACHE_I))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "ProcCmd"]) (const _NODE_Get)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Get)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (const (boolc true)))]) in
  rule name params formula statement

let n_Store_Home85 =
  let name = "n_Store_Home85" in
  let params = [paramdef "data" "DATA"] in
  let formula = (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E)) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeProc"; global "CacheData"]) (param (paramref "data"))); (assign (record [global "Sta"; global "CurrData"]) (param (paramref "data")))]) in
  rule name params formula statement

let n_Store86 =
  let name = "n_Store86" in
  let params = [paramdef "data" "DATA"; paramdef "src" "NODE"] in
  let formula = (eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "CacheState"])) (const _CACHE_E)) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "CacheData"]) (param (paramref "data"))); (assign (record [global "Sta"; global "CurrData"]) (param (paramref "data")))]) in
  rule name params formula statement

let n_NI_Replace_Home1 =
  let name = "n_NI_Replace_Home1" in
  let params = [] in
  let formula = (andList [(eqn (var (record [global "Sta"; global "HomeRpMsg"; global "Cmd"])) (const _RP_Replace)); (eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeRpMsg"; global "Cmd"]) (const _RP_None)); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_Replace_Home2 =
  let name = "n_NI_Replace_Home2" in
  let params = [] in
  let formula = (andList [(eqn (var (record [global "Sta"; global "HomeRpMsg"; global "Cmd"])) (const _RP_Replace)); (eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _False))]) in
  let statement = (assign (record [global "Sta"; global "HomeRpMsg"; global "Cmd"]) (const _RP_None)) in
  rule name params formula statement

let n_NI_ShWb5 =
  let name = "n_NI_ShWb5" in
  let params = [] in
  let formula = (andList [(eqn (var (record [global "Sta"; global "ShWbMsg"; global "Cmd"])) (const _SHWB_ShWb)); (eqn (var (record [global "Sta"; global "ShWbMsg"; global "HomeProc"])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_None)); (assign (record [global "Sta"; global "ShWbMsg"; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc true))); (forStatement (ifelseStatement (orList [(andList [(eqn (param (paramref "p")) (var (record [global "Sta"; global "ShWbMsg"; global "Proc"]))); (eqn (var (record [global "Sta"; global "ShWbMsg"; global "HomeProc"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true)))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))])) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc true))); (assign (record [global "Sta"; global "MemData"]) (var (record [global "Sta"; global "ShWbMsg"; global "Data"])))]) in
  rule name params formula statement

let n_NI_ShWb6 =
  let name = "n_NI_ShWb6" in
  let params = [] in
  let formula = (andList [(eqn (var (record [global "Sta"; global "ShWbMsg"; global "Cmd"])) (const _SHWB_ShWb)); (eqn (var (record [global "Sta"; global "Dir"; global "HomeShrSet"])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_None)); (assign (record [global "Sta"; global "ShWbMsg"; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc true))); (forStatement (ifelseStatement (orList [(andList [(eqn (param (paramref "p")) (var (record [global "Sta"; global "ShWbMsg"; global "Proc"]))); (eqn (var (record [global "Sta"; global "ShWbMsg"; global "HomeProc"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true)))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))])) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc true))); (assign (record [global "Sta"; global "MemData"]) (var (record [global "Sta"; global "ShWbMsg"; global "Data"])))]) in
  rule name params formula statement

let n_NI_ShWb7 =
  let name = "n_NI_ShWb7" in
  let params = [] in
  let formula = (andList [(andList [(eqn (var (record [global "Sta"; global "ShWbMsg"; global "Cmd"])) (const _SHWB_ShWb)); (eqn (var (record [global "Sta"; global "ShWbMsg"; global "HomeProc"])) (const _False))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeShrSet"])) (const _False))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_None)); (assign (record [global "Sta"; global "ShWbMsg"; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc true))); (forStatement (ifelseStatement (orList [(andList [(eqn (param (paramref "p")) (var (record [global "Sta"; global "ShWbMsg"; global "Proc"]))); (eqn (var (record [global "Sta"; global "ShWbMsg"; global "HomeProc"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true)))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))])) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "MemData"]) (var (record [global "Sta"; global "ShWbMsg"; global "Data"])))]) in
  rule name params formula statement

let n_NI_FAck8 =
  let name = "n_NI_FAck8" in
  let params = [] in
  let formula = (andList [(eqn (var (record [global "Sta"; global "ShWbMsg"; global "Cmd"])) (const _SHWB_FAck)); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_None)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "ShWbMsg"; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (var (record [global "Sta"; global "ShWbMsg"; global "Proc"]))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (var (record [global "Sta"; global "ShWbMsg"; global "HomeProc"])))]) in
  rule name params formula statement

let n_NI_FAck9 =
  let name = "n_NI_FAck9" in
  let params = [] in
  let formula = (andList [(eqn (var (record [global "Sta"; global "ShWbMsg"; global "Cmd"])) (const _SHWB_FAck)); (neg (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true))))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_None)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "ShWbMsg"; global "HomeProc"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_Wb10 =
  let name = "n_NI_Wb10" in
  let params = [] in
  let formula = (eqn (var (record [global "Sta"; global "WbMsg"; global "Cmd"])) (const _WB_Wb)) in
  let statement = (parallel [(assign (record [global "Sta"; global "WbMsg"; global "Cmd"]) (const _WB_None)); (assign (record [global "Sta"; global "WbMsg"; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false))); (assign (record [global "Sta"; global "MemData"]) (var (record [global "Sta"; global "WbMsg"; global "Data"])))]) in
  rule name params formula statement

let n_NI_Local_PutXAcksDone19 =
  let name = "n_NI_Local_PutXAcksDone19" in
  let params = [] in
  let formula = (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_PutX)) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_E)); (assign (record [global "Sta"; global "HomeProc"; global "CacheData"]) (var (record [global "Sta"; global "HomeUniMsg"; global "Data"])))]) in
  rule name params formula statement

let n_NI_Local_Put22 =
  let name = "n_NI_Local_Put22" in
  let params = [] in
  let formula = (andList [(eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_Put)); (eqn (var (record [global "Sta"; global "HomeProc"; global "InvMarked"])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "MemData"]) (var (record [global "Sta"; global "HomeUniMsg"; global "Data"]))); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Local_Put23 =
  let name = "n_NI_Local_Put23" in
  let params = [] in
  let formula = (andList [(eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_Put)); (eqn (var (record [global "Sta"; global "HomeProc"; global "InvMarked"])) (const _False))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "MemData"]) (var (record [global "Sta"; global "HomeUniMsg"; global "Data"]))); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_S)); (assign (record [global "Sta"; global "HomeProc"; global "CacheData"]) (var (record [global "Sta"; global "HomeUniMsg"; global "Data"])))]) in
  rule name params formula statement

let n_NI_Nak_Clear64 =
  let name = "n_NI_Nak_Clear64" in
  let params = [] in
  let formula = (eqn (var (record [global "Sta"; global "NakcMsg"; global "Cmd"])) (const _NAKC_Nakc)) in
  let statement = (parallel [(assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_None)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_Nak_Home65 =
  let name = "n_NI_Nak_Home65" in
  let params = [] in
  let formula = (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_Nak)) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false)))]) in
  rule name params formula statement

let n_PI_Local_Replace67 =
  let name = "n_PI_Local_Replace67" in
  let params = [] in
  let formula = (andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_S))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_PI_Local_PutX69 =
  let name = "n_PI_Local_PutX69" in
  let params = [] in
  let formula = (andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "MemData"]) (var (record [global "Sta"; global "HomeProc"; global "CacheData"])))]) in
  rule name params formula statement

let n_PI_Local_PutX70 =
  let name = "n_PI_Local_PutX70" in
  let params = [] in
  let formula = (andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E))]); (neg (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc true))))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "MemData"]) (var (record [global "Sta"; global "HomeProc"; global "CacheData"])))]) in
  rule name params formula statement

let n_PI_Local_GetX_PutX_HeadVld7572 =
  let name = "n_PI_Local_GetX_PutX_HeadVld7572" in
  let params = [] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_S))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p"))); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_E)); (assign (record [global "Sta"; global "HomeProc"; global "CacheData"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_PI_Local_GetX_PutX_HeadVld7473 =
  let name = "n_PI_Local_GetX_PutX_HeadVld7473" in
  let params = [] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_I))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p"))); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_E)); (assign (record [global "Sta"; global "HomeProc"; global "CacheData"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_PI_Local_GetX_PutX7374 =
  let name = "n_PI_Local_GetX_PutX7374" in
  let params = [] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_S))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_E)); (assign (record [global "Sta"; global "HomeProc"; global "CacheData"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_PI_Local_GetX_PutX7275 =
  let name = "n_PI_Local_GetX_PutX7275" in
  let params = [] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_I))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const (boolc false)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_E)); (assign (record [global "Sta"; global "HomeProc"; global "CacheData"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_PI_Local_GetX_PutX_HeadVld76 =
  let name = "n_PI_Local_GetX_PutX_HeadVld76" in
  let params = [] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_I))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p"))); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_E)); (assign (record [global "Sta"; global "HomeProc"; global "CacheData"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_PI_Local_GetX_PutX_HeadVld77 =
  let name = "n_PI_Local_GetX_PutX_HeadVld77" in
  let params = [] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_S))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p"))); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const (boolc false)))])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_E)); (assign (record [global "Sta"; global "HomeProc"; global "CacheData"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_PI_Local_GetX_GetX78 =
  let name = "n_PI_Local_GetX_GetX78" in
  let params = [] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_I))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_GetX)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_GetX)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Proc"]) (var (record [global "Sta"; global "Dir"; global "HeadPtr"]))); (assign (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"]) (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])))]) in
  rule name params formula statement

let n_PI_Local_GetX_GetX79 =
  let name = "n_PI_Local_GetX_GetX79" in
  let params = [] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_S))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_GetX)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_GetX)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Proc"]) (var (record [global "Sta"; global "Dir"; global "HeadPtr"]))); (assign (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"]) (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])))]) in
  rule name params formula statement

let n_PI_Local_Get_Put81 =
  let name = "n_PI_Local_Get_Put81" in
  let params = [] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_I))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "HomeProc"; global "InvMarked"])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_PI_Local_Get_Put82 =
  let name = "n_PI_Local_Get_Put82" in
  let params = [] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_I))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "HomeProc"; global "InvMarked"])) (const _False))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_S)); (assign (record [global "Sta"; global "HomeProc"; global "CacheData"]) (var (record [global "Sta"; global "MemData"])))]) in
  rule name params formula statement

let n_PI_Local_Get_Get83 =
  let name = "n_PI_Local_Get_Get83" in
  let params = [] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_I))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const (boolc false)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc true)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_Get)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_Get)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Proc"]) (var (record [global "Sta"; global "Dir"; global "HeadPtr"]))); (assign (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"]) (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])))]) in
  rule name params formula statement

let rules = [n_NI_Replace3; n_NI_Replace4; n_NI_InvAck_311; n_NI_InvAck_212; n_NI_InvAck_113; n_NI_InvAck_exists14; n_NI_InvAck_exists_Home15; n_NI_Inv16; n_NI_Inv17; n_NI_Remote_PutX18; n_NI_Remote_Put20; n_NI_Remote_Put21; n_NI_Remote_GetX_PutX_Home24; n_NI_Remote_GetX_PutX25; n_NI_Remote_GetX_Nak_Home26; n_NI_Remote_GetX_Nak27; n_NI_Local_GetX_PutX_1128; n_NI_Local_GetX_PutX_1029; n_NI_Local_GetX_PutX_10_Home30; n_NI_Local_GetX_PutX_931; n_NI_Local_GetX_PutX_932; n_NI_Local_GetX_PutX_8_NODE_Get33; n_NI_Local_GetX_PutX_834; n_NI_Local_GetX_PutX_8_Home_NODE_Get35; n_NI_Local_GetX_PutX_8_Home36; n_NI_Local_GetX_PutX_7_NODE_Get37; n_NI_Local_GetX_PutX_7_NODE_Get38; n_NI_Local_GetX_PutX_739; n_NI_Local_GetX_PutX_740; n_NI_Local_GetX_PutX_641; n_NI_Local_GetX_PutX_542; n_NI_Local_GetX_PutX_443; n_NI_Local_GetX_PutX_344; n_NI_Local_GetX_PutX_245; n_NI_Local_GetX_PutX_146; n_NI_Local_GetX_GetX47; n_NI_Local_GetX_GetX48; n_NI_Local_GetX_Nak49; n_NI_Local_GetX_Nak50; n_NI_Local_GetX_Nak51; n_NI_Remote_Get_Put_Home52; n_NI_Remote_Get_Put53; n_NI_Remote_Get_Nak_Home54; n_NI_Remote_Get_Nak55; n_NI_Local_Get_Put_Dirty56; n_NI_Local_Get_Put57; n_NI_Local_Get_Put_Head58; n_NI_Local_Get_Get59; n_NI_Local_Get_Get60; n_NI_Local_Get_Nak61; n_NI_Local_Get_Nak62; n_NI_Local_Get_Nak63; n_NI_Nak66; n_PI_Remote_Replace68; n_PI_Remote_PutX71; n_PI_Remote_GetX80; n_PI_Remote_Get84; n_Store_Home85; n_Store86; n_NI_Replace_Home1; n_NI_Replace_Home2; n_NI_ShWb5; n_NI_ShWb6; n_NI_ShWb7; n_NI_FAck8; n_NI_FAck9; n_NI_Wb10; n_NI_Local_PutXAcksDone19; n_NI_Local_Put22; n_NI_Local_Put23; n_NI_Nak_Clear64; n_NI_Nak_Home65; n_PI_Local_Replace67; n_PI_Local_PutX69; n_PI_Local_PutX70; n_PI_Local_GetX_PutX_HeadVld7572; n_PI_Local_GetX_PutX_HeadVld7473; n_PI_Local_GetX_PutX7374; n_PI_Local_GetX_PutX7275; n_PI_Local_GetX_PutX_HeadVld76; n_PI_Local_GetX_PutX_HeadVld77; n_PI_Local_GetX_GetX78; n_PI_Local_GetX_GetX79; n_PI_Local_Get_Put81; n_PI_Local_Get_Put82; n_PI_Local_Get_Get83]

(*let rules = [n_NI_Local_GetX_PutX_1029]*)

let n_CacheStateProp =
  let name = "n_CacheStateProp" in
  let params = [] in
  let formula = (forallFormula [paramdef "p" "NODE"] (forallFormula [paramdef "q" "NODE"] (imply (neg (eqn (param (paramref "p")) (param (paramref "q")))) (neg (andList [(eqn (var (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "CacheState"])) (const _CACHE_E)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "q"])]; global "CacheState"])) (const _CACHE_E))]))))) in
  prop name params formula

let n_CacheStatePropHome =
  let name = "n_CacheStatePropHome" in
  let params = [] in
  let formula = (forallFormula [paramdef "p" "NODE"] (neg (andList [(eqn (var (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "CacheState"])) (const _CACHE_E)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E))]))) in
  prop name params formula

let n_DataProp =
  let name = "n_DataProp" in
  let params = [] in
  let formula = (forallFormula [paramdef "p" "NODE"] (imply (eqn (var (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "CacheState"])) (const _CACHE_E)) (eqn (var (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "CacheData"])) (var (record [global "Sta"; global "CurrData"]))))) in
  prop name params formula

let n_MemDataProp =
  let name = "n_MemDataProp" in
  let params = [] in
  let formula = (imply (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const (boolc false))) (eqn (var (record [global "Sta"; global "MemData"])) (var (record [global "Sta"; global "CurrData"])))) in
  prop name params formula

let properties = [n_CacheStateProp; n_CacheStatePropHome; n_DataProp; n_MemDataProp]


let protocol = {
  name = "n_flash_unde_noaux";
  types;
  vardefs;
  init;
  rules;
  properties;
}


let propertiesRef=ref [] 

  let preProcessProp p =
  let Prop(name,params,formula)=p in
 (* let ()=print_endline name in
  let ()=print_endline ("this is"^(ToStr.Debug.form_act  (Loach.Trans.trans_formula types formula))) in*)
  match formula with 
  
  |Imply(a,b) ->
    if (List.length params) =2
    then [Prop(name,params,b)]
    else [p]
  |_ ->[p]
let count=ref 0

let preProcessAndProp p =
  let Prop(name,params,formula)=p in
 (* let ()=print_endline name in
  let ()=print_endline ("this is"^(ToStr.Debug.form_act  (Loach.Trans.trans_formula types formula))) in*)
  match formula with 
  
  |AndList(_) ->
   List.map ~f:(fun f ->let ()=count:=!count + 1 in Prop(name^(string_of_int (!count)),params,f)) ( negDisjI2Implication (Neg(formula)))
  |_ ->[Prop(name,params,Imply(Chaos,Neg(formula)))]
  
 
let  () =  
  let tmp=Client.Smt2.host := UnixLabels.inet_addr_of_string  "192.168.20.15" in
	let tmp=Client.Murphi.host := UnixLabels.inet_addr_of_string  "192.168.20.15" in
  let _smt_context = Smt.set_context "flash" (ToStr.Smt2.context_of ~insym_types:[] ~types ~vardefs) in
  let ()=Generalize.zero_special:=true in
  let ()=PublicVariables.enumStrings := PublicVariables.extract types in 
  let ()=propertiesRef:=TestParser.loop "flash_data_cub_inv.m" () in
   let properties=List.concat (List.map ~f:(preProcessAndProp) (!propertiesRef)) in
  let k=List.map ~f:(fun p -> print_endline (ToMurphi.prop_act p))  properties in
  	let paraRef= paramfix "i" "NODE" (Intc(3)) in	
	let dparaDef=paramdef "data" "DATA"  in
  let pair=("n_Store_Home85",[dparaDef]) in
  let pair1=("n_Store86",[dparaDef]) in
  let ()=Cmp.initInvs properties types  paraRef in
  let ()=Cmp.setPrules rules in
  let ptrVars=[(record [global "Sta"; global "Dir"; global "HeadPtr"]);
		(record [global "Sta"; global "ShWbMsg"; global "Proc"]);
		(record [global "Sta"; global "WbMsg"; global "Proc"])] in
	Cmp.cmpGenChk ptrVars properties ~types:types  paraRef   [1;2] ~unAbstractedReqs:[pair;pair1] [] rules  protocol ["NODE";"DATA"] ptrVars

(*let main () =  
  let localhost="192.168.1.37" in
  let a=CheckInv.startServer ~murphi:(In_channel.read_all "flash1130.m")
    ~smv:(In_channel.read_all "mutualEx.smv") "flash0"  "flash0" 
    localhost localhost  ~types:types ~vardefs:vardefs  protocol in  
  let ()=Generalize.zero_special:=true in
  let ()=PublicVariables.enumStrings := PublicVariables.extract types in 
  let ()=propertiesRef:=TestParser.loop "flash_data_cub_inv.m" () in
  let properties=List.concat (List.map ~f:(preProcessAndProp) (!propertiesRef)) in
  let paraRef= paramfix "i" "NODE" (Intc(3)) in
  let dparaDef=paramdef "data" "DATA"  in
  let pair=("n_Store_Home85",[dparaDef]) in
  let pair1=("n_Store86",[dparaDef]) in
  let ()=Cmp.initInvs properties types  paraRef in
  let ()=Cmp.setPrules rules in
  let results=Cmp.cmpOnPrs properties ~types:types  paraRef  [1;2] ~unAbstractedReqs:[pair;pair1]   [ ]  rules in
  let ()=print_endline "----------------------/n" in
  let ()=print_endline "--------all abs rules--------------/n" in
  
   let rs'=List.map ~f:(simplify_rule_by_elim_false_eq 3 [(param (paramref "p")) ]) (fst results) in*)
  (*let rs'=fst results in 
  let rs'=   List.map ~f:(LoachGeneralize.rule_act ~rename:false ~generalizedtParas:[intc 4] ) rs' in*)
  (*let a=List.map ~f:(fun  r -> print_endline (ToMurphi.rule_act r)) rs' in
  (*let a=List.map ~f:(fun  r -> print_endline (ToMurphi.rule_act r)) rs' in*)
  let invs= List.map ~f:(fun f ->LoachGeneralize.form_act ~rename:false ~generalizedtParas:[intc 3;intc 2 ] f [] []) (snd results)   in
  let b=List.map ~f:(fun  (_,_,f) -> print_endline (ToMurphi.form_act f)) invs in
  ()
let () = run_with_cmdline main  

(*let () = run_with_cmdline (fun () ->
  let protocol = preprocess_rule_guard ~loach:protocol in
  let cinvs_with_varnames, relations = find protocol
    ~murphi:(In_channel.read_all "n_flash_unde_noaux.m")
  in
  Isabelle.protocol_act protocol cinvs_with_varnames relations ()
)*)

*)
