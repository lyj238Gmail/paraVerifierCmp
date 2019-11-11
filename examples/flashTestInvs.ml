
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline
open CheckInv
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
  enum "NODE" (int_consts [1; 2; 3]);
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
  [arrdef [("ShrSet", [paramdef "i0" "NODE"])] "boolean"];
  [arrdef [("InvSet", [paramdef "i1" "NODE"])] "boolean"]
]

let _UNI_MSG = List.concat [
  [arrdef [("Cmd", [])] "UNI_CMD"];
 [arrdef [("Proc", [])] "NODE"];
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
  [arrdef [("Data", [])] "DATA"]
]

let _SHWB_MSG = List.concat [
  [arrdef [("Cmd", [])] "SHWB_CMD"];
  [arrdef [("Proc", [])] "NODE"];
  [arrdef [("Data", [])] "DATA"]
]

let _NAKC_MSG = List.concat [
  [arrdef [("Cmd", [])] "NAKC_CMD"]
]

let _STATE = List.concat [
  record_def "Dir" [] _DIR_STATE;
   record_def "Proc" [paramdef "i2" "NODE"] _NODE_STATE;
  [arrdef [("MemData", [])] "DATA"];
  record_def "UniMsg" [paramdef "i2" "NODE"] _UNI_MSG;
  record_def "InvMsg" [paramdef "i3" "NODE"] _INV_MSG;
  record_def "RpMsg" [paramdef "i4" "NODE"] _RP_MSG;
  record_def "WbMsg" [] _WB_MSG;
  record_def "ShWbMsg" [] _SHWB_MSG;
  record_def "NakcMsg" [] _NAKC_MSG;
  [arrdef [("CurrData", [])] "DATA"];
  [arrdef [("PrevData", [])] "DATA"];
  [arrdef [("LastWrVld", [])] "boolean"];
     [arrdef [("LastWrPtr", [])] "NODE"];
	 [arrdef [("PendReqSrc", [])] "NODE"];
  [arrdef [("PendReqCmd", [])] "UNI_CMD"];
  [arrdef [("Collecting", [])] "boolean"];
  [arrdef [("FwdCmd", [])] "UNI_CMD"];
	  [arrdef [("FwdSrc", [])] "NODE"];
 
  [arrdef [("LastInvAck", [])] "NODE"];
	 [arrdef [("LastOtherInvAck", [])] "NODE"]
]

let vardefs = List.concat [
  (*[arrdef [("Home", [])] "NODE"];*)
  record_def "Sta" [] _STATE
]



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
    
(*let properties  =List.concat (List.map ~f:(preProcessProp) properties)*)

let ()=	
  let ()=PublicVariables.enumStrings := PublicVariables.extract types in 
  let ()=propertiesRef:=TestParser.loop "flash_changed_Invs.invs" () in

  (*let properties=List.concat (List.map ~f:(preProcessProp) (!propertiesRef)) in*)
     let paraRef= paramfix "i" "NODE" (Intc(1)) in

    let fs= Cmp.properties2invs (!propertiesRef) ~types:types  paraRef in

  let localhost="192.168.1.37" in
  let a=CheckInv.startServer ~murphi:(In_channel.read_all "flash1130.m")
    ~smv:(In_channel.read_all "flash_nodata.smv") "flash"  "flash" 
    localhost localhost  ~types:types ~vardefs:vardefs in

    let ()=print_endline "enter checkInv" in
  let fs=List.filter ~f:(fun f -> not (CheckInv.checkInv types f) )fs in
	let ()=print_endline "enter here" in
  let b=List.map ~f:(fun  f -> print_endline (ToMurphi.form_act f)) fs in
 (* let c=CheckInv.checkProps types  properties in*)
  ()
   

(*let () =    
  (*let ()=Generalize.zero_special:=true in*)
  let ()=PublicVariables.enumStrings := PublicVariables.extract types in 
  let ()=propertiesRef:=TestParser.loop "flash_changed_Invs.invs" () in
  let properties=List.concat (List.map ~f:(preProcessProp) (!propertiesRef)) in
  let paraRef= paramfix "i" "NODE" (Intc(4)) in
  let dparaDef=paramdef "data" "DATA"  in
  let pair=("n_Store_Home101",[dparaDef]) in
  let pair1=("n_Store101",[dparaDef]) in
  let results=Cmp.cmpOnPrs properties ~types:types  paraRef  [1;2;3] ~unAbstractedReqs:[pair;pair1] rules in
  let ()=print_endline "----------------------/n" in
  let a=List.map ~f:(fun  r -> print_endline (ToMurphi.rule_act r)) (fst results) in
  let b=List.map ~f:(fun  f -> print_endline (ToMurphi.form_act f)) (snd results) in
  ()*)
