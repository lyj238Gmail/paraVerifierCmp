 

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


let propertiesRef=ref [] 
let nodeNums=2

let propInstForRuleWith1Para pprops nodeNums=
	
	let mkActualParasForInv pprop=
		let Prop( name, params, pinv)=pprop in
		let range=Utils.up_to nodeNums in
		let paraRanges=if (List.length params=1)
			then (Utils.combination_permutation range 1) (*[[2]]*)
			else (  (Utils.combination_permutation [0;1;] 2)) 
						(*[[2;3]]*) in
		let paraNumPairsL=List.map ~f:(fun x-> List.zip params x) paraRanges in
		let mk paraNumPairs=
			let Some(paraNumPairs)=paraNumPairs in
					List.map
					 ~f:(fun (p,num)->let  Paramecium.Paramdef(pname,indextype)=p in  
					 Paramecium.Paramfix(pname,indextype,Intc(num + 1 )))
			 		paraNumPairs in  
		(List.map ~f:mk paraNumPairsL) in	
	
	let mkActualProps prop=
		let Prop( name, params, pinv)=prop	  in
		let inv2Prop f p=
			let inv'=apply_form ~p:p f in
			Prop( name^(ToMurphi.form_act inv'), [],inv') in
		let props=
			if (List.length params=0) then [prop]
			else List.map ~f:(fun p-> inv2Prop pinv p) (mkActualParasForInv prop) in
		props  in
	
		
	let props= 
		List.concat (List.map ~f:mkActualProps	pprops	) in
	props	
	

let main ()=
	let ()=Generalize.zero_special:=true in
  let ()=PublicVariables.enumStrings := PublicVariables.extract types in 
  let ()=propertiesRef:=TestParser.loop "german.invs" () in
  
  let props=propInstForRuleWith1Para (!propertiesRef) nodeNums in
  let a=List.map ~f:(fun  p -> print_endline (ToMurphi.prop_act p)) props in
  ()
  
let ()=main ()  
  (*let properties=List.concat (List.map ~f:(preProcessProp) (!propertiesRef)) in*)
  

