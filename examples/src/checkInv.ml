
open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

module CheckInv=struct

let check_with_murphi form =
          let form_str = ToStr.Smv.form_act ~lower:false ( form) in
          let res = Murphi.is_inv form_str in
          print_endline (sprintf "Check by mu: %s, %b" form_str res); res

let startServer   ?(smv_escape=(fun inv_str -> inv_str))
    ?(smv="") ?(smv_ord="")   ?(murphi="")  murphiName smvName
    muServer smvServer ~types ~vardefs protocol=      
    
  let _smt_context = Smt.set_context murphiName (ToStr.Smt2.context_of ~insym_types:[] ~types ~vardefs) in
    
  let _mu_context = Murphi.set_context murphiName murphi in
   
  let _smv_context =
  	 if smv = "" then
        Smv.set_context ~escape:smv_escape smvName (Loach.ToSmv.protocol_act protocol) ~smv_ord
      else begin Smv.set_context ~escape:smv_escape smvName smv ~smv_ord end
   in
     ()
     
let mkSubstItem   (pdf, i)=
	let Paramdef(pn,pt)=pdf in
	let substItem=Paramecium.Paramfix(pn,pt,Intc(i )) in
	substItem
     
let check types prop=
	let Prop( name, params, inv)=prop in
	(*let subst1=	[Paramecium.Paramfix("i",indextype,Intc(index ));
		Paramecium.Paramfix("j",indextype,Intc(index  ));] in*)
	let actualParas=Utils.up_to ((List.length params) + 1) in	
	let Some(pairs)=List.zip params actualParas in
	let subst=List.map ~f:mkSubstItem pairs in
	let inv=apply_form ~p:subst inv in
	let inv=Trans.trans_formula  types inv in
	(*let ()=print_endline ((ToStr.Smv.form_act  inv)) in*)
	let c=Smv.is_inv (ToStr.Smv.form_act ( inv) ) in
	let b=try Smv.is_inv (ToStr.Smv.form_act ( inv) ) &&  ((not !Cmdline.confirm_with_mu) || check_with_murphi inv) with
          | Client.Smv.Cannot_check -> check_with_murphi inv
          | _ -> raise Utils.Empty_exception    in
  if b 
	then let ()=print_endline ((ToStr.Smv.form_act  inv)^"ok/n") in true
	else let ()=print_endline "failure" in false       
	

let checkProps types props=
	List.filter ~f:(fun x ->  check types x)  props

let checkInv types inv=
	let inv=Trans.trans_formula  types inv in
	let ()=print_endline ((ToStr.Smv.form_act  inv)) in
	let b=try Smv.is_inv (ToStr.Smv.form_act ( inv) ) &&  ((not !Cmdline.confirm_with_mu) || check_with_murphi inv) with
          | Client.Smv.Cannot_check -> check_with_murphi inv
          | _ -> raise Utils.Empty_exception    in
  if b 
	then let ()=print_endline ((ToStr.Smv.form_act  inv)^"ok/n") in true
	else let ()=print_endline "failure" in false   
	
	
let checkInvStr inv=
	let b=try Smv.is_inv inv &&  ((not !Cmdline.confirm_with_mu) || Murphi.is_inv inv) with
          | Client.Smv.Cannot_check -> Murphi.is_inv inv
          | _ -> raise Utils.Empty_exception    in
  if b 
	then let ()=print_endline (inv^"ok/n") in true
	else let ()=print_endline (inv^"failure") in false  
	
end

