open Utils
open Paramecium
open Loach
open Core.Std

let table = Hashtbl.create ~hashable:String.hashable ()

let base_index = ref 0

let rename_ref = ref true

let next_name () = 
  let res = sprintf "p__Inv%d" (!base_index) in
  incr base_index; res

(** Convert paramref *)
let paramref_act ~generalizedtParas   pr pds pfs =
  
  match pr with
  | Paramref(_) -> (pds,pfs,pr) (*Prt.error (ToStr.Debug.paramref_act   pr^"\n"); raise Unexhausted_inst*)
  | Paramfix(vname, tname, c) ->
	if (List.mem  generalizedtParas c)
	then
	(*let ()=print_endline (ToStr.Debug.paramref_act   pr^"\n") in*)
	begin
    if (!rename_ref) then
      begin
	   (*)  let ()=print_endline (ToStr.Debug.paramref_act   pr^"enter rename=true\n") in*)
        let key = tname^ToStr.Debug.const_act  c in
        match Hashtbl.find table key with
        | None ->
          let new_name = next_name () in
          let new_pd = paramdef new_name tname in
          Hashtbl.replace table ~key ~data:new_pd;
          (new_pd::pds, paramfix new_name tname c::pfs, paramref new_name)
        | Some(Paramdef(vn, _)) ->
          let has = List.exists pds ~f:(fun (Paramdef(n, _)) -> n = vn) in
          let pds' = if has then pds else paramdef vn tname::pds in
          let pfs' = if has then pfs else paramfix vn tname c::pfs in
          (pds', pfs', paramref vn)
      end
    else begin
      match List.find pds ~f:(fun (Paramdef(vn, _)) -> vn = vname) with
      | None -> (paramdef vname tname::pds, pr::pfs, paramref vname)
      | Some(_) -> (pds, pfs, paramref vname)
    end
    end
	else (pds, pfs, pr)

(** Convert a list of components *)
let components_act ~generalizedtParas components pds pfs ~f =
  let rec wrapper components gened_comp pds pfs =
    match components with
    | [] -> (pds, pfs, gened_comp)
    | c::components' ->
      let (pds', pfs', c') = f c pds pfs in
      wrapper components' (gened_comp@[c']) pds' pfs'
  in
  wrapper components [] pds pfs

(** Convert var *)
let var_act ~generalizedtParas (Arr(ls)) pds pfs =
  let rec wrapper ls pds pfs res =
    match ls with
    | [] -> (pds, pfs, res)
    | (n, prs)::ls' ->
      let (pds', pfs', prs') = components_act ~generalizedtParas:generalizedtParas prs pds pfs ~f:(paramref_act ~generalizedtParas:generalizedtParas) in
      wrapper ls' pds' pfs' (res@[(n, prs')])
  in
  let (pds', pfs', ls') = wrapper ls pds pfs [] in
  (pds', pfs', arr ls')

(** Convert exp *)
let rec exp_act ~generalizedtParas e pds pfs =
  match e with
  | Const(_) -> (pds, pfs, e)
  | Var(v) ->
    let (pds', pfs', v') = var_act ~generalizedtParas v pds pfs in
    (pds', pfs', var v')
  | Param(pr) ->
    let (pds', pfs', pr') = paramref_act  ~generalizedtParas:generalizedtParas pr pds pfs in
    (pds', pfs', param pr')
  | UIF(n, el) ->
    let (pds', pfs', el') = components_act ~generalizedtParas:generalizedtParas el pds pfs ~f:(exp_act ~generalizedtParas:generalizedtParas) in
    (pds', pfs', uif n el')
  | Ite(_, _, _) -> raise Empty_exception

(** Convert formula *)
let form_act ~generalizedtParas ?(rename=true) f pds pfs=
  rename_ref := rename;
  let rec wrapper f pds pfs =
    match f with
    | Chaos
    | Miracle -> (pds, pfs, f)
    | UIP(n, el) ->
      let (pds', pfs', el') = components_act ~generalizedtParas:generalizedtParas el pds pfs ~f:(exp_act ~generalizedtParas:generalizedtParas) in
      (pds', pfs', uip n el')
    | Eqn(e1, e2) ->
      let (pds1, pfs1, e1') = exp_act ~generalizedtParas:generalizedtParas e1 pds pfs in
      let (pds2, pfs2, e2') = exp_act ~generalizedtParas:generalizedtParas e2 pds1 pfs1 in
      (pds2, pfs2, eqn e1' e2')
    | Neg(f) ->
      let (pds', pfs', f') = wrapper f pds pfs in
      (pds', pfs', neg f')
    | AndList(fl) ->
      let (pds', pfs', fl') = components_act ~generalizedtParas:generalizedtParas fl pds pfs ~f:wrapper in
      (pds', pfs', andList fl')
    | OrList(fl) ->
      let (pds', pfs', fl') = components_act ~generalizedtParas:generalizedtParas fl pds pfs ~f:wrapper in
      (pds', pfs', orList fl')
    | Imply(f1, f2) ->
      let (pds1, pfs1, f1') = wrapper f1 pds pfs in
      let (pds2, pfs2, f2') = wrapper f2 pds1 pfs1 in
      (pds2, pfs2, imply f1' f2')
    | ForallFormula(pds0,pf) ->
    	let (pds', pfs', f') = wrapper pf pds pfs in
    	(pds', pfs', ForallFormula(pds0, f'))
    	
  	| ExistFormula(pds0,pf) ->
  	let (pds', pfs', f') = wrapper pf pds pfs in
    	(pds', pfs', ExistFormula(pds0, f'))
  in
  let (pds, pfs, f') = wrapper f pds pfs in
  let sorted_pds =
    pds
    |> List.dedup ~compare:(fun pd1 pd2 ->
      String.compare (ToStr.Debug.paramdef_act   pd1) (ToStr.Debug.paramdef_act   pd2))
    |> List.sort ~cmp:(fun (Paramdef(n1, _)) (Paramdef(n2, _)) -> String.compare n1 n2)
    |> List.sort ~cmp:(fun (Paramdef(_, tn1)) (Paramdef(_, tn2)) -> String.compare tn1 tn2)
  in
  let sorted_pfs =
    pfs
    |> List.dedup ~compare:(fun pf1 pf2 ->
      String.compare (ToStr.Debug.paramref_act   pf1) (ToStr.Debug.paramref_act   pf2))
    |> List.sort ~cmp:(fun pf1 pf2 -> String.compare (name_of_param pf1) (name_of_param pf2))
    |> List.sort ~cmp:(fun pf1 pf2 ->
      let typenameof pf =
        match pf with
        | Paramref(_) -> raise Unexhausted_inst
        | Paramfix(_, tn, _) -> tn
      in
      String.compare (typenameof pf1) (typenameof pf2)
    )
  in
  (*Prt.info (ToStr.Debug.form_act   f^"\n"^ToStr.Debug.form_act   f'^", "^
    (String.concat (List.map sorted_pfs ~f:ToStr.Debug.paramref_act  ))^"\n")*)
  (sorted_pds, sorted_pfs, f')

let rec statement_act ~generalizedtParas ?(rename=true) statement  pds pfs =


	rename_ref := rename;
	
  let rec wrapper statement pds pfs =
  
  match statement with
  
  | Assign(v, e) -> 
  
  	let (pdsv, pfsv, v')=
  	(var_act ~generalizedtParas:generalizedtParas v pds pfs) in
  	
  	let (pdse, pfse, e') =
  	(exp_act ~generalizedtParas:generalizedtParas e pdsv pfsv) in
  	
  	 
  	(pdse, pfse, assign v'  e')
  	
  | Parallel(sl) -> 
  
  	 let (pds', pfs', sl') = components_act ~generalizedtParas:generalizedtParas sl pds pfs ~f:wrapper in
  	 
      (pds', pfs', parallel sl')
  
  | IfStatement(f, s) ->
  	let (pds', pfs', f')= form_act ~generalizedtParas:generalizedtParas ~rename:rename  f pds pfs in
  	
  	let (pdss',pfss', s')=statement_act ~generalizedtParas:generalizedtParas ~rename:rename   s pds' pfs' in
  	
  	 (pdss',pfss',
  	 	ifStatement f'  s')
  
  | IfelseStatement(f, s1, s2) ->
    let (pds', pfs', f')= form_act ~generalizedtParas:generalizedtParas ~rename:rename   f pds pfs in
  	
  	let (pdss',pfss', s1')=statement_act ~generalizedtParas:generalizedtParas ~rename:rename   s1 pds' pfs' in
  	
  	let (pdss'',pfss'', s2'')=statement_act ~generalizedtParas:generalizedtParas ~rename:rename   s2 pdss' pfss' in
  	(pdss'',pfss'',
  	 	ifelseStatement f'  s1' s2'')
  
  		
  | ForStatement(s, pd) ->
  	 	let (pds', pfs', s')= statement_act ~generalizedtParas:generalizedtParas  ~rename:rename  s pds pfs  in
  	 	
    (pds', pfs', ForStatement(s', pd)) 
  in
  let (pds, pfs, f') = wrapper statement pds pfs in
  let sorted_pds =
    pds
    |> List.dedup ~compare:(fun pd1 pd2 ->
      String.compare (ToStr.Debug.paramdef_act   pd1) (ToStr.Debug.paramdef_act   pd2))
    |> List.sort ~cmp:(fun (Paramdef(n1, _)) (Paramdef(n2, _)) -> String.compare n1 n2)
    |> List.sort ~cmp:(fun (Paramdef(_, tn1)) (Paramdef(_, tn2)) -> String.compare tn1 tn2)
  in
  let sorted_pfs =
    pfs
    |> List.dedup ~compare:(fun pf1 pf2 ->
      String.compare (ToStr.Debug.paramref_act   pf1) (ToStr.Debug.paramref_act   pf2))
    |> List.sort ~cmp:(fun pf1 pf2 -> String.compare (name_of_param pf1) (name_of_param pf2))
    |> List.sort ~cmp:(fun pf1 pf2 ->
      let typenameof pf =
        match pf with
        | Paramref(_) -> raise Unexhausted_inst
        | Paramfix(_, tn, _) -> tn
      in
      String.compare (typenameof pf1) (typenameof pf2)
    )
  in
  (*Prt.info (ToStr.Debug.form_act   f^"\n"^ToStr.Debug.form_act   f'^", "^
    (String.concat (List.map sorted_pfs ~f:ToStr.Debug.paramref_act  ))^"\n")*)
  (sorted_pds, sorted_pfs, f')  
      
let rule_act ~generalizedtParas ?(rename=true) r=
	rename_ref := rename;

	let  Loach.Rule(name,paramdefs,g, act)=r in
	let (pds,pfs,pg)=form_act ~rename:rename ~generalizedtParas:generalizedtParas g [] [] in
	let (pds',pfs',act')=statement_act  ~rename:rename  
	~generalizedtParas:generalizedtParas act pds pfs in  
  let sorted_pds =
    pds'
    |> List.dedup ~compare:(fun pd1 pd2 ->
      String.compare (ToStr.Debug.paramdef_act   pd1) (ToStr.Debug.paramdef_act   pd2))
    |> List.sort ~cmp:(fun (Paramdef(n1, _)) (Paramdef(n2, _)) -> String.compare n1 n2)
    |> List.sort ~cmp:(fun (Paramdef(_, tn1)) (Paramdef(_, tn2)) -> String.compare tn1 tn2)
  in
  let sorted_pfs =
    pfs'
    |> List.dedup ~compare:(fun pf1 pf2 ->
      String.compare (ToStr.Debug.paramref_act   pf1) (ToStr.Debug.paramref_act   pf2))
    |> List.sort ~cmp:(fun pf1 pf2 -> String.compare (name_of_param pf1) (name_of_param pf2))
    |> List.sort ~cmp:(fun pf1 pf2 ->
      let typenameof pf =
        match pf with
        | Paramref(_) -> raise Unexhausted_inst
        | Paramfix(_, tn, _) -> tn
      in
      String.compare (typenameof pf1) (typenameof pf2)
    )
  in
  (*Prt.info (ToStr.Debug.form_act   f^"\n"^ToStr.Debug.form_act   f'^", "^
    (String.concat (List.map sorted_pfs ~f:ToStr.Debug.paramref_act  ))^"\n")*)
  Loach.Rule(name,paramdefs@sorted_pds,pg, act')  	
  
let concreteInv2ParamProp  inv i=
	let paras=Int.Set.to_list (ParasOf.of_form inv) in
	let (pds,pfs,pg)=form_act ~rename:false ~generalizedtParas:(List.map ~f:intc paras) inv [] [] in
	  Prop(string_of_int i, pds,pg)
	
