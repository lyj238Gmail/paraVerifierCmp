open Utils
open Core.Std

open Paramecium
open ToStr
open Formula

module FormulaCmp=Comparator.Make(struct
	type t=formula
	let sexp_of_t f =sexp_of_formula f
	let t_of_sexp s=formula_of_sexp s
  let compare x y= (String.compare (ToStr.Smv.form_act x) (ToStr.Smv.form_act y)) 
end)

let rec allSubFormofExp e= 
	match e with
    | Const(_)
    | Param(_)  
    | Var(_) -> Set.of_list [] ~comparator: FormulaCmp.comparator
    | Ite(f, e1, e2) ->  Set.union_list [allSubFormofForm   f; allSubFormofExp   e1; allSubFormofExp   e2] ~comparator: FormulaCmp.comparator
    | UIF(n, el) -> Set.union_list (List.map el ~f:(allSubFormofExp  )) ~comparator: FormulaCmp.comparator
  (** Names of formula *)
  and allSubFormofForm   f =
    match f with
    | Chaos
    | Miracle -> Set.of_list [] ~comparator: FormulaCmp.comparator
    | UIP(n, el) -> Set.union_list (List.map el ~f:(allSubFormofExp  )) ~comparator: FormulaCmp.comparator
    | Eqn(e1, e2) -> 
    	if String.Set.is_empty (VarNames.of_form f)  
    	then Set.of_list [] ~comparator: FormulaCmp.comparator
    	else Set.of_list [f] ~comparator: FormulaCmp.comparator
    | Neg(form) -> allSubFormofForm   form
    | AndList(fl)
    | OrList(fl) -> Set.union_list (List.map fl ~f:(allSubFormofForm  )) ~comparator: FormulaCmp.comparator
    | Imply(f1, f2) -> Set.union_list [allSubFormofForm   f1; allSubFormofForm   f2] ~comparator: FormulaCmp.comparator
    


let rec  allSubFormofStatement   s =
    match s with
    | Assign(v, e) -> Set.union_list [allSubFormofExp   e] ~comparator: FormulaCmp.comparator    
    | Parallel(slist) -> Set.union_list (List.map slist ~f:( allSubFormofStatement  )) ~comparator: FormulaCmp.comparator
    

let allSubFormofRule   r = 
    match r with
    | Rule(_, _, f, s) -> Set.union_list [allSubFormofForm   f;  allSubFormofStatement   s]    ~comparator: FormulaCmp.comparator

let allSubFormofRules rs= Set.union_list  (List.map rs ~f:( allSubFormofRule  ) ) ~comparator: FormulaCmp.comparator 
 
let normApplyProp (Prop(a,paradefs,f))=
	let len=List.length paradefs in
	let perm=up_to len in
	let paraPairs=List.zip paradefs perm in
	let paraPairs=match paraPairs with
				|None->[]
				|Some( paraPairs0)-> paraPairs0 in
	let paras=List.map ~f:(fun (Paramdef(n,t), i)-> Paramfix(n,t,Intc(i+1))) paraPairs in
	let nf=Paramecium.apply_form ~p:paras f in
	Prop(a,[],nf)
	
let normApplyRule	(Rule(n,paradefs,g,a))=
	let len=List.length paradefs in
	let perm=up_to len in
	let paraPairs=List.zip paradefs perm in
	let paraPairs=match paraPairs with
				|None->[]
				|Some( paraPairs0)-> paraPairs0 in
	let paras=List.map ~f:(fun (Paramdef(n,t), i)-> Paramfix(n,t,Intc(i+1))) paraPairs in
	Paramecium.apply_rule ~p:paras (Rule(n,paradefs,g,a))
	
	
let allSubFormofProt  prot=
	let { Paramecium.name = name0;
      Paramecium.types = types0;
      vardefs = vardefs0;
      init = new_init0;
      rules = new_rules0;
      properties = new_props0;
      }=prot in
  (*here we need an instantiation action*)
  (*let fs=List.map ~f:(fun p->normApplyProp2Form p) new_props0 in *)
  let fs=List.map ~f:(fun (Prop(n,paradefs,f)) -> f) new_props0 in
  let fsOfProp= (List.concat (List.map ~f:(fun f0 ->Formula.form2AllSymForms ~types:types0 ~f:f0) fs)) in  	  
  let fsOfProp=Set.union_list (List.map ~f: allSubFormofForm fsOfProp) ~comparator: FormulaCmp.comparator  in
  (*let rs=List.map ~f:normApplyRule new_rules0 in*)
  let fs=Set.to_list (allSubFormofRules  new_rules0)    in
  let fsOfRule=List.concat (List.map ~f:(fun f -> Formula.form2AllSymForms ~f:f ~types:types0) fs) in 
  let fsOfRule=Set.of_list fsOfRule ~comparator: FormulaCmp.comparator in 
  let s=Set.union_list [fsOfProp;fsOfRule]  ~comparator: FormulaCmp.comparator  in
  let ls=Set.of_list (Set.elements s) ~comparator: FormulaCmp.comparator  in
    Set.to_list ls
    
let formClosure  f r=
	let Rule(name,paradefs,g,act)=r in	  
	let sts =match act with	 
	|Assign(v,e)->[act]
	|Parallel(sts0) -> sts0 in	
	let assigns=List.map ~f:(fun (Assign(v,e)) ->   (v,e)) sts in
	let result=InvFinder.pre_cond f assigns in
	let fs=List.map ~f:snd result in
	let isf f=if (not (String.Set.is_empty (VarNames.of_form f)  ))
    	then  true 
    	else  false   in
  List.filter ~f:isf fs
	
let rec formsClosures fs rs  =
	let tmpf f=List.concat (List.map ~f:(formClosure  f) rs) in
	let tmps=List.concat (List.map ~f:tmpf fs) in
	let tmps=   (Set.of_list tmps ~comparator: FormulaCmp.comparator) in
	let fss=(Set.of_list fs ~comparator: FormulaCmp.comparator) in
	if	(Set.is_empty (Set.diff tmps fss) )
	then fs
	else (*let ()=print_endline "------------------------------"in
	let b=List.map ~f:(fun f -> print_endline (ToStr.Smv.form_act  f))
		 (Set.to_list (Set.union tmps fss)) in*)
	formsClosures (Set.to_list (Set.union tmps fss)) rs
	

	
let extract  prot   =
	 let { Paramecium.name = name0;
      types = types0;
      vardefs = vardefs0;
      init = new_init0;
      rules = new_rules0;
      properties = new_prop0;
      }=prot in 
   let newProt= { Paramecium.name = name0;
      types = types0;
      vardefs = vardefs0;
      init = new_init0;
      rules = List.concat (List.map ~f:(Formula.allPossibInst2Rule types0)  new_rules0);
      properties = List.map ~f:normApplyProp new_prop0;
      } in   
   let fls= (allSubFormofProt newProt) in
   formsClosures fls (newProt.rules)
   
let extractSubFormsByRule prot   =
	let { Paramecium.name = name0;
      types = types0;
      vardefs = vardefs0;
      init = new_init0;
      rules = new_rules0;
      properties = new_prop0;
      }=prot in 
   let newProt= { Paramecium.name = name0;
      types = types0;
      vardefs = vardefs0;
      init = new_init0;
      rules = List.concat (List.map ~f:(Formula.allPossibInst2Rule types0)  new_rules0);
      properties = List.map ~f:normApplyProp new_prop0;
      } in   
    
   let computeSubForms (r, i)=
   		let Rule(name, _, f, s)=r in
   		(name(*^(string_of_int i)*), Set.to_list (allSubFormofRule  r)) in
	 let  Some(pairs)=List.zip newProt.rules (up_to (List.length newProt.rules)) in
   List.map ~f:computeSubForms pairs
   
   	
   	
   
