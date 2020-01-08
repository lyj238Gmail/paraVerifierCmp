open Loach

open Utils
open Core.Std


open ToStr

	let dict = Core.Std.Hashtbl.create ~hashable:Core.Std.String.hashable ()
	let invsInsts=ref []
	let prulesRef= ref []
	
let getInsInstsForRuleWithParam1	()=
	let Some(invs)=List.hd (!invsInsts) in
	invs
	
let getInsInstsForRuleWithParam2 ()	=
	let Some(invs)=List.hd (List.rev (!invsInsts)) in
	invs	
		
	
	(*let param_alpha_eq para1 para2 =
		match para1 with 
			|Paramfix(pn,pt,i) ->
				match para2 with
					|Paramfix(pn',pt',i') ->
						if (pt=pt') then i=i'
						else false
					|_ ->false
			|Paramref(pn)	->
				match para2 with
					|Paramfix(pn',pt',i') ->
						false
					|Paramref(pn')->pn=pn'	
					
	let var_alpha_eq para1 para2 =*)	
					
(*decide if antOf inv ==> guardOF rule *)
let loachImply ant cons types=

	  
		(*let ()=print_endline ("ant="^(ToMurphi.form_act ant)) in
		let ()=print_endline ("cons="^(ToMurphi.form_act cons)) in*)
		let ant=Loach.Trans.trans_formula types ant in
		let cons=Loach.Trans.trans_formula types cons in
		let b=not(Formula.is_satisfiable (Neg( (Paramecium.imply    ant     cons)))) in
		(*let ()=if b then (print_endline "ok") else (print_endline "fault") in*)
		b
		
let setImply ant cons types=		
	let ant=Loach.Trans.trans_formula types ant in
	let cons=Loach.Trans.trans_formula types cons in
	let strOfgsOfAnt= List.map ~f:(ToStr.Smv.form_act) (Formula.flat_and_to_list ant) in
	let strOfgsOfCons= List.map ~f:(ToStr.Smv.form_act)  (Formula.flat_and_to_list cons) in
		Utils.list_subset strOfgsOfCons strOfgsOfAnt
		
let relate inv ~rule ~types=
		
		let Loach.Rule(name,paramdefs,g, act)=rule in		
		let (invName,inv)=inv  in
		let Loach.Imply(ant,cons)=inv in
		 (*setImply g ant types*)
		loachImply g ant types 
		(*let ant=Loach.Trans.trans_formula types ant in
		let g=Loach.Trans.trans_formula types g in*)
		(*Formula.is_tautology (Paramecium.imply  g ant)*)
		(*there is two kinds of implementation: *)
		(*1. Formula.is_tautology (Paramecium.imply  ant g)*)
		(*2. transForm forms into strings, and compare the subseteq relation*)
		(*let strOfgsOfAnt= List.map ~f:(ToStr.Smv.form_act) (Formula.flat_and_to_list ant) in
		let strOfgsOfg= List.map ~f:(ToStr.Smv.form_act)  (Formula.flat_and_to_list g) in
		Utils.list_subset strOfgsOfAnt strOfgsOfg*)

(*let vardefs = List.concat [
  [arrdef [("n", [paramdef "i0" "client"])] "state"];
  [arrdef [("x", [])] "boolean"]
]
 
  let params = [paramdef "i" "client"] in
  let formula = (eqn (var (arr [("n", [paramref "i"])])) (const _I)) in
  let statement = (assign (arr [("n", [paramref "i"])]) (const _T)) in
*)

(*decide wehther index of paramref1 is equal to index*)
(*,which is a int*)
let onlyOnParamRef index paramref1=
	match paramref1 with 
			|Paramecium.Paramfix(pname,vname, Intc(index'))->index=index'
			|_->false

let onlyOnStrParamRefs index arrAcesses=
	let paraRefs=List.concat (List.map ~f:(fun x -> snd x) arrAcesses) in
 	let judges=List.map ~f:(onlyOnParamRef index) paraRefs in
		List.fold ~f:(fun x y ->x || y) ~init:false judges
		
let onlyOnStrsParamRefs indexs arrAcesses=		
	let judges=List.map ~f:(fun i -> onlyOnStrParamRefs i arrAcesses) indexs in
		List.fold ~f:(fun x y ->x || y) ~init:false judges
		
(*limitation! now we only deal one-arity like a[1], a[2],a[1].global, or a.g.s[1]
notice the formal def of paramRef above,
Index i is on a[i]  List.fold ~init:true ~f:(fun res x -> res && x)
*)			
let onlyOnVar index var=		
		match var with
		|Paramecium.Arr(ls)->onlyOnStrParamRefs index ls
		(*let paraRefs=List.concat (List.map ~f:(fun x -> snd x) ls) in
		List.fold ~f:(fun x y ->x || y) ~init:false paraRefs*)
			
		|_->false
		
let onlyOnVars absIndexs var=
	List.fold ~f:(fun y index -> (onlyOnVar index var) || y) absIndexs ~init:true

		
(*expression exp is on index index*)		
let onExp index exp=	
	match exp with
		Var(v) -> onlyOnVar index v
		|_ ->false
		
(*Formula f is on index*)
let rec onFormula index formula=
	(*let ()=print_endline ((ToMurphi.form_act formula)) in*)
	match formula with
		|Loach.Eqn(e1,e2) -> (onExp index e1) || (onExp index e2)
		|Neg(f) -> 		onFormula index  f
		|ForallFormula(d,f) -> onFormula index  f   (*false	*)
		|Chaos ->false
		|Miracle ->false
		|AndList(ls) -> List.fold ls ~f:(fun x y -> x || (onFormula index y)) ~init:false
		|Imply(f1,f2) -> (onFormula index  f1) || (onFormula index  f2)
		|OrList(ls) -> List.fold ls ~f:(fun x y -> x || (onFormula index y)) ~init:false
		|ExistFormula(d,f) -> onFormula index  f  
		
let  onFormulas absIndexs formula=
	List.fold ~f:(fun b i -> b || 		(onFormula i formula)) absIndexs ~init:false
		
(*require all the sub-assignments are on index
require that the caller call this statementAllOn, either statement is an 
assignment or it is a for-statement*)			
let rec  statementAllOn index statement= 
	match statement with
	|Assign(var,value) ->  onlyOnVar index var 
	|Parallel(statementList) -> 
		List.fold  (List.map ~f:( statementAllOn index) statementList) 
		 ~f:(fun x y -> x && y) ~init:true
	|IfStatement(bcond,statement) ->
		 statementAllOn index statement
	|IfelseStatement(b,s1,s2) ->
	 ( statementAllOn index s1) && ( statementAllOn index s2)
	|ForStatement(s,parmDefs) ->false
		(*regularForStatement(s)*)
		
let statementAllOnIndexs absIndexs  st		=
	List.fold ~f:(fun  y index->statementAllOn index st || y) absIndexs ~init:false

let  onlyOnRule index rule=
	let Rule(name,paraDefs,g,statement)=rule in
		 statementAllOn index statement	
		
(*(forallFormula [paramdef "j" "NODE"] (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))])*)	
(*let alpha_rename_forallForm  (ForallFormula(pds,pf)) paramRefs =
	let Some(ls)=(List.zip pds paramRefs) in 
	let pds'=List.map ~f:(fun (Paramdef(pn,pt),Paramfix(pn',pt',i))->Paramdef(pn',pt)) ls in
	let paramRefs'=List.map ~f:(fun (Paramdef(pn,pt),Paramfix(pn',pt',i))->Paramref(pn')) ls in
	
	let pf'=apply_form ~p:paramRefs' pf in
	ForallFormula(pds',pf')
	
Give a concrete invariant: A -> B: 
and a paramRef containing an index
if index does not occur in A, we need generalize B; otherwise just B
e.g., a[1]=E--> x=false, index is 1, its result is x=false; but
cache[1]=E-->cache[2]=I, index is 1, its result forall i. cache[i]=I*)
module FormulaCmp=Comparator.Make(struct
	type t=Loach.formula
	let sexp_of_t f =Loach.sexp_of_formula f
	let t_of_sexp s=Loach.formula_of_sexp s
  let compare x y= String.compare (ToMurphi.form_act x) (ToMurphi.form_act y) 
    
end)

module NameFormulaCmp=Comparator.Make(struct
	type t=string*Loach.formula
	let sexp_of_t (str,f) =Loach.sexp_of_formula f
	let t_of_sexp s=Loach.formula_of_sexp s
  let compare (s1,x) (s2, y)= String.compare (ToMurphi.form_act x) (ToMurphi.form_act y) 
    
end)
open Core.Std	
let drawConclusion absIndexs types  oldConclusions invaraint=	
	(*let Paramecium.Paramfix(pname,indextype,Intc(index))=paramRef in*)
	let Imply(ant,cons)=snd invaraint in	
	(*let ()=print_endline (ToMurphi.form_act ( invaraint))  in*)
	let antParams=Loach.ParasOf.of_form ant in
	let consParams=Loach.ParasOf.of_form cons in
	let absIndexSet=Int.Set.of_list absIndexs in
	let add conclusion= 
	
		let isForall 	conclusion=
			 match conclusion with
			|ForallFormula(_,_) ->  true
			|_ ->false in
		let parasOfCon=(Loach.ParasOf.of_form conclusion) in	
		if (not (Set.is_empty  parasOfCon)) && (Set.is_empty (Set.inter parasOfCon  absIndexSet)) then
		[]
		else 
		(*if List.mem oldConclusions conclusion then*)
		let oldSet=(Set.of_list oldConclusions ~comparator: FormulaCmp.comparator) in
		if (Set.mem  oldSet conclusion) then
		 [] 
	else 
		if List.length absIndexs=2 then
		match conclusion with
		|ForallFormula(_,_) ->[conclusion] 
		|_ -> if (Int.Set.is_empty (Int.Set.diff (Loach.ParasOf.of_form conclusion) absIndexSet)) then
						[conclusion]
					else [] 
		else [conclusion] in
	
	
	
	let generalizedParas=
		if (Int.Set.is_empty antParams)
		then consParams
		else Int.Set.diff consParams antParams in
	let generalizedParas=Int.Set.diff 	generalizedParas absIndexSet in
	 if (Int.Set.is_empty generalizedParas) then
	 add cons
	 else 
	 let (pds,prs,pf)=LoachGeneralize.form_act 
		 	~generalizedtParas:( Paramecium.int_consts (Int.Set.to_list generalizedParas)) ~rename:false cons [] [] in
		 	let f=ForallFormula(pds, pf)  in
		 	add f
	(*if (Int.Set.is_empty antParams) then
		begin
			if (Int.Set.is_empty consParams)  then
				add cons
			else 
			let conclusions0=add cons in
			let (pds,prs,pf)=LoachGeneralize.form_act 
		 	~generalizedtParas:( Paramecium.int_consts (Int.Set.to_list generalizedParas)) ~rename:false cons [] [] in
		 	let f=ForallFormula(pds, pf)  in
			let conclusions1=add f in
			if (Int.Set.is_empty (Int.Set.diff consParams absIndexSet)) then (*consParas <=absIndexs e.g. consParas=[3] *)
				conclusions0@conclusions1
			else conclusions1
		end
	else
		begin
		if (Int.Set.is_empty generalizedParas) then
			begin
			let conclusions0=add cons in
			let (pds,prs,pf)=LoachGeneralize.form_act 
		 	~generalizedtParas:( Paramecium.int_consts (Int.Set.to_list (Int.Set.diff consParams absIndexSet))) ~rename:false cons [] [] in
		 	let f=ForallFormula(pds, pf)  in
			let conclusions1=add f in
			if (Int.Set.is_empty (Int.Set.diff consParams absIndexSet)) then (*consParas <=antParas; consParas <=absIndexs e.g. consParas=[3] *)
				conclusions0
			else conclusions1	
			end
		else
			let (pds,prs,pf)=LoachGeneralize.form_act 
			 	~generalizedtParas:( Paramecium.int_consts (Int.Set.to_list generalizedParas)) ~rename:false cons [] [] in
			let f=ForallFormula(pds, pf)  in	
				add f 
		end
	       	*)
		
		(*else Int.Set.diff consParams (Int.Set.of_list [index]) in*)
		
	(*let generalizedParas= 
		if (Int.Set.is_empty generalizedParas) && (not (Int.Set.is_empty consParams)) 
		then consParams
		else  generalizedParas in*)
	
	(*let matchVarDo var oldParamRefs=
		match var with
		|Paramecium.Arr(ls)->
		 	if   (Int.Set.is_empty generalizedParas)
		 	then begin if List.mem oldConclusions cons then [] else [cons] end 
		 	else 
		 	let (pds,prs,pf)=LoachGeneralize.form_act 
		 	~generalizedtParas:( Paramecium.int_consts (Int.Set.to_list generalizedParas)) ~rename:false cons [] [] in
		 	let f=ForallFormula(pds, pf)  in
		 	begin 
		 		if List.mem oldConclusions f 
		 		then []
		 	  else [f]
		 	end*)
			(*
				if (onlyOnVar index var)
				then 
				begin
					if (not(onFormula index ant) )
					then 
						let (pds,prs,pf)=Generalize.form_act (Trans.trans_formula  ~types:types cons) in	
						let f=
							match pds with
							|[]-> cons
							|_-> (ForallFormula(pds,Trans.invTrans_formula pf)) in
						(*if List.mem oldConclusions  f then []*)
						if loachImply (Loach.AndList(oldConclusions)) f types then []
						else [ f]
					else
					begin
					if List.mem oldConclusions cons then []
					(*if loachImply (Loach.AndList(oldConclusions)) cons types then []*)
					else [cons]  (*case1:cons == a[index]=v*) 
					end
				end
				else				
					let (pds,prs,pf)=Generalize.form_act (Trans.trans_formula  ~types:types cons) in	
					let f=
					match pds with
					|[]-> cons
					|_-> (ForallFormula(pds,Trans.invTrans_formula pf)) in
					
					(*if List.mem oldConclusions  f then []*)
					if loachImply (Loach.AndList(oldConclusions)) f types then []
					else [ f]
			
		|_-> begin if List.mem oldConclusions cons then [] else [cons] end 	in*)
	(*let ()=print_endline (ToMurphi.form_act ( cons))  in	*)
	(*match cons with
	|Eqn(Var(var),value)	-> 
		let Paramecium.Arr(arrAcesses) = var in
		let paraRefs=List.concat (List.map ~f:(fun x -> snd x) arrAcesses) in
		matchVarDo var paraRefs
	|Neg(Eqn(Var(var),value))	->
		let Paramecium.Arr(arrAcesses) = var in
		let paraRefs=List.concat (List.map ~f:(fun x -> snd x) arrAcesses) in
		matchVarDo var paraRefs*)
	
	
(*let rec drawConclusions paramRef types oldConclusions invs =*)
let rec drawConclusions absIndexs types oldConclusions invs =
	match invs with
	|[] -> oldConclusions
	|inv::invs' ->let cons=(drawConclusion absIndexs types oldConclusions inv) in
								drawConclusions absIndexs types (cons@oldConclusions) invs'

(*The form of rule and invariant is the key!
invs=[..., inv,...], where inv is concrete, e.g., inv= n[other]=c--> x=false, where usually other is a constant 3;
both r and invs are concrete
paraRef contains an index which usuall is the "other" 
using all invariants to strengthen the guard of a rule by incrementally 
adding conclusions of invariants*)
let rec cmpStrengthRule invs  ~types absIndexs (r, usedInvs)=
	(*let Paramecium.Paramfix(pname,indextype,Intc(index))=paramRef in*)
	let Rule(name,paramdefs,g, act)=r  in	
	
	let ()=print_endline "----------------------------\n" in
	let ()=print_endline name in
	let ()=if (loachImply g Miracle types) then 
							print_endline "-------Miracle occurs--------\n"
							else () in
	let ()=print_endline (ToMurphi.rule_act r) in
	let invsRelated=List.filter ~f:(relate ~rule:r ~types: types) invs in	
	let ()=print_endline "-------invS related--------\n" in
	let b=List.map ~f:(fun finv -> print_endline  (ToMurphi.form_act (snd finv))) invsRelated in
	let ()=print_endline "----------------------------\n" in
		match	invsRelated with
		|[]->   Some(r, usedInvs)
		|_ ->
			 
			let conclusions=  (drawConclusions absIndexs types   [] invsRelated)  in
			let ()=print_endline "-------conclusions drawed--------\n" in
			let b=List.map ~f:(fun finv -> print_endline  (ToMurphi.form_act finv)) (List.rev conclusions) in
			let ()=print_endline "----------------------------\n" in
			if conclusions=[] then Some(r, usedInvs)
			else
				
				let gs=Loach.flat_loach_and_to_list g in
				let g=andList (gs@conclusions) in
				(*let action=rightSubByInvs act index invs in*)
				
				if (loachImply g Miracle types) then 
						let()=	print_endline "-------Miracle occurs--------\n" in
						None
				else 
					let newR=Rule(name,paramdefs,g, act) in
					let invs'=List.filter ~f:(fun x->not (List.mem invsRelated x)) invs in
					cmpStrengthRule invs' types absIndexs (newR, usedInvs@invsRelated)
				
(*make sure paramRef is a proper actual parameter to instantisate pr*) 	
let rec upto n=
	if (n=0) then []
	else (upto (n - 1))@[n]


	
let propInstForRuleWith1Para pprops ~types paramRef=
	let  Paramecium.Paramfix(pname,indextype,Intc(index))=paramRef in
	
	let mkActualParasForInv pprop=
		let Prop( name, params, pinv)=pprop in
		let paraRanges=if (List.length params=1)
			then ([[0];[1];[2]]) (*[[2]]*)
			else (  (Utils.combination_permutation [0;1;2] 2)) 
						(*[[2;3]]*) in
		let paraNumPairsL=List.map ~f:(fun x-> List.zip params x) paraRanges in
		let mk paraNumPairs=
			let Some(paraNumPairs)=paraNumPairs in
					List.map
					 ~f:(fun (p,num)->let  Paramecium.Paramdef(pname,indextype)=p in  
					 Paramecium.Paramfix(pname,indextype,Intc(num+index -2 )))
			 		paraNumPairs in  
		(List.map ~f:mk paraNumPairsL) in	
	(*let subst1=	[[Paramecium.Paramfix("i",indextype,Intc(index ));
		Paramecium.Paramfix("j",indextype,Intc(index  ));]] in
	let subst2=[[Paramecium.Paramfix("i",indextype,Intc(index ));
		Paramecium.Paramfix("j",indextype,Intc(index - 1 ));]] in 		
	;[Paramecium.Paramfix("j",indextype,Intc(index ));
		Paramecium.Paramfix("i",indextype,Intc(index +1 ));]*)	 
	let mkActualProps prop=
		let Prop( name, params, pinv)=prop	  in
		if (List.length params=0) then [(name,pinv)]
		else List.map ~f:(fun p-> (name,apply_form ~p:p pinv)) (mkActualParasForInv prop) in
		(*if (List.length params=1) then
		List.map ~f:(fun p-> apply_form ~p:p pinv) subst1
		else List.map ~f:(fun p-> apply_form ~p:p pinv) subst2 in*) (*(mkActualParasForInv prop) in*)
		
	let invs= 
		List.concat (List.map ~f:mkActualProps	pprops	) in
	let  invs=Set.elements (Set.of_list invs ~comparator: NameFormulaCmp.comparator) in 	
		invs
		
let propInstForRuleWith2Para pprops ~types paramRef=
	let  Paramecium.Paramfix(pname,indextype,Intc(index))=paramRef in
	
	let mkActualParasForInv pprop=
		let Prop( name, params, pinv)=pprop in
		let paraRanges=if (List.length params=1)
			then ([[0];[1];[2];[3]]) (*[[2];[3]]*)
			else (  (Utils.combination_permutation [0;1;2;3] 2)) in
		let paraNumPairsL=List.map ~f:(fun x-> List.zip params x) paraRanges in
		let mk paraNumPairs=
			let Some(paraNumPairs)=paraNumPairs in
					List.map
					 ~f:(fun (p,num)->let  Paramecium.Paramdef(pname,indextype)=p in 
					  Paramecium.Paramfix(pname,indextype,Intc(num+index -2 )))
			 		paraNumPairs in  
		(List.map ~f:mk paraNumPairsL) in	
	(*let subst1=	[[Paramecium.Paramfix("i",indextype,Intc(index ));
		Paramecium.Paramfix("j",indextype,Intc(index +1 ));]] in
	let subst2=[[Paramecium.Paramfix("i",indextype,Intc(index ));
		Paramecium.Paramfix("j",indextype,Intc(index +1 ));]; 		
	 [Paramecium.Paramfix("i",indextype,Intc(index ));
		Paramecium.Paramfix("j",indextype,Intc(index - 1 ));]] in	 *)
	let mkActualProps prop=
		let Prop( name, params, pinv)=prop	  in
		if (List.length params=0) then [(name,pinv)]
		(*else if (List.length params=1) then
		List.map ~f:(fun p-> apply_form ~p:p pinv) subst1
		else List.map ~f:(fun p-> apply_form ~p:p pinv) subst2 in *)
		else List.map ~f:(fun p-> (name,apply_form ~p:p pinv)) (mkActualParasForInv prop) in
		
	let invs= 
		List.concat (List.map ~f:mkActualProps	pprops	) in
	let  invs=Set.elements (Set.of_list invs ~comparator: NameFormulaCmp.comparator) in 	
		invs
(*tranform parameterized  locah properties into concrete	loach formulas *)
let properties2invs pprops ~types paramRef=
	let  Paramecium.Paramfix(pname,indextype,Intc(index))=paramRef in
	
	(*let mkActualParasForInv pprop=
		let Prop( name, params, pinv)=pprop in
		let paraRanges=if (List.length params=1)
			then ([[1];[2]])
			else (  (Utils.permutation (upto  (List.length params)))) in
		let paraNumPairsL=List.map ~f:(fun x-> List.zip params x) paraRanges in
		let mk paraNumPairs=
			let Some(paraNumPairs)=paraNumPairs in
					List.map
					 ~f:(fun (p,num)->let  Paramecium.Paramdef(pname,indextype)=p in  Paramecium.Paramfix(pname,indextype,Intc(num+index -1 )))
			 		paraNumPairs in  
		(List.map ~f:mk paraNumPairsL) in	*)
	let subst1=	[[Paramecium.Paramfix("i",indextype,Intc(index ));
		Paramecium.Paramfix("j",indextype,Intc(index  ));]] in
	let subst2=[[Paramecium.Paramfix("i",indextype,Intc(index ));
		Paramecium.Paramfix("j",indextype,Intc(index +1 ));]] in 		
	(*;[Paramecium.Paramfix("j",indextype,Intc(index ));
		Paramecium.Paramfix("i",indextype,Intc(index +1 ));]*)	 
	let mkActualProps prop=
		let Prop( name, params, pinv)=prop	  in
		if (List.length params=0) then [pinv]
		(*else if (List.length params=1) then
		List.map ~f:(fun p-> apply_form ~p:p pinv) subst1*)
		else List.map ~f:(fun p-> apply_form ~p:p pinv) subst2 in (*(mkActualParasForInv prop) in*)
		
	let invs= 
		List.concat (List.map ~f:mkActualProps	pprops	) in
		invs
				
(*let cmpStrengthPrInvs invs ~types paramRef pr=		
	(*let Paramfix(pname,indextype,Intc(index))=paramRef in
	let mkActualParasForInv pprop=
		let Prop( name, params, pinv)=pprop in
		let paraNumPairsL=List.map ~f:(fun x-> List.zip params x) (  (Utils.permutation (upto  (List.length params)))) in
		let mk paraNumPairs=
			let Some(paraNumPairs)=paraNumPairs in
					List.map
					 ~f:(fun (p,num)->let Paramdef(pname,indextype)=p in Paramfix(pname,indextype,Intc(num+index)))
			 		paraNumPairs in  
		(List.map ~f:mk paraNumPairsL) in
	 		 
	let mkActualProps prop=
		let Prop( name, params, pinv)=prop	  in
		List.map ~f:(fun p-> apply_form ~p:p pinv) (mkActualParasForInv prop) in
		
	let invs= 
		List.concat (List.map ~f:mkActualProps	pprops	) in*)
	let Paramfix(pname,indextype,Intc(index))=paramRef in	
	let r=apply_rule ~p:[paramRef] ~types pr in
	let onlyAffect=  onlyOnRule  index r in
	if onlyAffect then None
	else Some(cmpStrengthRule invs  ~types:types paramRef r)*)
	
(*If a guard g is on index, then remove it*)
let refineGuard absIndexs g=
	if onFormulas absIndexs g then []
	else [g]
	
exception CanNotDoRefine
(*refine simple actions of a statement
here either an assignment or a for assignment is simple,
if dict maps a array-element variable a[i] to a global variable x, then replace 
y:=a[i] with y:=x*)
let refineAct types dict absIndexs simpleAct=
	match simpleAct with
	|Assign(v,e) ->
		 begin 
		 match e	with 
		 |Var(Arr(ls))->
		 	if (onlyOnStrsParamRefs absIndexs ls) 
		 	then let eOption=Core.Std.Hashtbl.find dict 
		 							(ToStr.Smv.exp_act (Trans.trans_exp ~types:types (e)))  in
		 						(*let ()=print_endline 	(ToStr.Smv.exp_act (Trans.trans_exp ~types:types (Var(v)))) in
		 						let ()=print_endline 	(ToStr.Smv.exp_act (Trans.trans_exp ~types:types (e))) in*)
		 						match eOption with
		 						|Some(e') -> Assign(v,e')
								|None -> let ()=print_endline (ToMurphi.statement_act simpleAct) in raise CanNotDoRefine
			else simpleAct
		|_ ->simpleAct
		end
	|ForStatement(s,d)->	 simpleAct
	|_ ->simpleAct
	
	(*	
	begin
		 		if (onlyOnStrParamRefs index ls) 
		 		then let eOption=Core.Std.Hashtbl.find dict 
		 							(ToStr.Debug.exp_act (Trans.trans_exp ~types:types (Var(v))))  in
		 						match eOption with
		 						|Some(e') -> Assign(v,e')
								|None -> raise CanNotDoRefine
				end
	match cons with
	|Eqn(Var(var),value)	-> 
		if (onlyOnVar index var )
		then
	|Neg(Eqn(Var(var),value))	->
		matchVarDo var*)

let mkDict 	dict  absIndexs gs=
	let ()=Core.Std.Hashtbl.clear dict in
	let trans atomForm=
		match atomForm with
		|Paramecium.Eqn(Var(var),Var(var1))	-> 
			if (onlyOnVars absIndexs var ) || (not (onlyOnVars absIndexs var1))
			then [(ToStr.Smv.exp_act (Var(var))  , Var(var1))]
			else 
				if  (onlyOnVars absIndexs var1 )|| (not (onlyOnVars absIndexs var))
				then [(ToStr.Debug.exp_act (Var(var1))  ,  Var(var))]
				else []
		|_ ->[] in
	let pairsOfgs=List.concat (List.map ~f:trans gs) in	
	List.fold ~f:(fun () p -> Hashtbl.replace dict ~key:(fst p) ~data:(snd p))
	 pairsOfgs ~init:()

let statementDecompse st=
	match st with
		|Assign(v,e) -> [st]
		|Parallel(s)->s
		|ForStatement(s,d)->[st]
		
let needCmp absIndexs types notOtherExps r=	
	let Rule(name,paramdefs,g, act)=r  in
	(*let  Paramecium.Paramfix(pname,indextype,Intc(index))=paramRef in	*)
	let  statements=statementDecompse act in
	let statements=List.filter ~f:(fun st->not (statementAllOnIndexs absIndexs  st ))  statements in
		match statements with
		| [] -> false
		| _ -> (*true
			let g=Loach.eliminate_false_eq  index notOtherExps g in*)
			if (loachImply g Miracle types)  then false else true
			
let rec  statementNeedRightSub index statement= 
	match statement with
	|Assign(var,value) ->  onExp index value
	|Parallel(statementList) -> 
		List.fold  (List.map ~f:( statementNeedRightSub index) statementList) 
		 ~f:(fun x y -> x && y) ~init:true
	|IfStatement(bcond,statement) ->
		 statementNeedRightSub index statement
	|IfelseStatement(b,s1,s2) ->
	 ( statementNeedRightSub index s1) && ( statementNeedRightSub index s2)
	|ForStatement(s,parmDefs) ->false
		(*regularForStatement(s)*)
		
let statementNeedRightSubIndexs absIndexs  st		=
	List.fold ~f:(fun  y index->statementNeedRightSub index st || y) absIndexs ~init:false	
	
let statementsNeedRightSubIndexs absIndexs  sts		=
	List.fold ~f:(fun  y st->statementNeedRightSubIndexs absIndexs st || y) sts ~init:false				

(*abstract action to a rule;
here r is an strengthened rule
do two things:
1.eleminate useless assignments such as a[index]:=e;
2.replace gv:=a[i] with gv:=gv' if gv'=a[i] or a[i]=gv' occurs in g
3. eliminate all atomic formula a[i]=e or e=a[i]	
4. absIndexes is the set of the index of other nodes*)
let cmpAbstract  absIndexs types r=
	let Rule(name,paramdefs,g, act)=r  in
	(*let ()=print_endline 	(ToMurphi.rule_act r) in
	let  Paramecium.Paramfix(pname,indextype,Intc(index))=paramRef in	*)
	let  statements=statementDecompse act in
	(* the first thing*)
	let statements=List.filter ~f:(fun st->not (statementAllOnIndexs absIndexs  st ))  statements in
	let statementsNeedRighSub=statementsNeedRightSubIndexs absIndexs statements in
	let gs=flat_loach_and_to_list g in 
	let gs0=List.map ~f:(Trans.trans_formula ~types:types) gs in
	let gs1=List.concat (List.map ~f:(Formula.flat_and_to_list) gs0) in		
	(*the snd thing*)
	let refineStatements=
	if (statementsNeedRighSub) then
		match statements with
		|st::statements0 -> 
			let ()=print_endline name in
			let ()=mkDict dict absIndexs gs1 in
			let statements=List.map ~f:(refineAct types  dict  absIndexs) statements in
			statements
		|[]->[]  
	else 
	 
		let ()=Core.Std.Hashtbl.clear dict in
		match statements with
		|st::statements0 -> 
			let ()=print_endline name in 
			let statements=List.map ~f:(refineAct types  dict  absIndexs) statements in
			statements
		|[]->[]   in
		
	(*the 3rd thing*)
	let refinedGs=List.concat (List.map ~f:(refineGuard  absIndexs) gs)	in
	let r=Rule(name,paramdefs,AndList(refinedGs), Parallel(refineStatements)) in
	let generalizedtParas0=Int.Set.to_list (Int.Set.diff (Loach.ParasOf.of_rule r) (Int.Set.of_list absIndexs)) in 
	let generalizedtParas=Paramecium.int_consts generalizedtParas0 in
	let mapTab=Loach.ComputeMap.computeMapTable r (!prulesRef) in
	let ()=print_endline (string_of_int (Core.Std.Hashtbl.length mapTab)) in
	let ()=print_endline (ToMurphi.rule_act r) in 
	let r=Loach.ParaNameReplace.apply_rule r~dict:mapTab in
	let r'=LoachGeneralize.rule_act ~rename:false ~generalizedtParas:generalizedtParas r  in
	let Rule(name,paramdefs,g, s) =r' in
	let name'=name ^(String.concat ~sep:"_" (List.map ~f:(string_of_int) generalizedtParas0 )) in
	Rule(name',paramdefs,g, s)

exception ParaNumErrors (*raise when para numbers >2 *)
exception OtherException	(*raise when index in paraRef is not equal to length(nodes ) +1*)
(*instantiate a pr(parameterized rule) with 2 paras into rules*)
(*nodes is unabstracted nodes like [1;2] or [1;2;3] *)
(*unAbstractedParas---e.g., in the  rule "store src d" in  FLASH, d  is not needed
to be abstracted
constraint if nodes=[1,..,n], index= n+1;
when paranumbers of pr is 2, we need nodes to instantiate pr into rules 
pr[1][3],pr[2][3],pr[3][3];
pr[3][1],pr[3][2],
when paraNumbers of pr is 1, we instantiate pr into pr[3]; 
*)
(*open  Paramecium*)
let instantiatePr2Rules  	paramRef  nodes types ?(unAbstractedParas=[]) pr=
	let  Paramecium.Paramfix(pname,indextype,Intc(index))=paramRef in	
	let  Loach.Rule(name,paramdefs,g, act)=pr in	
	let absParamDefs=Utils.list_subtract paramdefs unAbstractedParas in
	let len=List.length absParamDefs in
	let lenOfNodes=List.length nodes in
	(*if (lenOfNodes+1) <> index 
	then raise OtherException
	else*)
		if len=0 then []	(*revised [pr]*)
		else if len=1
		then
			let [ Paramecium.Paramdef(pn,pt)]=absParamDefs in
			let para= Paramecium.Paramfix(pn,pt,Intc(index)) in
			   [(Loach.apply_rule_without_fold_forStatement  ~p:[para] ~types:types pr, [index])]  
			   
		else if (len >2) then
			raise ParaNumErrors 
		else
			(*do the first para*)
			let Some( Paramecium.Paramdef(pn,pt))=List.hd absParamDefs in
			let actualParas=List.map 
				(*~f:(fun i ->  Paramecium.Paramfix(pn,pt,Intc(i))) (nodes @ [index]) in*)
				~f:(fun i ->  Paramecium.Paramfix(pn,pt,Intc(i))) ( [index - 1;index + 1]) in
			(*eg. actualParas=[3,4] the choices for the first parameter*)
			let (Some( Paramecium.Paramdef(pn',pt')))=List.nth absParamDefs 1 in
			let p'=Paramecium.Paramfix(pn',pt',Intc(index)) in
			(*p' is for  the second parameter*)
			let actualParaLs=List.map
				~f:(fun p-> [p; p'])  actualParas in
			(*e.g., actualParaLs=[[3,3],[3,4]]*)
			
			let rs=List.map ~f:(fun para -> Loach.apply_rule_without_fold_forStatement  
				 ~p:para ~types:types pr) actualParaLs in	
			(*let endR=List.nth rs ((List.length nodes) )in*)
			let Some(endR)=List.nth rs 1 in
			(*let Some(Loach.Rule(name',paramdefs',g', act'))=endR in
			let gs=match g' with
				AndList(gs) -> gs 
				|_ ->[g'] in 
			let gs=List.concat (List.map ~f:(flat_loach_and_to_list) gs) in	
			let g1=Loach.Neg(Eqn(Param(Paramfix( pn',pt',Intc(index))), Param(Paramfix(pn,pt,Intc(index+1))))) in
			let g2=Loach.Neg(Eqn(Param(Paramfix(pn,pt,Intc(index+1))),Param(Paramfix( pn',pt',Intc(index))))) in
			let gs'=List.filter ~f:(fun g -> not ( (g=g1) ||(g=g2))) gs in
			let Some(endR)=endR in
			let endR'=Loach.Rule(name',paramdefs',AndList(gs'), act') in*)
			(*let Some(r1)=(List.nth rs 0) in
			let Some(r2)=(List.nth rs 1) in
			let rs=[r1; r2;endR'] in*)
	     (*  let Some(rs0)=(List.tl (List.rev rs)) in*)
			let Some(r0)=(List.nth rs 0) in
			(*let Some(r0)=(List.nth rs 1) in*)
			let rs=(endR,[index;index+1])::[(r0,[index])] in 

			 
			let Some(Paramecium.Paramdef(pn,pt))=List.nth absParamDefs 1 in
			let actualParas=List.map 
				(*~f:(fun i -> Paramfix(pn,pt,Intc(i))) (nodes ) in*)
				~f:(fun i -> Paramecium.Paramfix(pn,pt,Intc(i))) ([index - 1] ) in
			let (Some(Paramecium.Paramdef(pn',pt')))=List.nth absParamDefs 0 in
			let p'=Paramecium.Paramfix(pn',pt',Intc(index  )) in
			let actualParaLs=List.map
				~f:(fun p-> [ p';p])  actualParas in
			let rs'=List.map ~f:(fun para -> Loach.apply_rule_without_fold_forStatement ~p:para ~types:types pr) actualParaLs in	
			(*let Some(r0')=(List.nth (List.rev rs') 0) in*)
			let Some(r0')=(List.nth rs' 0) in
				(rs@[(r0',[index])])
			 (*List.filter ~f:( fun x -> not (onlyOnRule  index x) )  	(rs@rs')*)
(*return [(cr, abs_i)]---cr the concrete rule, the index to be abstracted*)


(*do cmp method on parameterized rule pr with properties pprops
1. obtain concrete invariants according to  the other(index in paramRef;
2. obtain rule instances according to nodes and the other node
3. decide whether there is a rule to be needed to be strengthened and abstarcted
4. if there are some rules, do strengthening and abstarcting actions *)			
let cmp 	 pprops ~types paramRef  nodes ?(unAbstractedParas=[])  notOtherExps  pr=
	let  Paramecium.Paramfix(pname,indextype,Intc(index))=paramRef in	
	let  Loach.Rule(name,paramdefs,g, act)=pr in	
	let ()=match unAbstractedParas with
		|[]-> ()
		|_ -> print_endline name in
	
	(*let invs=properties2invs pprops ~types:types paramRef in*)
	
						
						
	
	let rs=instantiatePr2Rules  	paramRef  nodes types ~unAbstractedParas:unAbstractedParas  pr in  (*	paramRef  nodes types*)
	let rs=List.filter ~f:(fun (r,abs_is)-> needCmp abs_is types  notOtherExps r  ) rs in
	match rs with
	|[] ->( [],[])
	|_ ->
	let rs'=List.map 
		~f:(fun (r,abs_is) -> 
				let invs=if (List.length abs_is<2) then
							getInsInstsForRuleWithParam1 ()
					else getInsInstsForRuleWithParam2 () in
				(*let k1=print_endline ("length of invs="^(string_of_int (List.length invs))) in
			   let k=List.map ~f:(fun f -> print_endline (ToMurphi.form_act f)) invs in*)
					((cmpStrengthRule invs  ~types:types abs_is (r,[])) ,abs_is)
			) rs in (*cmpStrengthRule invs  ~types paramRef r*)
	let usedInvs=List.dedup (List.concat (List.map 
		~f:(fun x ->match x with 
			|(Some(r,usedInvs),abs_is) -> usedInvs
			|(None ,abs_is)-> []) rs')) in
	let rs'=List.map 
		~f:(fun  x ->match x with 
		 |(Some(r,usedInvs),abs_is) ->(Some(cmpAbstract abs_is types r,usedInvs),abs_is)
		 |(None,abs_is)-> (None, abs_is)) rs' in
	(rs',usedInvs)
	(*let rs'=List.map 
		~f:(fun  x ->match x with 
		 |(Some(r,usedInvs),abs_is) ->(Some(r),abs_is)
		 |(None,abs_is)-> (None, abs_is)) rs' in
	let rs''=List.map 
		~f:(fun x-> match x with 
		|(Some(r),abs_is)->[cmpAbstract abs_is types r]
		|(None,abs_is) -> [])  rs' in 
	(List.concat rs'',usedInvs)*) 


	

(*do cmp actions on a list of rules
unAbstractedReqs is a list of pairs of a rule and unAbstractedParas*) 
let cmpOnPrs 	pprops ~types paramRef  nodes  ?(unAbstractedReqs=[])  notOtherExps  prs=
	let cmpt r=
		let  Loach.Rule(name,paramdefs,g, act)=r in	
		let ls=List.filter ~f:(fun (prName,paras) -> String.equal name prName) unAbstractedReqs in
			match ls with
			|[]->[]
			|_ ->let Some(pair)=List.hd ls in
				snd pair  in
	let resultL=List.map ~f:(fun r -> cmp 	pprops ~types paramRef  nodes ~unAbstractedParas:(cmpt r) notOtherExps r) prs in
	let Some(rsCmpInf)=List.zip prs (List.map ~f:fst resultL) in
	 
	let invs=(*List.dedup (List.concat (List.map ~f:snd resultL)) in*)
	Set.elements (Set.of_list (List.concat (List.map ~f:snd resultL)) ~comparator: NameFormulaCmp.comparator)  in
	(rsCmpInf,invs)

		
	
let initInvs ppros types paramRef=	
 	let ()=invsInsts:=[propInstForRuleWith1Para ppros ~types:types paramRef; 
 		propInstForRuleWith2Para ppros ~types:types paramRef;] in ()
 		
 		
let setPrules prules 		=
 let ()=prulesRef:=prules in
 ()

let print_pair p=
	let (r, absOptions)=p in
	let Rule(rn,pdsr,g,act)=r in
	let ()=print_endline rn in
	let printOptionPair (opt,abs_is)=
		match opt with
		|Some((r,usedInvs))->
			let ()=print_endline (ToMurphi.rule_act r) in
			let tmp=List.map ~f:(fun (n,inv)->print_endline n) usedInvs in
			()  
		|None->() in
	List.map ~f:printOptionPair absOptions

let cmpAbsProtGen pprops ~types paramRef  nodes  ?(unAbstractedReqs=[])  notOtherExps  prs (prot0:Loach.protocol)=
 (* let {name=name0; types=types0; vardefs=vardefs0; init=init0; rules=rules0; properties=properties0} :Loach.protocol= prot0   in*)
	let result=cmpOnPrs 	pprops ~types paramRef  nodes  ~unAbstractedReqs  notOtherExps  prs in
	let props=List.filter 
		~f:(fun p -> let Loach.Prop(pn,pds,pinv)=p in
					List.exists ~f:(fun (pn',inv)->pn'=pn) (snd result))
		(pprops) in

	let get_absRules_of_pair p=
		let (r, absOptions)=p in
		let Loach.Rule(rn,pdsr,g,act)=r in
		let ()=print_endline rn in
		let getOptionPair (opt,abs_is)=
			match opt with
			|Some((r',usedInvs))->[r'] 
			|None->[] in
			List.concat (List.map ~f:getOptionPair absOptions) in

	let rulesAbs=List.concat (List.map ~f:get_absRules_of_pair   (fst result)) in
		
		{name=prot0.name; types=prot0.types; vardefs=prot0.vardefs;
		 init=prot0.init; rules=prot0.rules@rulesAbs;  
		 properties=props}
	



















