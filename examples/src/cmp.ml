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
		let (invName,psubs,inv)=inv  in
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
		|Param(pr)->onlyOnParamRef index pr
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
	|Assign(var,value) ->  onlyOnVar index var (*|| onExp index value*)
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
	type t=string*Paramecium.paramref list*Loach.formula
	let sexp_of_t (str,psub,f) =Loach.sexp_of_formula f
	let t_of_sexp s=Loach.formula_of_sexp s
  let compare (s1,p1,x) (s2, p2,y)= String.compare (ToMurphi.form_act x) (ToMurphi.form_act y) 
    
end)
open Core.Std	
let drawConclusion absIndexs types  oldConclusions invTrip=	
	(*let Paramecium.Paramfix(pname,indextype,Intc(index))=paramRef in*)
	let (invn,prefs,invariant)=invTrip in
	let Imply(ant,cons)=invariant in	
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
let rec cmpStrengthRule invTrips  ~types absIndexs (r, usedInvs)=
	(*let Paramecium.Paramfix(pname,indextype,Intc(index))=paramRef in*)
	let Rule(name,paramdefs,g, act)=r  in	
	
	let ()=print_endline "----------------------------\n" in
	let ()=print_endline name in
	let ()=if (loachImply g Miracle types) then 
							print_endline "-------Miracle occurs--------\n"
							else () in
	let ()=print_endline (ToMurphi.rule_act r) in
	let invsRelated=List.filter ~f:(relate ~rule:r ~types: types) invTrips in	
	let ()=print_endline "-------invS related--------\n" in
	let b=List.map ~f:(fun finv -> let (invn,pref,inv)=finv in print_endline  (ToMurphi.form_act inv)) invsRelated in
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
					let invs'=List.filter ~f:(fun x->not (List.mem invsRelated x)) invTrips in
						Some(newR,usedInvs@invsRelated)
					(*cmpStrengthRule invs' types absIndexs (newR, usedInvs@invsRelated)*)
				
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
		if (List.length params=0) then [(name,[],pinv)]
		else List.map ~f:(fun p-> (name,p,apply_form ~p:p pinv)) (mkActualParasForInv prop) in
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
	let mkActualProps prop=
		let Prop( name, params, pinv)=prop	  in
		if (List.length params=0) then [(name,[],pinv)]
		else List.map ~f:(fun p-> (name,p,apply_form ~p:p pinv)) (mkActualParasForInv prop) in		
	let invs= 
		List.concat (List.map ~f:mkActualProps	pprops	) in
	let  invs=Set.elements (Set.of_list invs ~comparator: NameFormulaCmp.comparator) in 	
		invs


	(*let subst1=	[[Paramecium.Paramfix("i",indextype,Intc(index ));
		Paramecium.Paramfix("j",indextype,Intc(index +1 ));]] in
	let subst2=[[Paramecium.Paramfix("i",indextype,Intc(index ));
		Paramecium.Paramfix("j",indextype,Intc(index +1 ));]; 		
	 [Paramecium.Paramfix("i",indextype,Intc(index ));
		Paramecium.Paramfix("j",indextype,Intc(index - 1 ));]] in	 *)
		(*else if (List.length params=1) then
		List.map ~f:(fun p-> apply_form ~p:p pinv) subst1
		else List.map ~f:(fun p-> apply_form ~p:p pinv) subst2 in *)

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
		 	if not (Int.Set.is_empty (Int.Set.inter (ParasOf.of_statement simpleAct) (Int.Set.of_list absIndexs))) (*(onlyOnStrsParamRefs absIndexs ls) *)
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



module SParaFix = Set.Make(struct type t = Paramecium.paramref 
	let sexp_of_t f =Paramecium.sexp_of_paramref f
	let t_of_sexp s=Paramecium.paramref_of_sexp s
	let compare x y= String.compare 
	(ToMurphi.paramref_act x) (ToMurphi.paramref_act y) end)

module ParaFixiesOf = struct
   open SParaFix 

  (** fixed parameters of var *)
  let of_param p=
  match p with 
  | Paramecium.Paramref(_)-> SParaFix.of_list []
  | Paramecium.Paramfix(n,t,Intc(i)) -> SParaFix.of_list [Paramfix(n,t,Intc(i))]
  
  let of_var v =
    let Paramecium.Arr(ls) = v in
     (SParaFix.union_list (List.map ls 
    ~f:(fun (n, prefs) -> SParaFix.union_list (List.map ~f:of_param prefs))))

  (** Names of exp *)
  let rec of_exp e =
    match e with
    | Const(_)->  of_list []
    | Param(p) -> of_param p
    | Var(v) -> of_var v
    | Ite(f, e1, e2) -> SParaFix.union_list [of_form f; of_exp e1; of_exp e2]
    | UIF(n, el) -> SParaFix.union_list (List.map el ~f:of_exp)
  (** Names of formula *)
  and of_form f =
    match f with
    | Chaos
    | Miracle -> SParaFix.of_list []
    | UIP(n, el) -> SParaFix.union_list (List.map el ~f:of_exp)
    | Eqn(e1, e2) -> SParaFix.union_list [of_exp e1; of_exp e2]
    | Neg(form) -> of_form form
    | AndList(fl)
    | OrList(fl) -> SParaFix.union_list (List.map fl ~f:of_form)
    | Imply(f1, f2) ->SParaFix. union_list [of_form f1; of_form f2]
		| ForallFormula(pds,f') -> of_form f'

  let rec of_statement s =
    match s with
    | Assign(v, e) -> SParaFix.union_list [of_var v; of_exp e]
    | Parallel(slist) -> SParaFix.union_list (List.map slist ~f:of_statement)    
	  | IfStatement(cond,s)-> SParaFix.union_list [of_form cond; of_statement s]
  | IfelseStatement(f,s1,s2) ->SParaFix.union_list [of_form f; of_statement s1;of_statement s2]
  | ForStatement(s,pdfs) -> of_statement s

  let of_rule r = 
    match r with
    | Rule(_, _, f, s) -> SParaFix.elements (SParaFix.union_list [of_form f; of_statement s])
end    
    			

(*abstract action to a rule;
here r is an strengthened rule
do two things:
1.eleminate useless assignments such as a[index]:=e;
2.replace gv:=a[i] with gv:=gv' if gv'=a[i] or a[i]=gv' occurs in g
3. eliminate all atomic formula a[i]=e or e=a[i]	
4. absIndexes is the set of the index of other nodes*)
let cmpAbstract  absIndexs types r=
	let Rule(name,paramdefs,g, act)=r  in
	let parafixes=SParaFix.elements (ParaFixiesOf.of_statement act) in
	let pnsOnAbstractInd=List.filter 
		~f:(fun p ->
			 let Paramecium.Paramfix(n,t,i)=p in
			 let Paramecium.Intc(i)=i in
			 List.mem absIndexs i) parafixes in 
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
	(pnsOnAbstractInd,Rule(name',paramdefs,g, s))

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
			begin
			let Some( Paramecium.Paramdef(pn,pt))=List.hd absParamDefs in
			let actualParas=List.map 
				(*~f:(fun i ->  Paramecium.Paramfix(pn,pt,Intc(i))) (nodes @ [index]) in*)
				~f:(fun i ->  Paramecium.Paramfix(pn,pt,Intc(i))) ( [index - 1;index + 1]) in
			let actParaNames=List.map 
					~f:(fun p->let Paramecium.Paramfix(pn,pt,Intc(i))=p in pn) actualParas in
			
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
			end
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
	
	let rs=instantiatePr2Rules  	paramRef  nodes types ~unAbstractedParas:unAbstractedParas  pr in  (*	paramRef  nodes types*)
	(*let tmp=if (name="n_Store") 
					then begin 
					let ()=print_endline  "-------start debug for rule:" in
					let ()=print_endline (ToMurphi.rule_act pr) in
					let ()=print_endline  "------------------" in
					let tmp1=List.map rs ~f:(fun r -> print_endline (ToMurphi.rule_act (fst r))) in
					let str=read_line () in
					()
					end
					else () in*)
	let rs1=List.filter ~f:(fun (r,abs_is)-> not (needCmp abs_is types  notOtherExps r ) ) rs in
	let rs1'=List.map 		~f:(fun  (r,abs_is) ->(None, abs_is)) rs1 in 
  (*rs1' is those which are not need to be cmped*)
	let rs=List.filter ~f:(fun (r,abs_is)-> needCmp abs_is types  notOtherExps r  ) rs in
	match rs with
	|[] ->( rs1',[])
	|_ ->
	let resultCmps'=List.map 
		~f:(fun (r,abs_is) -> 
			 
				let invs=if (List.length abs_is<2) then
							getInsInstsForRuleWithParam1 ()
					else getInsInstsForRuleWithParam2 () in

				(*let k1=print_endline ("length of invs="^(string_of_int (List.length invs))) in
			   let k=List.map ~f:(fun f -> print_endline (ToMurphi.form_act f)) invs in*)
					((cmpStrengthRule invs  ~types:types abs_is (r,[])) ,abs_is)
			) rs in
 (*cmpStrengthRule invs  ~types paramRef r*)

	let usedInvs=List.dedup (List.concat (
		List.map resultCmps'
		~f:(fun x ->match x with 
			|(Some(r,usedInvs),abs_is) -> usedInvs
			|(None ,abs_is)-> []) 

			)) in	
	
	let rs'=List.map 
		~f:(fun  x ->match x with 
		 |(Some(r,usedInvs),abs_is) ->(Some(cmpAbstract abs_is types r,usedInvs),abs_is)
		 |(None,abs_is)-> (None, abs_is)) resultCmps' in

	(rs'@rs1',usedInvs)
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
		let ls=List.filter ~f:(fun (prName,paras) -> name=prName) unAbstractedReqs in
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
		|Some(((absParams,r),usedInvs))->
			let ()=print_endline (ToMurphi.rule_act r) in
			let tmp=List.map ~f:(fun (n,inv)->print_endline n) usedInvs in
			()  
		|None->() in
	List.map ~f:printOptionPair absOptions

let pair2AbsLemmaCases ~types pprops p=
	let (r, absOptions)=p in
	let Rule(rn,pdsr,g,act)=r in
	let parafix2paradef p=
		let Paramecium.Paramfix(pn,t,i)=p in
		Paramecium.Paramdef(pn,t) in
	let dealOptionPair (opt,abs_is)=
		match opt with
		|Some(((absParams,absR),usedInvs))->
			let props=List.filter 
				~f:(fun p -> let Loach.Prop(pn,pds,pinv)=p in
					List.exists ~f:(fun (pn',prefs,inv)->pn'=pn) (usedInvs))
				(pprops)  in
			(*GenCmpProof.CaseAbs(List.map ~f:parafix2paradef absParams,  r, absR,props,[])*)
			GenCmpProof.CaseAbs(List.map ~f:parafix2paradef absParams,  r, absR,usedInvs,[])
		|None->(let ()=print_endline "genSkip" in GenCmpProof.CaseSkip( pdsr, r)) in
	let cases=List.map ~f:dealOptionPair absOptions in
	(r,cases@[CaseId(r)])

let isabelle2AbsInvs cinvs=
	let invAct cinv =
		let (InvFinder.ConcreteProp(Prop(name, pds, pinv), _)) =cinv in
		match pds with
		|[]->[name ]
		|_->	if List.length pds= 1 
			then List.map ~f:(fun n->String.concat ~sep:" " [name;n]) ["0";"1"]
			else List.map ~f:(fun p->String.concat ~sep:" " ([name]@p)) [["0";"1"];["1";"0"]] in
	
	let inv_insts_str = String.concat ~sep:" ,\n" (
    List.map   ~f:(fun str -> sprintf "%s" str  ) (List.concat (List.map ~f:invAct cinvs))
  ) in
  sprintf " \n\nsubsection{*Definitions of  the Set of Abs Invariant Formula Instances *}\ndefinition invariantsAbs  ::\"  formula list\" where [simp]:
\"invariantsAbs   \\<equiv> [\n%s\n]\"\n\n"  inv_insts_str



module SVar= Set.Make(struct type t = Paramecium.var 
	let sexp_of_t v =Paramecium.sexp_of_var v
	let t_of_sexp s=Paramecium.var_of_sexp s
	let compare x y= String.compare 
	(ToMurphi.var_act x) (ToMurphi.var_act y) end)


module VarsOf = struct
   open SVar

  (** fixed parameters of var *)
  
  
  let of_var v =
    of_list [v] 

  (** Names of exp *)
  let rec of_exp e =
    match e with
    |  Paramecium.Const(_)->  of_list []
    |  Paramecium.Param(p) ->of_list []
    |  Paramecium.Var(v) -> of_var v
    |  Paramecium.Ite(f, e1, e2) -> SVar.union_list [of_form f; of_exp e1; of_exp e2]
    |  Paramecium.UIF(n, el) -> SVar.union_list (List.map el ~f:of_exp)
  (** Names of formula *)
  and of_form f =
    match f with
    | Paramecium.Chaos
    | Paramecium.Miracle -> SVar.of_list []
    | Paramecium.UIP(n, el) -> SVar.union_list (List.map el ~f:of_exp)
    | Paramecium.Eqn(e1, e2) -> SVar.union_list [of_exp e1; of_exp e2]
    | Paramecium.Neg(form) -> of_form form
    | Paramecium.AndList(fl)
    | Paramecium.OrList(fl) -> SVar.union_list (List.map fl ~f:of_form)
    | Paramecium.Imply(f1, f2) ->SVar. union_list [of_form f1; of_form f2] 

  let rec of_statement s =
    match s with
    | Paramecium.Assign(v, e) -> SVar.union_list [of_var v; of_exp e]
    | Paramecium.Parallel(slist) -> SVar.union_list (List.map slist ~f:of_statement)   

  let of_rule r =  
    match r with
    | Paramecium.Rule(rn, _, f, s) -> 
			let result=(SVar.union_list [of_form f; of_statement s])  in
			let found=List.exists (SVar.elements result) ~f:(fun x->(ToMurphi.var_act x)="Cache[i].Data")  in
			let tmp=	if found 
								then print_endline ("find:"^rn^":") (*ToMurphi.rule_act r*)
								else () in
			result
	 
		

	let of_prot (prot:Paramecium.protocol)=
		let makeRuleInst pr=
			let Paramecium.Rule(rn, pds, guard, statement) = pr in			
   		let partition_pds=partition pds ~f:(fun (Paramdef(_,tname))-> tname) in
   		let prefss=Paramecium.cart_product_with_name_partition partition_pds prot.types in
	 		let rs=List.map ~f:(fun sub->Paramecium.apply_rule pr sub) prefss in 
			rs  in
		let rInsts=List.concat (List.map ~f: makeRuleInst prot.rules) in
		
		SVar.elements (SVar.union_list (List.map ~f:of_rule rInsts))
end

(*
axiomatization  where axiomOnf2 [simp,intro]:
   "s \<in> reachableSet (set (allInitSpecs N )) (rules N) \<Longrightarrow>  1 \\<le> N \<Longrightarrow>i\<noteq>j \<Longrightarrow> 
  i \\<le> N \<Longrightarrow>j \\<le> N \<Longrightarrow> formEval (f 0 1) s \<Longrightarrow> formEval (f i j) s\"
axiomatization  where axiomOnf1 [simp,intro]:
   \"s \<in> reachableSet (set (allInitSpecs N )) (rules N) \<Longrightarrow> i\\<le>N \<Longrightarrow>formEval (f 0 ) s \<Longrightarrow> formEval (f i) s"
*)
let prop2ConcInv types property =
  let Paramecium.Prop(_, pds, f) = property in 
    if List.length pds > 0 then
      let ps = Paramecium.cart_product_with_paramfix pds (types) in
      List.map ps ~f:(fun p ->   (Paramecium.neg (Paramecium.apply_form f ~p)))
    else begin
      [  (Paramecium.neg f)]
    end


let outAbsProtWithCmpLemmas ~types absProt prot cases varLsInVF' others=
	let tmp=(Isabelle.types_ref := absProt.types) in
	let typeStr=String.concat ~sep:"\n" (List.filter_map   ~f:Isabelle.type_act absProt.types) in
	let ncStr="definition  NC::\"nat \" where [simp]: \"NC==1\"\n\n " in
	let protInParam=Loach.Trans.act ~loach:prot in
	(*let tmp=print_endline (Loach.Trans.)*)
	(*let vfStr=sprintf "definition VF::\"varType set\" where [simp]: 
\"VF \\<equiv>{%s}\"\n" 
		(String.concat ~sep:"," (List.map ~f:Isabelle.var_act' (VarsOf.of_prot protInParam))) in*)
	let ruleStr=  Isabelle.rules_actCmp absProt.rules in
	 let concProps=(List.map ~f:(fun p->InvFinder.ConcreteProp(Trans.trans_prop ~types p,[])) absProt.properties) in
	let concInvs=List.concat (List.map 
				~f:(fun p->let p =Trans.trans_prop ~types p in 
							prop2ConcInv types p) 
			absProt.properties) in
	(*let allVars=List.concat (List.map ~f:(fun x ->SVar.elements (VarsOf.of_form x))	concInvs) in *)
	let allVars=VarsOf.of_prot protInParam in			
	let allVarsInVF=SVar.elements (SVar.diff (SVar.of_list allVars) (SVar.of_list varLsInVF')) in							
	let vfStr=sprintf "\ndefinition VF::\"varType set\" where [simp]: 
\"VF \\<equiv>{%s}\"\n\n" 
		(String.concat ~sep:"," (List.map ~f:Isabelle.var_act' allVarsInVF )) in  (*VarsOf.of_prot protInParam*)
	let vfStr'=sprintf "\ndefinition VF'::\"varType set\" where [simp]: 
\"VF' \\<equiv>{%s}\"\n\n" 
		(String.concat ~sep:"," (List.map ~f:Isabelle.var_act' varLsInVF' )) in 
	let invStr=Isabelle.invs_act_without_neg concProps 		 in
	let absInvStr=isabelle2AbsInvs concProps in
	let axiomStr="\n\naxiomatization  where axiomOnf2 [simp,intro]:
   \"s \<in> reachableSet (set (allInitSpecs N )) (rules N)   \<Longrightarrow>i\<noteq>j \<Longrightarrow> 
   formEval (f 0 1) s \<Longrightarrow> formEval (f i j) s\"
axiomatization  where axiomOnf1 [simp,intro]:
   \"s \<in> reachableSet (set (allInitSpecs N )) (rules N)  \<Longrightarrow>formEval (f 0 ) s \<Longrightarrow> formEval (f i) s\"\n"
		in
	let thmStr="\nlemma usThm1:
  assumes a1:\"f \\<in> (set invariantsAbs)\" and a4:\"\\<forall>f.  f \\<in>(set invariantsAbs) \\<longrightarrow>  formEval f s\"
  shows \"formEval f  s\"
  using a4 local.a1 by blast \n" in
	let initsStr=Isabelle.inits_act absProt.init in
	let tmp=GenCmpProof.others:=others in
	let caseStr=GenCmpProof.lemmaGenerates cases in
	let filename =   absProt.name^"_abs.thy"   in 
	Unix.mkdir_p absProt.name;
	Isabelle.file_pub absProt.name typeStr (ncStr^vfStr^vfStr'^ruleStr) (invStr^absInvStr^initsStr^axiomStr^thmStr) (caseStr) ();
	Isabelle.file_root' absProt.name;
	Isabelle.file_sh' absProt.name

let cmpAbsProtGen pprops ~types paramRef  nodes  ?(unAbstractedReqs=[])  notOtherExps  prs (prot0:Loach.protocol) varLsInVF'=

	let result=cmpOnPrs 	pprops ~types paramRef  nodes  ~unAbstractedReqs  notOtherExps  prs in

	let props=List.filter 
		~f:(fun p -> let Loach.Prop(pn,pds,pinv)=p in
					List.exists ~f:(fun (pn',pfs,inv)->pn'=pn) (snd result))
		(pprops) in
	let propsRev=List.map props
		~f:(fun p->let Loach.Prop(pn,pds,pinv)=p in
					let prs=List.map ~f:(fun param-> let Paramecium.Paramdef(n,t)=param in Paramecium.Paramref(n)) pds in
					let getSome (Some(a))=a in
					if (List.length pds=2) then
						let paramConstr= 	(Loach.neg (Loach.eqn (Loach.Param(getSome(List.nth prs 0))) (Loach.Param(getSome(List.nth prs 1)))))  in
							Loach.Prop(pn,pds,imply paramConstr pinv)	
					else Loach.Prop(pn,pds,pinv)) in
	let get_absRules_of_pair p=
		let (r, absOptions)=p in
		let Loach.Rule(rn,pdsr,g,act)=r in
		let ()=print_endline rn in
		let getOptionPair (opt,abs_is)=
			match opt with
			|Some((r',usedInvs))->[r'] 
			|None->[] in
			List.concat (List.map ~f:getOptionPair absOptions) in
	let cases=List.map ~f:(pair2AbsLemmaCases ~types pprops) (fst result) in
	let rulesAbs=List.concat (List.map ~f:get_absRules_of_pair   (fst result)) in
	let absProt=	
		{name=prot0.name; types=prot0.types; vardefs=prot0.vardefs;
		 init=prot0.init; rules=prot0.rules@(List.map ~f:snd rulesAbs);  
		 properties=props}  in
	let ()=Isabelle.absRules:=(List.map ~f:(fun x-> let Rule(rn,pds,g,act)=snd x in rn) rulesAbs) in
	let Paramecium.Paramfix(n,t,c)=paramRef in
	let Paramecium.Intc(ic)=c in
	let others=[paramRef;  Paramecium.Paramfix(n,t,Paramecium.Intc(ic+1))] in
	let ()=outAbsProtWithCmpLemmas ~types absProt prot0 cases varLsInVF' others in
	absProt

let make fileName=	
	let template=sprintf "
INCLUDEPATH = /home/lyj238/Downloads/cmurphi5.4.9/include
SRCPATH = /home/lyj238/Downloads/cmurphi5.4.9/src/

CXX = g++

CFLAGS = 

# optimization
OFLAGS = -ggdb
#OFLAGS = -O2

#Murphi options
MURPHIOPTS = -b -c

%s: %s.cpp
	${CXX} ${CFLAGS} ${OFLAGS} -o %s %s.cpp -I${INCLUDEPATH} -lm


%s.cpp: %s.m
	${SRCPATH}mu ${MURPHIOPTS} %s.m" fileName  fileName
fileName	 fileName fileName fileName fileName  in
	let ()=Out_channel.write_all ("makefile")  template in  ()

let cmpGenChk pprops ~types paramRef  nodes  ?(unAbstractedReqs=[])  notOtherExps  prs (prot0:Loach.protocol) scalars varLsInVF'=
	let absProt=cmpAbsProtGen pprops ~types paramRef  nodes  ~unAbstractedReqs notOtherExps  prs (prot0:Loach.protocol) varLsInVF' in
	let tmp=ToMurphi.setScalarTypes scalars in
	let ()= make (absProt.name^"_abs") in
	let filename =   absProt.name^"_abs.m"   in 
	let ()=Out_channel.write_all (filename)  (ToMurphi.protocol_act absProt) in
  let _mu_context = Murphi.set_context absProt.name (ToMurphi.protocol_act absProt) in
	let b=Murphi.is_inv (ToStr.Smv.form_act ~lower:false ( Paramecium.chaos)) in
	if b then print_endline "ok" else print_endline "no"



(*File "src/cmp.ml", line 881, characters 24-56:
Error: This expression has type
         rule * ((rule * ('a * (string * 'b) list)) option * 'c) list ->
         rule * GenCmpProof.lemmaCase list
       but an expression was expected of type
         rule * ((rule * (string * formula) list) option * int list) list ->
         'd
       Type 'a * (string * 'b) list is not compatible with type
         (string * formula) list 
*)

	
	



















