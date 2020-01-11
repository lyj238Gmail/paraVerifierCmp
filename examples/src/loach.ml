(** Language for cache coherence protocols in support of
    parameterization and local variables
*)

open Utils
open Core.Std

open Paramecium
open ToStr

(** Unexhausted instantiation
    This exception should never be raised. Once raised, There should be a bug in this tool.
*)
exception Unexhausted_inst

(** Global variable *)
let global name = arr [(name, [])]

(** Record definition *)
let record_def name paramdefs vardefs =
  List.map vardefs ~f:(fun vardef ->
    let Arrdef(ls, t) = vardef in
    arrdef ((name, paramdefs)::ls) t
  )

(** Record *)
let record vars =
  arr (List.concat (List.map vars ~f:(fun (Arr(ls)) -> ls)))


type exp =
  | Const of const
  | Var of var
  | Param of paramref
  | Ite of formula * exp * exp
  | UIF of string * exp list
and formula =
  | Chaos
  | Miracle
  | UIP of string * exp list
  | Eqn of exp * exp
  | Neg of formula
  | AndList of formula list
  | OrList of formula list
  | Imply of formula * formula
  | ForallFormula of paramdef list * formula
  | ExistFormula of paramdef list * formula
with sexp


  
let const c = Const c
let var v = Var v
let param paramref = Param(paramref)
let ite f e1 e2 = Ite(f, e1, e2)
let uif  n el = UIF(n, el)

let chaos = Chaos
let miracle = Miracle
let uip n el = UIP(n, el)
let eqn e1 e2 = Eqn(e1, e2)
let neg f = Neg f
let andList fs = AndList fs
let orList fs = OrList fs
let imply f1 f2 = Imply(f1, f2)
let forallFormula paramdefs form = ForallFormula(paramdefs, form)
let existFormula paramdefs form = ExistFormula(paramdefs, form)

(** Assignment statements *)
type statement =
  | Assign of var * exp
  | Parallel of statement list
  | IfStatement of formula * statement
  | IfelseStatement of formula * statement * statement
  | ForStatement of statement * paramdef list
with sexp

let assign v e = Assign(v, e)
let parallel statements = Parallel statements
let ifStatement form statement = IfStatement(form, statement)
let ifelseStatement form s1 s2 = IfelseStatement(form, s1, s2)
let forStatement s paramdefs = ForStatement(s, paramdefs)



let write vardef exp_i exp_v types =
  let Arrdef([(n, [Paramdef(pn, tn)])], _) = vardef in
  forStatement (
    ifStatement (
      eqn (param (paramref pn)) exp_i
    ) (
      assign ((arr [(n, [paramref pn])])) (exp_v)
    )
  ) [paramdef pn tn]


let read vardef exp_i types =
  let Arrdef([(n, [Paramdef(pn, tn)])], _) = vardef in
  let indice = name2type ~tname:tn ~types in
  let values = List.map indice ~f:(fun c -> var (arr [(n, [paramfix pn tn c])])) in
  List.reduce_exn values ~f:(fun res x ->
    let Var(Arr([(_, [Paramfix(_, _, c)])])) = x in
    ite (eqn exp_i (const c)) x (res)
  )

	
let flat_loach_and_to_list form =
   
  let rec wrapper form =
    match form with
    | Chaos
    | Miracle
    | Eqn(_)
    | UIP(_)
    | Neg(UIP(_))
    | Neg(Eqn(_)) -> [form]
    | AndList([]) -> [chaos]
    | AndList([f]) -> [f]
    | AndList(fl) -> List.concat (List.map fl ~f:wrapper)
    | OrList([]) -> [miracle]
    | OrList([f]) -> [f]
    | OrList(fl) -> [form]
    | _ ->[form]
  in
  wrapper form	


(** Represents rules which consists of guard and assignments
    + Rule: name, parameters, guard, assignments
*)
type rule = 
  | Rule of string * paramdef list * formula * statement
with sexp

let rule name paramdef f s = Rule(name, paramdef, f, s)

type prop =
  | Prop of string * paramdef list * formula
with sexp

let prop name paramdef f = Prop(name, paramdef, f)

(** Represents the whole protocol *)
type protocol = {
  name: string;
  types: typedef list;
  vardefs: vardef list;
  init: statement;
  rules: rule list;
  properties: prop list;
}
with sexp

let rec apply_exp e ~p =
  match e with
  | Const(_) -> e
  | Var(x) -> var (apply_array x ~p)
  | Param(pr) -> param (apply_paramref pr ~p)
  | Ite(f, e1, e2) -> ite (apply_form f ~p) (apply_exp e1 ~p) (apply_exp e2 ~p)
  | UIF(n, el) -> uif n (List.map el ~f:(apply_exp ~p))
and apply_form f ~p =
  match f with
  | Chaos
  | Miracle -> f
  | UIP(n, el) -> uip n (List.map el ~f:(apply_exp ~p))
  | Eqn(e1, e2) -> eqn (apply_exp e1 ~p) (apply_exp e2 ~p)
  | Neg(form) -> neg (apply_form form ~p)
  | AndList(fl) -> andList (List.map fl ~f:(apply_form ~p))
  | OrList(fl) -> orList (List.map fl ~f:(apply_form ~p))
  | Imply(f1, f2) -> imply (apply_form f1 ~p) (apply_form f2 ~p)
  | ForallFormula(paramdefs, form) -> forallFormula paramdefs (apply_form form ~p)
  | ExistFormula(paramdefs, form) -> existFormula paramdefs (apply_form form ~p)

let rec apply_statement statement ~p ~types =
  match statement with
  | Assign(v, e) -> assign (apply_array v ~p) (apply_exp e ~p)
  | Parallel(sl) -> parallel (List.map sl ~f:(apply_statement ~p ~types))
  | IfStatement(f, s) -> ifStatement (apply_form f ~p) (apply_statement s ~p ~types)
  | IfelseStatement(f, s1, s2) ->
    ifelseStatement (apply_form f ~p) (apply_statement s1 ~p ~types) (apply_statement s2 ~p ~types)
  | ForStatement(s, pd) ->
    let s' = apply_statement s ~p ~types in
    let pfs = cart_product_with_paramfix pd types in
    parallel (List.map pfs ~f:(fun p -> apply_statement s' ~p ~types))

let rec eliminate_for statement ~types =
  match statement with
  | Assign(_) -> statement
  | Parallel(sl) -> parallel (List.map sl ~f:(eliminate_for ~types))
  | IfStatement(f, s) -> ifStatement f (eliminate_for s ~types)
  | IfelseStatement(f, s1, s2) ->
    ifelseStatement f (eliminate_for s1 ~types) (eliminate_for s2 ~types)
  | ForStatement(s, pd) ->
    let pfs = cart_product_with_paramfix pd types in
    parallel (List.map pfs ~f:(fun p -> apply_statement s ~p ~types))

let apply_rule r ~p ~types =
  let Rule(n, paramdefs, f, s) = r in
  let name =
    if p = [] then n
    else begin
      let const_act c =
        match c with
        | Intc(i) -> Int.to_string i
        | Strc(s) -> String.lowercase s
        | Boolc(b) -> String.uppercase (Bool.to_string b)
      in
      let paramref_act pr =
        match pr with
        | Paramfix(_, _, c) -> sprintf "[%s]" (const_act c)
        | Paramref(_) -> raise Unexhausted_inst
      in
      sprintf "%s%s" n (String.concat (List.map p ~f:paramref_act))
    end
  in
  let remainedPdefs=List.filter 
  	~f:( fun x -> let Paramdef(n,t)=x in 
  								let result=find_paramfix p n in
  								match result with
  									|Some(_)->false
  									|_ ->true) 
  		paramdefs			in				
  									
  rule name remainedPdefs (apply_form f ~p) (apply_statement s ~p ~types)
  (*duan's old version: rule name [] (apply_form f ~p) (apply_statement s ~p ~types)*)
  


let rec eliminate_false_eq  other notOtherExps f=
  match f with
  | Chaos -> Chaos
  | Miracle -> Miracle
  | UIP(n, el) -> uip n el
  | Eqn(e1, e2) -> 
	begin
  	match e1 with
  		| Param(p1) ->
		  begin
  			match e2 with
  			| Param(p2) ->
  					if (p1=p2)
  					then Chaos
  					else 
  					begin
					       
						match p1 with 
						|Paramfix(p1Name,p1Type,Intc(i1)) ->
	                   begin
							match p2 with
							|Paramfix(p2Name,p2Type,Intc(i2)) ->
  							if (i1=other) || (i2=other)
  							then Miracle
  							else f
							|_ ->
							 if (i1=other) then Miracle
							 else f
						  end
           |_  ->  
						 begin
							match p2 with
							|Paramfix(p2Name,p2Type,Intc(i2)) ->
  							if  (i2=other)
  							then Miracle
  							else f
							|_ ->
							 if (p1=p2) then Chaos
							 else f
						  end
  						end
  			|_ ->
				begin
					    
					match p1 with 
						|Paramfix(p1Name,p1Type,Intc(i1)) ->
	           begin
							
  							if (i1=other) &&(List.mem notOtherExps e2 )
  							then Miracle
  							else f
							
						  end
             |_ ->  f
					
					
  				end	
        end
  		|_-> 
  		if (e1=e2)
  			then Chaos
  			else  
			begin
			match e2 with
  			| Param(p2) ->
				begin
  					match p2 with
							|Paramfix(p2Name,p2Type,Intc(i2)) ->
  							if  (i2=other)&&(List.mem  notOtherExps e1)
  							then Miracle
  							else f
							|_ -> f
				end
           |_ -> f
			end
  					
    end	
  	
  | Neg(form) -> 
	begin
	let form=eliminate_false_eq other notOtherExps form in
  	match form with
  		|Chaos ->Miracle
  		|Miracle -> Chaos
  		|_->Neg(form)
  	end	
  | AndList(fl) -> 
  	 let mid=List.map fl ~f:(eliminate_false_eq other notOtherExps ) in
  	 let flaseLS=List.filter ~f:(fun g -> g=Miracle) mid in
  	 let notTrueLs=List.filter ~f:(fun g -> g<>Chaos ) mid in
  	  if (flaseLS <>[] )
  	  then Miracle
  	  else AndList(notTrueLs)
  	  
  | OrList(fl) -> orList (List.map fl ~f:(eliminate_false_eq other notOtherExps ))
  | Imply(f1, f2) -> imply (eliminate_false_eq other notOtherExps f1 ) (eliminate_false_eq other  notOtherExps f2 )
  | ForallFormula(paramdefs, form) -> forallFormula paramdefs (eliminate_false_eq other notOtherExps form )
  | ExistFormula(paramdefs, form) -> existFormula paramdefs (eliminate_false_eq other notOtherExps form )

let rec simplify_statement_by_elim_false_eq other notOtherExps statement0 =  
 match statement0 with 
  | Assign(v, e) ->statement0 
  | Parallel(sl) -> parallel (List.map sl ~f:(simplify_statement_by_elim_false_eq other notOtherExps ))
  | IfStatement(f, s) -> ifStatement (eliminate_false_eq other notOtherExps f ) (simplify_statement_by_elim_false_eq other notOtherExps s)
  | IfelseStatement(f, s1, s2) ->
    ifelseStatement (eliminate_false_eq other notOtherExps f ) (simplify_statement_by_elim_false_eq other notOtherExps s1  ) (simplify_statement_by_elim_false_eq other notOtherExps s2  )
  | ForStatement(s, pd) ->
    let s' = simplify_statement_by_elim_false_eq other notOtherExps s in
     forStatement s' pd


let simplify_rule_by_elim_false_eq other notOtherExps r =
  let Rule(n, paramdefs, f, s) = r in
  let s'=simplify_statement_by_elim_false_eq other notOtherExps s in
  let f'=eliminate_false_eq other notOtherExps (AndList(flat_loach_and_to_list f)) in
   Rule(n, paramdefs, f', s')
   
   


    
let rec apply_statement_without_fold_forStatement statement ~p ~types =
  match statement with
  | Assign(v, e) -> assign (apply_array v ~p) (apply_exp e ~p)
  | Parallel(sl) -> parallel (List.map sl ~f:(apply_statement_without_fold_forStatement ~p ~types))
  | IfStatement(f, s) -> ifStatement (apply_form f ~p) (apply_statement_without_fold_forStatement s ~p ~types)
  | IfelseStatement(f, s1, s2) ->
    ifelseStatement (apply_form f ~p) (apply_statement_without_fold_forStatement s1 ~p ~types) (apply_statement_without_fold_forStatement s2 ~p ~types)
  | ForStatement(s, pd) ->
    let s' = apply_statement_without_fold_forStatement s ~p ~types in
     forStatement s' pd
    (*let pfs = cart_product_with_paramfix pd types in
    parallel (List.map pfs ~f:(fun p -> apply_statement_without_fold_forStatement s' ~p ~types)) *)
    
let apply_rule_without_fold_forStatement r ~p ~types =
  let Rule(n, paramdefs, f, s) = r in
  let name =
    if p = [] then n
    else begin
      let const_act c =
        match c with
        | Intc(i) -> Int.to_string i
        | Strc(s) -> String.lowercase s
        | Boolc(b) -> String.uppercase (Bool.to_string b)
      in
      let paramref_act pr =
        match pr with
        | Paramfix(prn, _, c) -> sprintf "_%s_%s" prn (const_act c)
        | Paramref(_) -> raise Unexhausted_inst
      in
      sprintf "%s%s" n (String.concat (List.map p ~f:paramref_act))
    end
  in
  let remainedPdefs=List.filter 
  	~f:( fun x -> let Paramdef(n,t)=x in 
  								let result=find_paramfix p n in
  								match result with
  									|Some(_)->false
  									|_ ->true) 
  		paramdefs			in				
  									
  rule name remainedPdefs (apply_form f ~p) 
  (apply_statement_without_fold_forStatement s ~p ~types)    
  

let apply_prop property ~p =
  let Prop(name, paramdefs, f) = property in
  prop name [] (apply_form f ~p)

let rule_to_insts r ~types =
  let Rule(n, pd, f, s) = r in
  let ps = cart_product_with_paramfix pd types in
  if pd = [] then
    [rule n pd f (eliminate_for s ~types)]
  else begin
    List.map ps ~f:(fun p -> apply_rule r ~p ~types)
  end


let analyze_if statement guard ~types =
  let nofor = eliminate_for statement ~types in
  let rec wrapper statement ~m ~g =
    match statement with
    | Assign(v, e) ->
      let key = ToStr.Debug.var_act v in 
      let data = (
        match String.Map.find m key with
        | None -> (v, [(g, e)])
        | Some(v, exps) -> (v, (g, e)::exps)
      ) in
      String.Map.add m ~key ~data
    | Parallel(sl) ->
      let rec wrap_parallel sl m =
        match sl with
        | [] -> m
        | s::sl' -> wrap_parallel sl' (wrapper s ~m ~g)
      in
      wrap_parallel sl m
    | IfStatement(f, s) -> wrapper s ~m ~g:(andList [f; g])
    | IfelseStatement(f, s1, s2) ->
      let if_part = wrapper s1 ~m ~g:(andList [f; g]) in
      wrapper s2 ~m:if_part ~g:(andList [neg f; g])
    | ForStatement(_) -> raise Empty_exception
  in
  let m = wrapper nofor ~m:String.Map.empty ~g:guard in
  let keys = String.Map.keys m in
  List.map keys ~f:(fun k -> String.Map.find_exn m k)










let rec get_var_of_balanced s =
  match s with
  | Assign(v, _)
  | ForStatement(Assign(v, _), _) -> v
  | IfelseStatement(_, s, _)
  | ForStatement(IfelseStatement(_, s, _), _) -> get_var_of_balanced s
  | _ -> raise Empty_exception

let get_vname_map_of_balanced sl =
  let rec wrapper sl m =
    match sl with
    | [] -> m
    | s::sl' ->
      let v = get_var_of_balanced s in
      let key = ToStr.Debug.var_act v in
      wrapper sl' (String.Map.add m ~key ~data:s)
  in
  wrapper sl String.Map.empty

let merge_ifelse f s1 s2 =
  match (s1, s2) with
  | (ForStatement(s, pd), ForStatement(s', _)) ->
    (* TODO need to check pds? *)
    forStatement (ifelseStatement f s s') pd
  | (_, ForStatement(s, pd)) -> forStatement (ifelseStatement f s1 s) pd
  | (ForStatement(s, pd), _) -> forStatement (ifelseStatement f s s2) pd
  | (Assign(_), Assign(_))
  | (Assign(_), IfelseStatement(_))
  | (IfelseStatement(_), Assign(_))
  | (IfelseStatement(_), IfelseStatement(_)) -> ifelseStatement f s1 s2
  | _ -> raise Empty_exception

let rec balance_ifstatement statement =
  match statement with
  | Assign(_) -> [statement]
  | Parallel(sl) -> List.concat (List.map sl ~f:balance_ifstatement)
  | IfStatement(f, s) -> balance_ifstatement (ifelseStatement f s (parallel []))
  | IfelseStatement(f, s1, s2) ->
    let bs1 = balance_ifstatement s1 in
    let bs2 = balance_ifstatement s2 in
    let _names1 = get_vname_map_of_balanced bs1 in
    let names2 = get_vname_map_of_balanced bs2 in
    let rec wrapper pair res =
      match pair with
      | ([], []) -> res
      | ([], b2::bs2') ->
        let v = get_var_of_balanced b2 in
        let next_s = assign v (var v) in
        wrapper ([], bs2') (merge_ifelse f next_s b2::res)
      | (b1::bs1', bs2) ->
        let v = get_var_of_balanced b1 in
        let key = ToStr.Debug.var_act v in
        let next_s =
          match String.Map.find names2 key with
          | None -> assign v (var v)
          | Some(s) -> s
        in
        let bs2' =
          match String.Map.find names2 key with
          | None -> bs2
          | _ -> rm_from_list bs2 ~f:(fun s -> get_var_of_balanced s = v)
        in
        wrapper (bs1', bs2') (merge_ifelse f b1 next_s::res)
    in
    wrapper (bs1, bs2) []
  | ForStatement(s, pd) ->
    let bs = balance_ifstatement s in
    List.map bs ~f:(fun s' -> forStatement s' pd)

let eliminate_ifelse statement =
  let rec wrapper statement =
    match statement with
    | Assign(_) -> statement
    | IfelseStatement(f, s1, s2) ->
      let Assign(v, e1) = wrapper s1 in
      let Assign(_, e2) = wrapper s2 in
      assign v (ite f e1 e2)
    | ForStatement(s, pd) -> forStatement (wrapper s) pd
    | _ -> raise Empty_exception
  in
  let balanced = balance_ifstatement statement in
  parallel (List.map balanced ~f:wrapper)









let rec eliminate_imply_neg form =
  match form with
  | Chaos
  | Miracle
  | UIP(_)
  | Eqn(_) -> form
  | Neg(Chaos) -> miracle
  | Neg(Miracle) -> chaos
  | Neg(UIP(_))
  | Neg(Eqn(_)) -> form
  | Neg(Neg(f)) -> eliminate_imply_neg f
  | Neg(AndList(fl)) -> eliminate_imply_neg (orList (List.map fl ~f:neg))
  | Neg(OrList(fl)) -> eliminate_imply_neg (andList (List.map fl ~f:neg))
  | Neg(Imply(f1, f2)) -> eliminate_imply_neg (andList [f1; neg f2])
  | Neg(ForallFormula(pd, f)) -> existFormula pd (eliminate_imply_neg (neg f))
  | Neg(ExistFormula(pd, f)) -> forallFormula pd (eliminate_imply_neg (neg f))
  | AndList(fl) -> andList (List.map fl ~f:eliminate_imply_neg)
  | OrList(fl) -> orList (List.map fl ~f:eliminate_imply_neg)
  | Imply(f1, f2) -> eliminate_imply_neg (orList [neg f1; f2])
  | ForallFormula(pd, f) -> forallFormula pd (eliminate_imply_neg f)
  | ExistFormula(pd, f) -> existFormula pd (eliminate_imply_neg f)

let rec remove_inner_andList form =
  match form with
  | ForallFormula(_, _)
  | ExistFormula(_, _)
  | Chaos
  | Miracle
  | Eqn(_)
  | UIP(_)
  | Neg(Eqn(_)) -> [form]
  | AndList(fl) -> List.concat (List.map fl ~f:remove_inner_andList)
  | OrList(fl) -> [orList (List.concat (List.map fl ~f:remove_inner_orList))]
  | Neg(_)
  | Imply(_) -> raise Empty_exception
and remove_inner_orList form =
  match form with
  | ForallFormula(_, _)
  | ExistFormula(_, _)
  | Chaos
  | Miracle
  | Eqn(_)
  | UIP(_)
  | Neg(Eqn(_)) -> [form]
  | AndList(fl) -> [andList (List.concat (List.map fl ~f:remove_inner_andList))]
  | OrList(fl) -> List.concat (List.map fl ~f:remove_inner_orList)
  | Neg(_)
  | Imply(_) -> raise Empty_exception

let simplify form =
  let no_imply_neg = eliminate_imply_neg form in
  let rec wrapper form =
    match form with
    | ForallFormula(pd, f) -> forallFormula pd (wrapper f)
    | ExistFormula(pd, f) -> existFormula pd (wrapper f)
    | Chaos -> chaos
    | Miracle -> miracle
    | Eqn(_)
    | UIP(_)
    | Neg(UIP(_))
    | Neg(Eqn(_)) -> form
    | AndList(_) ->
      let simplified = List.map (remove_inner_andList form) ~f:wrapper in
      if List.exists simplified ~f:(fun x -> x = Miracle) then miracle
      else begin
        let not_chaos = List.dedup (List.filter simplified ~f:(fun x -> not (x = Chaos))) in
        match not_chaos with
        | [] -> chaos
        | [one] -> one
        | _ ->
          not_chaos
          |> List.map ~f:(fun x -> match x with | OrList(fl) -> fl | _ -> [x])
          |> cartesian_product
          |> List.map ~f:(fun x -> andList x)
          |> (fun fl -> match fl with | [andf] -> andf | _ -> orList fl)
      end
    | OrList(_) ->
      let simplified = List.map (remove_inner_orList form) ~f:(wrapper) in
      if List.exists simplified ~f:(fun x -> x = Chaos) then chaos
      else begin
        let not_miracle = List.dedup (List.filter simplified ~f:(fun x -> not (x = Miracle))) in
        match not_miracle with
        | [] -> miracle
        | [one] -> one
        | _ -> orList not_miracle
      end
    | Neg(_)
    | Imply(_) -> raise Empty_exception
  in
  wrapper no_imply_neg







let preprocess_rule_guard  ~loach:{name; types; vardefs; init; rules; properties} =
  let do_work (Rule(name, pds, f, s)) =
    let simplified = simplify f in
    match simplified with
    | OrList(fl) ->
      let indice = up_to (List.length fl) in
      List.map2_exn fl indice ~f:(fun g i -> rule (sprintf "%s__part__%d" name i) pds g s)
    | _ -> [rule name pds simplified s]
  in {
    name;
    types;
    vardefs;
    init;
    rules = List.concat (List.map rules ~f:do_work);
    properties
  }


let negDisjI2Implication f =
	let Neg(nf) = f in
	let fl=flat_loach_and_to_list nf in
	let conclusions=Utils.combination fl 1 in
	let listDiff l1 l2=List.filter ~f:(fun x -> not (List.mem  l2 x )) l1 in
	let preLs=List.map ~f:(fun x -> listDiff fl x) conclusions in
	let Some(pairLs)=List.zip preLs conclusions in
	let fs=List.map ~f:(fun (pre,cons) ->let [con]=cons in Imply(AndList(pre),Neg(con))) pairLs in
	fs


	
(*----------------------------- Translate module ---------------------------------*)

(** Translate language of this level to the next lower level *)
module Trans = struct

  exception Unexhausted_flatten

  (* Translate data structures from Loach to Paramecium *)

  let rec trans_exp ~types e =
    match e with
    | Const(c) -> Paramecium.const c
    | Var(x) -> Paramecium.var x
    | Param(pr) -> Paramecium.param pr
    | Ite(f, e1, e2) ->
      Paramecium.ite (trans_formula ~types f) (trans_exp ~types e1) (trans_exp ~types e2)
    | UIF(n, el) -> Paramecium.uif n (List.map el ~f:(trans_exp ~types))
  and trans_formula ~types form =
    match form with
    | Chaos -> Paramecium.chaos
    | Miracle -> Paramecium.miracle
    | UIP(n, el) -> Paramecium.uip n (List.map el ~f:(trans_exp ~types))
    | Eqn(e1, e2) -> Paramecium.eqn (trans_exp ~types e1) (trans_exp ~types e2)
    | Neg(f) -> Paramecium.neg (trans_formula ~types f)
    | AndList(fl) -> Paramecium.andList (List.map fl ~f:(trans_formula ~types))
    | OrList(fl) -> Paramecium.orList (List.map fl ~f:(trans_formula ~types))
    | Imply(f1, f2) -> Paramecium.imply (trans_formula ~types f1) (trans_formula ~types f2)
    | ForallFormula(paramdefs, f) -> 
      let ps = cart_product_with_paramfix paramdefs types in
      let f' = trans_formula ~types f in
      Paramecium.andList (List.map ps ~f:(fun p -> Paramecium.apply_form ~p f'))
    | ExistFormula(paramdefs, f) -> 
      let ps = cart_product_with_paramfix paramdefs types in
      let f' = trans_formula ~types f in
      Paramecium.orList (List.map ps ~f:(fun p -> Paramecium.apply_form ~p f'))

  let trans_statement ~types statement =
    let no_for = eliminate_for statement ~types in
    let rec wrapper statement =
      let balanced_statement =
        let statement' = balance_ifstatement statement in
        match statement' with
        | [] -> raise Empty_exception
        | s::[] -> s
        | _ -> parallel statement'
      in
      match balanced_statement with
      | Assign(v, e) -> Paramecium.assign v (trans_exp ~types e)
      | Parallel(slist) -> Paramecium.parallel (List.map slist ~f:wrapper)
      | IfelseStatement(f, s1, s2) ->
        let Paramecium.Assign(v1, e1) = wrapper s1 in
        let Paramecium.Assign(v2, e2) = wrapper s2 in
        if v1 = v2 then
          Paramecium.assign v1 (Paramecium.ite (trans_formula ~types f) e1 e2)
        else begin
          raise Empty_exception
        end
      | IfStatement(_, _)
      | ForStatement(_) -> raise Empty_exception
    in
    wrapper no_for

  let trans_prop ~types property =
    let Prop(n, p, f) = property in
    Paramecium.prop n p (trans_formula ~types f)

  let trans_rule ~types r =
    match r with
    | Rule(n, p, f, s) ->
      let f' = simplify f in
      let s' = trans_statement ~types s in
      match f' with
      | OrList(fl) ->
        let indice = up_to (List.length fl) in
        List.map2_exn fl indice ~f:(fun g i ->
          let new_name = sprintf "%s__part__%d" n i in
          Paramecium.rule new_name p (trans_formula ~types g) s'
        )
      | _ -> [Paramecium.rule n p (trans_formula ~types f') s']

  (** Translate language of Loach to Paramecium

      @param loach cache coherence protocol written in Loach
      @return the protocol in Paramecium
  *)
  let act ~loach:{name; types; vardefs; init; rules; properties} =
    let new_init = trans_statement ~types init in
    let new_prop = List.map properties ~f:(trans_prop ~types) in
    let new_rules = List.concat (List.map rules ~f:(trans_rule ~types)) in
    { Paramecium.name = name;
      types = types;
      vardefs = vardefs;
      init = new_init;
      rules = new_rules;
      properties = new_prop;
    }
  
  (*Inverse trans trans a paramecium thing to the loach one*)  
   let rec invTrans_exp   e =
    match e with
    | Paramecium.Const(c) -> const c
    | Paramecium.Var(x) ->  var x
    | Paramecium.Param(pr) ->  param pr
    | Paramecium.Ite(f, e1, e2) ->
       ite (invTrans_formula   f) (invTrans_exp   e1) (invTrans_exp   e2)
    | Paramecium.UIF(n, el) -> uif n (List.map el ~f:(invTrans_exp  ))
  and invTrans_formula   form =
    match form with
    | Paramecium.Chaos ->  chaos
    | Paramecium.Miracle -> miracle
    | Paramecium.UIP(n, el) -> uip n (List.map el ~f:(invTrans_exp  ))
    | Paramecium.Eqn(e1, e2) ->  eqn (invTrans_exp   e1) (invTrans_exp   e2)
    | Paramecium.Neg(f) ->  neg (invTrans_formula   f)
    | Paramecium.AndList(fl) ->  andList (List.map fl ~f:(invTrans_formula  ))
    | Paramecium.OrList(fl) ->  orList (List.map fl ~f:(invTrans_formula  ))
    | Paramecium.Imply(f1, f2) ->  imply (invTrans_formula   f1) (invTrans_formula   f2)  
	
	let invTrans_prop p=
		let Paramecium.Prop(n,pdfs,f)=p in
		Prop(n,pdfs, invTrans_formula f)
end















(*********************************** Module Variable Names, with Param values *****************)

(** Get variable names in the components *)
module VarNamesWithParam = struct
  
  open String.Set

  let of_var_ref = ref (fun _x -> of_list [])

  (** Names of exp *)
  let rec of_exp ~types e =
    match e with
    | Const(_)
    | Param(_) -> of_list []
    | Var(v) -> (!of_var_ref) v
    | Ite(f, e1, e2) -> union_list [of_form ~types f; of_exp ~types e1; of_exp ~types e2]
    | UIF(n, el) -> union_list (List.map el ~f:(of_exp ~types))
  (** Names of formula *)
  and of_form ~types f =
    match f with
    | Chaos
    | Miracle -> of_list []
    | UIP(n, el) -> union_list (List.map el ~f:(of_exp ~types))
    | Eqn(e1, e2) -> union_list [of_exp ~types e1; of_exp ~types e2]
    | Neg(form) -> of_form ~types form
    | AndList(fl)
    | OrList(fl) -> union_list (List.map fl ~f:(of_form ~types))
    | Imply(f1, f2) -> union_list [of_form ~types f1; of_form ~types f2]
    | ForallFormula(pd, f) ->
      let ps = cart_product_with_paramfix pd types in
      of_form ~types (andList (List.map ps ~f:(fun p -> apply_form f ~p)))
    | ExistFormula(pd, f) ->
      let ps = cart_product_with_paramfix pd types in
      of_form ~types (orList (List.map ps ~f:(fun p -> apply_form f ~p)))


  let rec of_statement ~types s =
    match s with
    | Assign(v, e) -> union_list [(!of_var_ref) v; of_exp ~types e]
    | Parallel(slist) -> union_list (List.map slist ~f:(of_statement ~types))
    | IfStatement(f, s) -> union_list [of_form ~types f; of_statement ~types s]
    | IfelseStatement(f, s1, s2) ->
      union_list [of_form ~types f; of_statement ~types s1; of_statement ~types s2]
    | ForStatement(_) -> raise Empty_exception

  let of_rule ~types ~of_var r = 
    of_var_ref := of_var;
    match r with
    | Rule(_, _, f, s) ->
      union_list [of_form ~types f; of_statement ~types s]
end












module ToSmv = struct
  open ToStr.Smv
  open Formula

  let types_ref = ref []
  let vardefs_ref = ref []

  let statement_act ?(is_init=false) statement guard =
    let analyzed = analyze_if statement guard ~types:(!types_ref) in
    let trans_assigns v guarded_exps =
      let rec wrapper guarded_exps cur_str =
        match guarded_exps with
        | [] -> cur_str
        | (g, e)::guarded_exps' ->
          let gstr = form_act (Formula.simplify (Trans.trans_formula ~types:(!types_ref) g)) in
          let estr = exp_act (Trans.trans_exp ~types:(!types_ref) e) in
          let cur_str' =
            if gstr = "FALSE" then
              cur_str
            else begin
              sprintf "%s%s : %s;\n" cur_str gstr estr
            end
          in
          if gstr = "TRUE" then
            cur_str'
          else begin
            wrapper guarded_exps' cur_str'
          end
      in
      let vstr = var_act v in
      let conditions = wrapper guarded_exps "" in
      if is_init then
        sprintf "init(%s) := case\n%sesac;" vstr conditions
      else begin
        sprintf "next(%s) := case\n%sTRUE : %s;\nesac;" vstr conditions vstr
      end
    in
    List.filter analyzed ~f:(fun (v, _) ->
      let Arrdef(_, tname) = List.find_exn (!vardefs_ref) ~f:(fun x ->
        let Arrdef(ls, t) = x in
        let parts = List.map ls ~f:(fun (n, pds) ->
          match pds with
          | [] -> [n]
          | _ ->
            let ps = cart_product_with_paramfix pds (!types_ref) in
            let const_strs = List.map ps ~f:(fun group -> 
              List.map group ~f:(fun pr -> paramref_act pr)
              |> String.concat
            ) in
            List.map const_strs ~f:(fun cstr -> sprintf "%s%s" n cstr)
        ) in
        let full_parts = cartesian_product parts in
        let full_names = List.map full_parts ~f:(fun parts -> String.concat ~sep:"." parts) in
        List.exists full_names ~f:(fun fn -> fn = var_act v)
      ) in
      List.length (name2type ~tname ~types:(!types_ref)) > 1
    )
    |> List.map ~f:(fun (v, guarded_exps) -> trans_assigns v guarded_exps)
    |> String.concat ~sep:"\n"

  let init_act statement =
    statement_act statement ~is_init:true chaos

  let rule_act r =
    let escape n =
      String.substr_replace_all n ~pattern:"[" ~with_:"__"
      |> String.substr_replace_all ~pattern:"]" ~with_:""
      |> String.substr_replace_all ~pattern:"." ~with_:"__"
    in
    let vars = String.Set.to_list (VarNamesWithParam.of_rule r ~types:(!types_ref) ~of_var:(fun v ->
      String.Set.of_list [var_act v]
    )) in
    let vars_str = String.concat vars ~sep:", " in
    (* rule process instance *)
    let Rule(n, _, f, s) = r in
    let name = escape n
    in
    let rule_proc_inst = sprintf "%s : process Proc__%s(%s);" name name vars_str in
    (* rule process *)
    let statement_str = escape (statement_act s f) in
    let rule_proc = 
      sprintf "MODULE Proc__%s(%s)\nASSIGN\n%s" name (escape vars_str) statement_str
    in
    (* result *)
    (rule_proc_inst, rule_proc)

  let prop_act property =
    let Prop(_, _, f) = property in
    sprintf "SPEC\n  AG (!%s)" (form_act (simplify (Trans.trans_formula ~types:(!types_ref) f)))



  let limit_params_in_typedef typedef =
    let Enum(name, consts) = typedef in
    enum name (List.filter consts ~f:(fun c ->
      match c with
      | Intc(i) -> i <= 30
      | _ -> true
    ))



  let protocol_act ?(limit_param=true) {name=_; types; vardefs; init; rules; properties} =
    let types = if limit_param then List.map types ~f:limit_params_in_typedef else types in
    types_ref := types;
    vardefs_ref := vardefs;
    let property_strs = [""] (* List.map properties ~f:prop_act *) in
    let rule_insts = List.concat (List.map rules ~f:(rule_to_insts ~types)) in
    let rule_proc_insts, rule_procs = List.unzip (List.map rule_insts ~f:(rule_act)) in
    let vardef_str =
      sprintf "VAR\n%s" (String.concat ~sep:"\n" (List.map vardefs ~f:(vardef_act ~types)))
    in
    let rule_proc_insts_str = String.concat ~sep:"\n\n" rule_proc_insts in
    let init_str = sprintf "ASSIGN\n%s" (init_act (eliminate_for init ~types)) in
    let prop_str = String.concat ~sep:"\n\n" property_strs in
    let rule_procs_str = String.concat ~sep:"\n\n---------\n\n" rule_procs in
    let strs = [vardef_str; rule_proc_insts_str; init_str; prop_str] in
    let main_module = 
      sprintf "MODULE main\n%s" (String.concat ~sep:"\n\n--------------------\n\n" strs)
    in
    sprintf "%s\n\n--------------------\n\n%s" main_module rule_procs_str


end







module PartParam = struct

  let attach name pf =
    let c =
      match pf with
      | Paramfix(_, _, x) -> x
      | _ -> raise Empty_exception
    in
    match c with
    | Strc(x) -> sprintf "%s_%s" name x
    | Intc(x) -> sprintf "%s_%d" name x
    | Boolc(x) -> sprintf "%s_%b" name x

  let attach_list name pfs =
    List.fold pfs ~init:name ~f:attach

  let apply_vardef vd ~insym_types ~types =
    let Arrdef(ls, tname) = vd in
    let rec wrapper head tail =
      match tail with
      | [] -> head
      | (name, pds)::tail' ->
        let insym_pds, sym_pds = List.partition_tf pds ~f:(fun (Paramdef(_, tn)) ->
          List.exists insym_types ~f:(fun t -> t = tn)
        ) in
        let ps = cart_product_with_paramfix insym_pds types in
        if ps = [] then
          let head' = List.map head ~f:(fun x -> x@[(name, pds)]) in
          wrapper head' tail'
        else begin
          let head' = List.concat (List.map head ~f:(fun x ->
            List.map ps ~f:(fun pfs ->
              let name' = List.fold pfs ~init:name ~f:attach in
              x@[(name', sym_pds)]
            )
          )) in
          wrapper head' tail'
        end
    in
    List.map (wrapper [[]] ls) ~f:(fun x -> arrdef x tname)


  let apply_paramref pr ~p =
    match pr with
    | Paramref(s) -> (
        match find_paramfix p s with
        | None -> pr
        | Some pf -> pf
      )
    | Paramfix(_) -> pr

  (* in Murphi, in-symmetric paramters should come ahead *)
  let apply_array (Arr(ls)) ~p =
    arr (List.map ls ~f:(fun (name, params) ->
      let prs, pfs =
        let insted = List.map params ~f:(apply_paramref ~p) in
        List.partition_tf insted ~f:(fun x -> match x with | Paramref(_) -> true | _ -> false)
      in
      attach_list name pfs, prs
    ))

  let rec apply_exp e ~p =
    match e with
    | Const(_) -> e
    | Var(x) -> var (apply_array x ~p)
    | Param(pr) ->
      begin
        let pr' = apply_paramref pr ~p in
        match pr' with
        | Paramref(_) -> param pr'
        | Paramfix(_, _, c) -> const c
      end
    | Ite(f, e1, e2) -> ite (apply_form f ~p) (apply_exp e1 ~p) (apply_exp e2 ~p)
    | UIF(n, el) -> uif n (List.map el ~f:(apply_exp ~p))
  and apply_form f ~p =
    match f with
    | Chaos
    | Miracle -> f
    | UIP(n, el) -> uip n (List.map el ~f:(apply_exp ~p))
    | Eqn(e1, e2) -> eqn (apply_exp e1 ~p) (apply_exp e2 ~p)
    | Neg(form) -> neg (apply_form form ~p)
    | AndList(fl) -> andList (List.map fl ~f:(apply_form ~p))
    | OrList(fl) -> orList (List.map fl ~f:(apply_form ~p))
    | Imply(f1, f2) -> imply (apply_form f1 ~p) (apply_form f2 ~p)
    | ForallFormula(paramdefs, form) -> forallFormula paramdefs (apply_form form ~p)
    | ExistFormula(paramdefs, form) -> existFormula paramdefs (apply_form form ~p)

  let rec apply_statement statement ~insym_types ~p ~types =
    match statement with
    | Assign(v, e) -> assign (apply_array v ~p) (apply_exp e ~p)
    | Parallel(sl) -> parallel (List.map sl ~f:(apply_statement ~insym_types ~p ~types))
    | IfStatement(f, s) -> ifStatement (apply_form f ~p) (apply_statement ~insym_types s ~p ~types)
    | IfelseStatement(f, s1, s2) ->
      ifelseStatement (apply_form f ~p) (
        apply_statement ~insym_types s1 ~p ~types
      ) (
        apply_statement s2 ~insym_types ~p ~types
      )
    | ForStatement(s, pd) ->
      let insym_pds, sym_pds = List.partition_tf pd ~f:(fun (Paramdef(_, tn)) ->
        List.exists insym_types ~f:(fun t -> t = tn)
      ) in
      let ps = cart_product_with_paramfix insym_pds types in
      if ps = [] then
        forStatement (apply_statement s ~insym_types ~p ~types) pd
      else begin
        parallel (List.map ps ~f:(fun p' ->
          if sym_pds = [] then
            apply_statement s ~insym_types ~p:(p@p') ~types
          else begin
            forStatement (apply_statement s ~insym_types ~p:(p@p') ~types) sym_pds
          end
        ))
      end

  let apply_rule r insym_types ~types =
    let Rule(n, paramdefs, f, s) = r in
    let insym_pds, sym_pds = List.partition_tf paramdefs ~f:(fun (Paramdef(_, tn)) ->
      List.exists insym_types ~f:(fun t -> t = tn)
    ) in
    let ps = cart_product_with_paramfix insym_pds types in
    let name p =
      if p = [] then n
      else begin
        let const_act c =
          match c with
          | Intc(i) -> Int.to_string i
          | Strc(s) -> String.lowercase s
          | Boolc(b) -> String.uppercase (Bool.to_string b)
        in
        let paramref_act pr =
          match pr with
          | Paramfix(pn, _, c) -> sprintf "%s%s" pn (const_act c)
          | Paramref(_) -> raise Unexhausted_inst
        in
        sprintf "%s_%s" n (String.concat ~sep:"_" (List.map p ~f:paramref_act))
      end
    in
    if ps = [] then
      [rule n paramdefs f (apply_statement s ~insym_types ~p:[] ~types)]
    else begin
      List.map ps ~f:(fun p ->
        rule (name p) sym_pds (apply_form f ~p) (apply_statement s ~insym_types ~p ~types)
      )
    end
    
    

  let apply_prop property insym_types ~types =
    let Prop(name, paramdefs, f) = property in
    let insym_pds, sym_pds = List.partition_tf paramdefs ~f:(fun (Paramdef(_, tn)) ->
      List.exists insym_types ~f:(fun t -> t = tn)
    ) in
    let ps = cart_product_with_paramfix insym_pds types in
    if ps = [] then
      [property]
    else begin
      List.map ps ~f:(fun p ->
        prop name sym_pds (apply_form f ~p)
      )
    end

  let apply_protocol insym_types protocol =
    let {name; types; vardefs; init; rules; properties} = protocol in
    let vardefs = List.concat (List.map vardefs ~f:(apply_vardef ~insym_types ~types)) in
    let init = apply_statement init ~insym_types ~p:[] ~types in
    let rules = List.concat (List.map rules ~f:(fun r -> apply_rule r insym_types ~types)) in
    let properties =
      List.map properties ~f:(fun property -> apply_prop property insym_types ~types)
      |> List.concat
    in
    { name;
      types;
      vardefs;
      init;
      rules;
      properties
    }
    
end    


 
(*module PararefCmp=Comparator.Make(struct
	type t=paramref
	let sexp_of_t (str,f) =sexp_of_paramref f
	let t_of_sexp s=paramref_of_sexp s
  let compare x y= String.compare (ToMurphi.paramref_act x) (ToMurphi.paramref_act y) 
    
end)*)


module ParasOf = struct
  
  open Int.Set

  (** fixed parameters of var *)
  let of_param p=
  match p with 
  | Paramref(_)-> of_list []
  | Paramfix(n,t,Intc(i)) -> of_list [i]
  
  let of_var v =
    let Arr(ls) = v in
     (union_list (List.map ls 
    ~f:(fun (n, prefs) -> union_list (List.map ~f:of_param prefs))))

  (** Names of exp *)
  let rec of_exp e =
    match e with
    | Const(_)-> of_list []
    | Param(p) -> of_param p
    | Var(v) -> of_var v
    | Ite(f, e1, e2) -> union_list [of_form f; of_exp e1; of_exp e2]
    | UIF(n, el) -> union_list (List.map el ~f:of_exp)
  (** Names of formula *)
  and of_form f =
    match f with
    | Chaos
    | Miracle -> of_list []
    | UIP(n, el) -> union_list (List.map el ~f:of_exp)
    | Eqn(e1, e2) -> union_list [of_exp e1; of_exp e2]
    | Neg(form) -> of_form form
    | AndList(fl)
    | OrList(fl) -> union_list (List.map fl ~f:of_form)
    | Imply(f1, f2) -> union_list [of_form f1; of_form f2]
		| ForallFormula(pds,f') -> of_form f'

  let rec of_statement s =
    match s with
    | Assign(v, e) -> union_list [of_var v; of_exp e]
    | Parallel(slist) -> union_list (List.map slist ~f:of_statement)    
	  | IfStatement(cond,s)-> union_list [of_form cond; of_statement s]
  | IfelseStatement(f,s1,s2) ->union_list [of_form f; of_statement s1;of_statement s2]
  | ForStatement(s,pdfs) -> of_statement s

  let of_rule r = 
    match r with
    | Rule(_, _, f, s) -> union_list [of_form f; of_statement s]
end    

module ComputeMap =struct

let dict=Core.Std.Hashtbl.create ~hashable:Core.Std.String.hashable () 
let full dict names =
	(List.length names)=(Core.Std.Hashtbl.length dict)
	
let apply_paramref pr  names dict=
  match pr with
  | Paramref(s) -> dict
  | Paramfix(pn,pt,Intc(i)) -> 
  	match (List.find ~f:(fun n -> n=pn) names) with
  	|Some(pn') ->  let ()= Core.Std.Hashtbl.replace dict ~key:(string_of_int i) ~data:pn in
  		dict
  	|None -> dict
  	
let rec apply_paramRefs refs names 	dict=
 	match refs with 
 	[] -> dict
 	|pref::refs0 ->
 		let dict1=apply_paramref pref  names dict in
 		if (full  dict1 names) then  dict1
 		else apply_paramRefs refs0 names 	dict1

(** Apply array with param *)
let rec apply_array (Arr(ls))    names dict =
	match ls with
	[] ->dict
	|l::ls' ->
		let (n, prefs)= l in
		let dict1=apply_paramRefs prefs  names dict in
		 
		if (full dict1 names) then  dict1
		else  apply_array (Arr(ls'))    names dict1  


let rec apply_exp e names dict =
  match e with
  | Const(_) -> dict
  | Var(x) -> (apply_array x  names dict)
  | Param(pr) ->  (apply_paramref pr  names dict)
  | Ite(f, e1, e2) -> 
     let dict1= (apply_form f  names dict) in
     if full dict1 names then
     	dict1
     else 
     begin
     	let dict2=(apply_exp e1  names dict1) in
     	 if full dict2 names then
     	dict2
     	else 
     	let dict3=(apply_exp e2  names dict2) in
     	dict3
     end	
  | UIF(n, el) -> 
  	match el with
  	[] -> dict
  	|(e::el') -> 
  	let dict1= (apply_exp e  names dict) in
  	 if full dict1 names then
     	dict1
     	else apply_exp (UIF(n,el')) names dict1
  
and apply_form f  names dict =
  match f with
  | Chaos
  | Miracle -> dict
  | UIP(n, el) -> 
  	begin
  	match el with
  	[] -> dict
  	|(e::el') -> 
  	let dict1= (apply_exp e  names dict) in
  	 if full dict1 names then
     	dict1
     	else apply_form (UIP(n,el')) names dict1
     end	
  | Eqn(e1, e2) -> 
  	let dict2=(apply_exp e1  names dict) in
     	 if full dict2 names then
     	dict2
     	else 
     	let dict3=(apply_exp e2  names dict2) in
     	dict3
     	
  | Neg(form) ->  (apply_form form  names dict)
  | AndList(fl) -> 
  	begin
  	match fl with
  	[] -> dict
  	|(f::fl') -> 
  	let dict1= (apply_form f  names dict) in
  	 if full dict1 names then
     	dict1
     	else apply_form (AndList(fl')) names dict1
   end  	
  | OrList(fl) -> 
  	begin
  	match fl with
  	[] -> dict
  	|(f::fl') -> 
  	let dict1= (apply_form f  names dict) in
  	 if full dict1 names then
     	dict1
     	else apply_form (AndList(fl')) names dict1
   end  	
  | Imply(f1, f2) ->  
  	let dict2=(apply_form f1  names dict) in
     	 if full dict2 names then
     	dict2
     	else 
     	let dict3=(apply_form f2  names dict2) in
     	dict3
  | ForallFormula(paramdefs, form) -> apply_form form  names dict
  | ExistFormula(paramdefs, form) -> apply_form form  names dict

let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false
  
let computeMapTable r prules=
	(* compute r is the instance of what prule in prules*)
	let Rule(rn,rdfs,rg,rbody)=r in
	let Some(pr)=List.find ~f:(fun (Rule(n,pdfs,g,s)) ->contains rn n) prules in
	let Rule(prn,prdfs,prg,prbody)=pr in	
	let ruleParaNames=List.map ~f:(fun (Paramdef(n,t)) -> n) prdfs in
	let ()=print_endline "ruleNames is" in
	let b=List.map ~f:(print_endline) ruleParaNames in
	let ()=Core.Std.Hashtbl.clear dict in  
	let dict=apply_form rg ruleParaNames dict in
	let ()=print_endline ("befor return") in
	let ()=print_endline (string_of_int (Core.Std.Hashtbl.length dict)) in
	dict
  
end	


module ParaNameReplace= struct
    
let apply_paramref pr     ~dict =
  match pr with
  | Paramref(s) -> pr
  | Paramfix(pn,pt,Intc(i)) -> 
  	match Core.Std.Hashtbl.find dict (string_of_int i) with
  	|Some(pn') -> Paramfix(pn',pt,Intc(i))
  	|None -> pr

(** Apply array with param *)
let apply_array (Arr(ls))   ~dict=
  arr (List.map ls ~f:(fun (name, params) ->
    name, List.map params ~f:(apply_paramref   ~dict)
  ))


let rec apply_exp e   ~dict=
  match e with
  | Const(_) -> e
  | Var(x) -> var (apply_array x   ~dict)
  | Param(pr) -> param (apply_paramref pr   ~dict)
  | Ite(f, e1, e2) -> ite (apply_form f   ~dict) (apply_exp e1   ~dict) (apply_exp e2   ~dict)
  | UIF(n, el) -> uif n (List.map el ~f:(apply_exp   ~dict))
and apply_form f   ~dict=
  match f with
  | Chaos
  | Miracle -> f
  | UIP(n, el) -> uip n (List.map el ~f:(apply_exp   ~dict))
  | Eqn(e1, e2) -> eqn (apply_exp e1   ~dict) (apply_exp e2   ~dict)
  | Neg(form) -> neg (apply_form form   ~dict)
  | AndList(fl) -> andList (List.map fl ~f:(apply_form   ~dict))
  | OrList(fl) -> orList (List.map fl ~f:(apply_form   ~dict))
  | Imply(f1, f2) -> imply (apply_form f1   ~dict) (apply_form f2   ~dict)
  | ForallFormula(paramdefs, form) -> forallFormula paramdefs (apply_form form   ~dict)
  | ExistFormula(paramdefs, form) -> existFormula paramdefs (apply_form form   ~dict)

let rec apply_statement statement  ~dict =
  match statement with
  | Assign(v, e) -> assign (apply_array v   ~dict) (apply_exp e   ~dict)
  | Parallel(sl) -> parallel (List.map sl ~f:(apply_statement   ~dict))
  | IfStatement(f, s) -> ifStatement (apply_form f   ~dict) (apply_statement s   ~dict)
  | IfelseStatement(f, s1, s2) ->
    ifelseStatement (apply_form f   ~dict) (apply_statement s1   ~dict) (apply_statement s2   ~dict)
  
  |  ForStatement(s, pd) ->
    let s' = apply_statement s   ~dict in
     forStatement s' pd



let apply_rule r   ~dict =
  let Rule(n, paramdefs, f, s) = r in
  
  rule n paramdefs (apply_form f   ~dict) (apply_statement s   ~dict)
  
end  


