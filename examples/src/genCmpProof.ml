


open Utils
open Core.Std


open ToStr
open Isabelle
open Paramecium
open Loach

type lemmaCase=
	|CaseAbs of paramdef list* rule *rule* prop list * prop list
	|CaseSkip of paramdef list* rule
	|CaseId of rule


let genRulenameWithParams rname=rname^" i"

let genAbsRuleName rname=rname^"_Abs NC"

let pdf2Str pdf= 
	let Paramdef(vn,tn)=pdf in 
	vn

(*here an absParams is a *)
let lemmaHeadGen r rAbs absParams=
  let Rule(rname,pds,g,a)=r in
  let pd_count_t = List.map absParams ~f:(fun x-> (pdf2Str x)^">NC") in
  let pd_str = String.concat ~sep:" & " pd_count_t in
  let nonAbsParams=List.filter ~f:(fun x -> (not (List.mem  absParams x))) pds in 
  let pd_count_t1 = List.map nonAbsParams ~f:(fun x-> (pdf2Str x)^"\\<le> NC") in
  let pd_str1 = String.concat ~sep:" & " pd_count_t1 in
  let rStr=String.concat ~sep:" " ([rname]@[get_pd_name_list pds])  in
  let Rule(rnameAbs,pdsAbs,gAbs,aAbs)=rAbs in
  let rAbsIsa=String.concat ~sep:" " ([rnameAbs]@[get_pd_name_list  pdsAbs]@["NC"])  in
  sprintf 
  "lemma lemmaOn%sGt_%s:
  assumes a1:\"%s\" and 
  a2:\"s ∈ reachableSet (set (allInitSpecs N)) (rules N)\"  and a3:\"NC<N\" and  
  a4:\"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s\" %s
  shows \"trans_sim_on1 (%s)  (%s) (set invariantsAbs) s\" (is \"trans_sim_on1 ?r ?r' (set ?F) s\")
  proof(rule ruleSimCond1)
    show \" formEval (pre ?r) s ⟶formEval (pre ?r') s\" (is \"?A ⟶?B\")
    proof(rule impI)+
      assume b0:\"?A\"
  "
  rname  (String.concat (List.map ~f:pdf2Str absParams))
  pd_str   
  (if List.length nonAbsParams=0 
   then ""
   else sprintf "and a5:\"%s\"" pd_str1)
  rStr rAbsIsa
(*should consider the case when pds=[], pds=[1,2]*)

let lemmaProofGen rulePds prop  result=
    let (proofStr,count)=result in
    let Prop(pn,pds,pinv)=prop in  
    let actualPsRng=List.map ~f:(fun x -> x - 1)  (Utils.up_to (List.length pds)) in
    (*now let we only consider invariants with less than 2 *)
    let actualParasInConcretInv=
        if List.length pds=0 
        then []
        else begin
          if List.length pds=1 
          then ["0"] 
          else ["0";"1"]
          end  in
    let invConcrete=String.concat ~sep:" "   ([pn]@actualParasInConcretInv) in
    (* e.g., invConcrete=inv_1 0 1 *)
    let invTargets=List.map ~f:
      (fun x->
        (if List.length pds=0 
        then pn 
        else begin
          if List.length pds=1
          then String.concat ~sep:" " ([pn]@[get_pd_name_list rulePds]) 
          else String.concat ~sep:" " ([pn]@[get_pd_name_list  ([let Some(h)=List.hd rulePds in h])]@[x])
          end ))      
      actualParasInConcretInv in
    (*if (List.length pds=1)  then*)
     
    let  proofG  invTarg result=
      let (proofStr,count)=result in
      let curStr=
        sprintf 
        "from a4  have tmp:\"formEval (%s)  s\"   
            by (force simp del:%s_def) 
        have tmp1:\"formEval (%s  ) s\" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf%d,force+)qed
        with b0  have c%d:\"formEval  (conclude (%s)) s\" by auto\n"
          invConcrete  
          pn
          invTarg  
          (if List.length pds=1 then 1 else 2)
          count invTarg  in      
      let  count=count +1 in
        (proofStr^curStr,count)  in

    let rec proofGs invTargs   result=
      let (str,count)=result in
      match invTargs with 
      | [] -> result
      | x::xs -> 
          proofGs xs (proofG x result) in
    proofGs invTargets result


let rec lemmaProofGenProps rulePds props result=
  match props with
  |[]-> result
  |x::xs ->lemmaProofGenProps rulePds xs 
    (lemmaProofGen rulePds x result)

 

let genPart1 r props1 proofStr=
    let Rule(rn,pds, g,act)=r in
    let (str1,count)=lemmaProofGenProps pds props1 (proofStr,0) in
    
    let strs= (List.map ~f:(fun i-> "c"^(sprintf "%d" i)) (up_to count)) in
    let str2=String.concat ~sep:" " strs in
    let end1=sprintf "%s
      from b0 %s show \"formEval (pre ?r') s\" 
       by auto
     qed
   next "   
      str1
      str2  in
    end1
    

let genPart2 props2 proofStr=

  let proofStr1=
  match props2 with
  |[]->""
  |[prop]->
  let Prop(pn,ppds,pinv)=prop in
        sprintf 
        "from a4  have tmp:\"formEval (%s 0  ) s\"   by (force simp del:%s_def)
     have b4:\"formEval (%s i  ) s\" 
     proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed"
          pn pn
          pn
  in 
  sprintf "%s
	show \"(∀  v. v ∈  varOfSent (act  ?r') ⟶  v ∈ varOfFormList ?F ⟶ formEval (pre ?r) s ⟶ 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)\"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:\"v∈ (varOfFormList invariantsAbs)\"  and b2:\"formEval (pre ?r) s\" and b3:\"v ∈varOfSent (act ?r')\"
  %s
  show \"expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s\"  
       apply (cut_tac  a1 b1 b2 %s,auto) done
   qed
 next
   show \"∀  v. v ∈  varOfSent (act ?r) ⟶  v ∈ varOfFormList ?F ⟶ v ∈  varOfSent (act ?r')\" by(cut_tac a1, auto)

  
 next 
   show \"∀ v va. v ∈ varOfSent (act ?r') ⟶va∈varOfExp ( substExpByStatement (IVar v)  (act ?r'))⟶ va ∈ (varOfFormList ?F)\"
     by auto  
 next
   show \"∀v. v ∈ varOfForm (pre (?r')) ⟶ v ∈ varOfFormList ?F\" by auto
qed"     
  proofStr
  proofStr1
  (match props2 with |[]->"" |_->"b4")

(*next     
   show "(∀  v. v ∈  varOfSent (act  ?r') ⟶  v ∈ varOfFormList ?F ⟶ formEval (pre ?r) s ⟶ 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v∈ (varOfFormList invariantsAbs)"  and b2:"formEval (pre ?r) s" and b3:"v ∈varOfSent (act ?r')"

     from a4  have tmp:"formEval (inv__3 0  ) s"   by (force simp del:inv__3_def)
     have b4:"formEval (inv__3 i  ) s" 
     proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed

     show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 b4,auto) done
   qed*)
 
    

let lemmaProofOnGtKind1 props1 props2 r rAbs absParams=
    let head=lemmaHeadGen  r rAbs absParams in
    let part1= genPart1 r props1 head in
    let part2=genPart2 props2 part1 in
    part2


(*lemmaProofOnGtKind1 deal with case where
r and rAbs exists at the same time 
lemmaProofOnGt generates such a proof
-----
lemma lemmaOnIdleGtNc1:
  assumes a1:"i>NC" and a2:"s ∈ reachableSet (set (allInitSpecs N)) (rules N)" and a3:"NC<N" and  
  a4:"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s"
  shows "trans_sim_on1 (n_Idle  i) (n_ABS_Idle  NC) (set invariantsAbs) s" (is "trans_sim_on1 ?r ?r' (set ?F) s")
proof(rule ruleSimCond1)
  show " formEval (pre ?r) s ⟶formEval (pre ?r') s" (is "?A ⟶?B")
  proof(rule impI)+
    assume b1:"?A"  
------head      
    from a4  have b4:"formEval (inv__5 0 1 ) s"   by (force simp del:inv__5_def)
    have b5:"formEval (inv__5 i 0 ) s" 
    proof(cut_tac a1 a2 a3 b4,rule axiomOnf2,force+)qed
    with b1  have b6:"formEval (neg (eqn (IVar (Field (Para (Ident ''n'') 0) ''st'')) (Const E))) s" by auto
    have b7:"formEval (inv__5 i 1 ) s" 
     proof(cut_tac a1 a2 a3 b4,rule axiomOnf2,force+)qed
    with b1 have b7:"formEval (neg (eqn (IVar (Field (Para (Ident ''n'') 1) ''st'')) (Const E))) s" by auto

      
     from a4 have b8:"formEval (inv__6 0 1 ) s"    by (force simp del:inv__6_def)

     have b9:"formEval (inv__6 i 0 ) s" 
    proof(cut_tac a1 a2 a3 b8,rule axiomOnf2,force+)qed
    with b1 have b9:"formEval (neg (eqn (IVar (Field (Para (Ident ''n'') 0) ''st'')) (Const C))) s" by auto
     have b10:"formEval (inv__6 i 1 ) s" 
     proof(cut_tac a1 a2 a3 b8,rule axiomOnf2,force+)qed
     with b1 have b11:"formEval (neg (eqn (IVar (Field (Para (Ident ''n'') 1) ''st'')) (Const C))) s" by auto
    
     from b1 b6 b7 b9 b11 show "formEval (pre ?r') s" 
       by auto
   qed
 next     
   show "(∀  v. v ∈  varOfSent (act  ?r') ⟶  v ∈ varOfFormList ?F ⟶ formEval (pre ?r) s ⟶ 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v∈ (varOfFormList invariantsAbs)"  and b2:"formEval (pre ?r) s" and b3:"v ∈varOfSent (act ?r')"
-------part1
     from a4  have tmp:"formEval (inv__3 0  ) s"   by (force simp del:inv__3_def)
     have b4:"formEval (inv__3 i  ) s" 
     proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed

     show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 b4,auto) done
   qed
 next
   show "∀  v. v ∈  varOfSent (act ?r) ⟶  v ∈ varOfFormList ?F ⟶ v ∈  varOfSent (act ?r')" by(cut_tac a1, auto)

  
 next 
   show "∀ v va. v ∈ varOfSent (act ?r') ⟶va∈varOfExp ( substExpByStatement (IVar v)  (act ?r'))⟶ va ∈ (varOfFormList ?F)"
      by auto  
qed
------part2
*)

let lemmaProofOnGtKind2   r absParams=
  let Rule(rname,pds,g,act)=r in
  let pd_count_t = List.map absParams ~f:(fun x-> (pdf2Str x)^">NC") in
  let pd_str = String.concat ~sep:" & " pd_count_t in
  let nonAbsParams=List.filter ~f:(fun x -> (not (List.mem  absParams x))) pds in 
  let pd_count_t1 = List.map nonAbsParams ~f:(fun x-> (pdf2Str x)^"\<le> NC") in
  let pd_str1 = String.concat ~sep:" & " pd_count_t1 in
  let rStr=String.concat ~sep:" " ([rname]@[get_pd_name_list pds])  in
  (*let (rnameAbs,pdsAbs,rAbs)=r in
  let rAbsIsa=String.concat ~sep:" " ([rnameAbs]@pdsAbs@["NC"])  in*) 
  sprintf 
  "lemma lemmaOn%sGtNc:
  assumes a1:\"%s\" and a2:\"s ∈ reachableSet (set (allInitSpecs N)) (rules N)\"  and  
  a4:\"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s\" %s
shows \"trans_sim_on1 (%s  ) skipRule (set invariantsAbs) s\" (is \"trans_sim_on1 ?r ?r' ?F s\")
proof(unfold trans_sim_on1_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:\"state_sim_on1 s s2 (set invariantsAbs)\"
  show \"state_sim_on1 (trans (act (n_Try i)) s) s2 (set invariantsAbs)\"
  proof(cut_tac a1,unfold state_sim_on1_def,
    (rule allI)+,(rule impI)+)
    fix f v
    assume b1:\" f ∈(set invariantsAbs)\" and b2:\"v ∈ varOfForm f\"  

    have b30: \"(varOfFormList  invariantsAbs) = {v. ∃f. f ∈ set  invariantsAbs∧ v ∈ varOfForm f}\"
      using setOfList by blast
      
     
    from b1 and b2 and b30 have b4:\"v ∈ (varOfFormList  invariantsAbs)\" by blast
     
    from b4 have b5:\"trans (act (n_Try  i)) s v = s v\" 
      by (cut_tac a1  b4  ,auto) 

    from b0   have b6:\"s v =s2 v \"
      using b1 b2 state_sim_on1_def by blast  
    show \"trans (act (n_Try i)) s v= s2 v\"
      using b5 b6 by auto 
  qed
qed"
rname 
  pd_str 
  (if List.length nonAbsParams=0 
   then ""
   else sprintf "and a5:\"%s\"" pd_str1)
  rStr



(*
lemmaProofOnGtKind2 deal with the case where 
r only exists, but no rAbs does.
lemma lemmaOnTryGtNc:
  assumes a1:"i>NC" and a2:"s ∈ reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s"
shows "trans_sim_on1 (n_Try  i) (n_Try  0) (set invariantsAbs) s" (is "trans_sim_on1 ?r ?r' ?F s")
proof(unfold trans_sim_on1_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on1 s s2 (set invariantsAbs)"
  show "state_sim_on1 (trans (act (n_Try i)) s) s2 (set invariantsAbs)"
  proof(cut_tac a1,unfold state_sim_on1_def,
    (rule allI)+,(rule impI)+)
    fix f v
    assume b1:" f ∈(set invariantsAbs)" and b2:"v ∈ varOfForm f"  

    have b30: "(varOfFormList  invariantsAbs) = {v. ∃f. f ∈ set  invariantsAbs∧ v ∈ varOfForm f}"
      using setOfList by blast
      
     
    from b1 and b2 and b30 have b4:"v ∈ (varOfFormList  invariantsAbs)" by blast
     
    from b4 have b5:"trans (act (n_Try  i)) s v = s v" 
      by (cut_tac a1  b4  ,auto) 

    from b0   have b6:"s v =s2 v "
      using b1 b2 state_sim_on1_def by blast  
    show "trans (act (n_Try i)) s v= s2 v"
      using b5 b6 by auto 
  qed
qed
*)


let lemmaProofGenLt r =
  let Rule(rn,pds,g,act)=r in
  let pd_count_t = List.map pds ~f:(fun x-> (pdf2Str x)^"\\<le>NC") in
  let pd_str = String.concat ~sep:" & " pd_count_t in
  let rStr=String.concat ~sep:" " ([rn]@[get_pd_name_list pds])  in
  sprintf  
  "lemma lemmaOn%sLeNc_%s:
  assumes a1:\"%s\" 
  shows \"trans_sim_on1 (%s) (%s) (set invariantsAbs) s\" (is \"trans_sim_on1 ?r ?r ?F s\")
proof(rule ruleSimId)
  show  \"∀v. v∈varOfForm (pre ?r) ⟶  v ∈(varOfFormList invariantsAbs) \"
    by(cut_tac a1, auto) 
    
next
  show  b1: \"∀v a. a ∈ set (statement2Assigns (act ?r)) ⟶ v∈varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))⟶v ∈varOfFormList invariantsAbs \"
   proof(cut_tac a1,(rule allI)+,(rule impI)+,auto) qed
    
 qed"
 
rn (String.concat (List.map ~f:pdf2Str absParams))
pd_str 
rStr rStr


(*formally one case is: (paramsAbs, r, r_abs,props1,props2) ----for abstraction
(paramsAbs,r) ----all things are abstracted, skip
(r,)----for itself*) 


let getCaseAbsParams aCase=
	match aCase with
	|CaseAbs(absParams,r,r',props1,props2) -> absParams
	|CaseSkip(absParams, r) ->absParams
	|CaseId(r) ->[]

let lemmaProofGenOnOneRule r cases=
  let Rule(rn,pds,g,act)=r in
	let pdsStr=(get_pd_name_list pds) in
  let ruleConstr = if List.is_empty pds then
          Isabelle.analyze_rels_in_pds   "r" rn pds
        else
          sprintf "\\<exists> %s. %s"
            (get_pd_name_list pds)
            (Isabelle.analyze_rels_in_pds   "r" rn pds)
      in
	
  let rStr=String.concat ~sep:" " ([rn]@[pdsStr])  in
  let genCase oneCase=
    let absParams=getCaseAbsParams oneCase in
    let pd_count_t = List.map absParams ~f:(fun x-> (let Paramecium.Paramdef(vn,_)=x in vn)^">NC") in
    let pd_str = String.concat ~sep:" & " pd_count_t in
    let nonAbsParams=List.filter ~f:(fun x -> (not (List.mem  absParams x))) pds in 
    let pd_count_t1 = List.map nonAbsParams ~f:(fun x-> (let Paramecium.Paramdef(vn,_)=x in vn)^"\<le> NC") in
    let pd_str1 = String.concat ~sep:" & " pd_count_t1 in
    let condStr=String.concat ~sep:"&" [pd_str;pd_str1](*if pd_str1="" then pd_str 
        else begin
          if pd_str="" then pd_str1 
          else String.concat ~sep:"&" [pd_str;pd_str1] 
          end*) in
    let rStr=String.concat ~sep:" " ([rn]@[get_pd_name_list pds])  in
    let rAbsStr=
      match oneCase with
      |CaseSkip(absParams, r) -> "skipRule"
			|CaseId(r) -> rStr 
      |CaseAbs(absParams,r,absr,props1,props2)->
        let Rule(rnAbs,pdsAbs,g,a)=absr in
        String.concat ~sep:" " ([rn]@[get_pd_name_list  pdsAbs]@["NC"])  in
		let usedLemma=
			 match oneCase with
      |CaseSkip(absParams, r) -> sprintf "lemmaOn%sGt_%s"  rn (String.concat (List.map ~f:pdf2Str absParams))
			|CaseId(r) -> sprintf "lemmaOn%sLeNc_%s"  rn (String.concat (List.map ~f:pdf2Str absParams))
      |CaseAbs(absParams,r,absr,props1,props2)->
        sprintf "lemmaOn%sGt_%s"  rn (String.concat (List.map ~f:pdf2Str absParams)) in
     
			
    let moreOverStr=sprintf 
      "moreover{
       assume a1:\"%s\" 
        have \"∃r'. ?P1 r' ∧ ?P2 r'\"
        proof(rule_tac x=\"(%s)\" in exI,rule conjI)
          show  \"?P1 (%s) \" 
           by(cut_tac a1, auto) 
          next
          show  \"?P2 (%s) \"
           using lemmaOn%s local.a1 d0 by blast 
        qed
       }"  
      condStr
      rAbsStr
      rAbsStr
      rAbsStr
      usedLemma
     (* (String.concat ~sep:"_" ([rn]@[(get_pd_name_list absParams)]@[(get_pd_name_list nonAbsParams)])) *) in
    (condStr,moreOverStr)  in
  let casesStr=
    String.concat ~sep:"|"
    (List.map ~f:(fun x->fst (genCase x)) cases) in
  let moreOverStrs=
    String.concat ~sep:"\n"
    (List.map ~f:(fun x->snd (genCase x)) cases) in 
  sprintf 
  "
lemma lemmaOn%s: 
  assumes   a2:\"s ∈ reachableSet (set (allInitSpecs N)) (rules N)\"  and  
  a4:\"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s\" and a5:\"%s\"
  shows \"∃ r'. r' ∈ rulesAbs NC∧ trans_sim_on1 r r' (set invariantsAbs) s\" (is \"∃r'.?P1 r' ∧ ?P2 r'\")
proof -
  from a5 obtain %s where d0:\"%s\"  by blast
  have \"%s\" by auto
  %s
  ultimately show \"∃r'.?P1 r' ∧ ?P2 r'\" 
    by satx
qed
"
  rn 
  ruleConstr
  (pdsStr)   (analyze_rels_in_pds   "r" rn pds)
  casesStr
  moreOverStrs


(*
lemma lemmaOnTry: 
  assumes   a2:"s ∈ reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s" and a5:"∃i. i≤N ∧ r=(n_Try  i)"
  shows "∃ r'. r' ∈ rulesAbs NC∧ trans_sim_on1 r r' (set invariantsAbs) s" (is "∃r'.?P1 r' ∧ ?P2 r'")
proof -
  from a5 obtain i where d0:"i≤N ∧ r=(n_Try  i)"  by blast
  have "i ≤ NC | i> NC" by auto
  moreover{
  assume a1:"i ≤NC" 
  have "∃r'. ?P1 r' ∧ ?P2 r'"
  proof(rule_tac x="(n_Try  i)" in exI,rule conjI)

    show  "?P1 (n_Try  i) " 
      by(cut_tac a1, auto) 
    
  next
    show  "?P2 (n_Try  i) "
      using lemmaOnTryLeNc local.a1 d0 by blast 
  qed
}
 moreover{
  assume a1:"i >NC" 
  have "∃r'. ?P1 r' ∧ ?P2 r'"
  proof(rule_tac x="(n_Try  0)" in exI,rule conjI)

    show  "?P1 (n_Try  0) " 
      by(cut_tac a1, auto) 
    
  next
    show  "?P2 (n_Try  0) "
    
      using lemmaOnTryGtNc local.a1 a2 a4 d0 by blast 
  qed 
}
  ultimately show "∃r'.?P1 r' ∧ ?P2 r'" 
    by satx
qed
*)
(*
n_Crit n_ABS_Crit_i*)




(*
Besides the CMPed rules, the CMP procedure also need provide a table to record:
r --CaseAbs(abstracted params * abstractedRule *abspropsStrengthen* absPropsDataRefinement)
r --CaseSkip(abstracted params ) ---means all the action is abstracted * skip * [] * []
r---CaseId(r ) --no params are needed abstarcted
1.generate all cases for paratitioning abstracted and nonabstracted parameters
2.generate each lemma for each cases
3.generate the summary lemma*)


let lemmaGenerateCase aCase =
  match aCase with
  |CaseAbs(absParams,r,rAbs,propsGuard,propsAct) ->
    lemmaProofOnGtKind1 propsGuard propsAct r rAbs absParams

  |CaseSkip(absParams,r)->
    lemmaProofOnGtKind2   r absParams

  |CaseId(r)->
    lemmaProofGenLt  r 

(*
1.generate all cases for paratitioning abstracted and nonabstracted parameters
2.generate each lemma for each cases
3.generate the summary lemma*)
let lemmaGenerate r allCases=   
  let allLemmasStr=String.concat ~sep:"\n" 
      (List.map ~f:lemmaGenerateCase allCases)  in
  let sumLemmaStr=lemmaProofGenOnOneRule r allCases in
     allLemmasStr^sumLemmaStr


let lemmaGenerates cmpList=
	let str=String.concat ~sep:"\n" 
		(List.map ~f:(fun pair -> let (r,cases)=pair in lemmaGenerate r cases) 
			cmpList)  in
	str

let cmpPair2Case  rules props cmpPair=
	let (rn, tuples)=cmpPair in	
	let Some(r)=List.find ~f:(fun r -> let Rule(rn',pds,g,a) = r  in rn=rn') rules in
	let Rule(rn,rParams,g,act)=r in
	let findParam pStr=List.find ~f:(fun p->let Paramdef(vn,tn)=p in vn=pStr) rParams in
	let dealWith tuple =
		let (kind,absParams,rAbsName,props1,props2)=tuple in		
 		let absParams=List.map ~f:(fun x-> let Some(y)=findParam x in y) absParams in
		if (kind =2)
		then CaseSkip(absParams,r)   
		else  begin
		
		let ()=print_endline rAbsName in
		let Some(rAbs)=List.find ~f:(fun r -> let  Rule(rn',pds,g,a) = r  in rAbsName=rn') rules in
		let propsGuard=match props1 with
			|[]->[]
			| _->List.map  
				~f:(fun pn' -> let ()=print_endline ("here"^pn') in
					let x=List.find ~f:(fun prop->  let  Prop(pn,pds,pinv) = prop  in let ()=print_endline pn in pn=pn') props in  
					match x with 
					|Some(x) -> x
					(*|None -> let ()=print_endline "No Match" in error("this")*) ) props1 in  
					
		let propsAct=match props2 with
			|[]->[]
			|_ -> List.map  
			~f:(fun pn' -> 
					let Some(x)=List.find ~f:(fun prop-> let  Prop(pn,pds,pinv) = prop  in pn=pn') props in x)   props2 in
		CaseAbs(absParams,r,rAbs,propsGuard,propsAct) end in		
(r,(List.map ~f:dealWith  tuples)@[CaseId(r)])	
	
let skip=
	let name="skipRule" in
	let params=[] in
	rule name [] chaos (parallel [(assign (global "x") (var (global "x")));]) 

let readCmp rules props fileName=
	let cmpPairs=GetCmpAbstractInfo.readCmpFromFile fileName in
	let casePairs=List.map ~f:(cmpPair2Case  rules props) cmpPairs in
	let filename =   "tmpParsingFile"   in
	let out=Out_channel.create filename    in
	let str=
		 ( lemmaGenerates casePairs)   in
  let ()=Out_channel.write_all filename  str in
	 Out_channel.close out 


