
open Core.Std


let genRulenameWithParams rname=rname^" i"

let genAbsRuleName rname=rname^"_Abs NC"

let lemmaHeadGen r rAbs absParams=
  let (rname,pds,r)=r in
  let pd_count_t = List.map absParams ~f:(fun x-> x^">NC") in
  let pd_str = String.concat ~sep:" & " pd_count_t in
  let nonAbsParams=List.filter (fun x -> (not (List.mem x absParams))) pds in 
  let pd_count_t1 = List.map nonAbsParams ~f:(fun x-> x^"\<le> NC") in
  let pd_str1 = String.concat ~sep:" & " pd_count_t1 in
  let rIsa=String.concat ~sep:" " ([rname]@pds)  in
  let (rnameAbs,pdsAbs,rAbs)=r in
  let rAbsIsa=String.concat ~sep:" " ([rnameAbs]@pdsAbs@["NC"])  in
  sprintf 
  "lemma lemmaOn%sGt:
  assumes a1:\"%s\" and 
  a2:\"s ∈ reachableSet (set (allInitSpecs N)) (rules N)\"  and a3:\"NC<N\" and  
  a4:\"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s\" %$
  shows \"trans_sim_on1 (%s)  (%s) (set invariantsAbs) s\" (is \"trans_sim_on1 ?r ?r' (set ?F) s\")
  proof(rule ruleSimCond1)
    show \" formEval (pre ?r) s ⟶formEval (pre ?r') s\" (is \"?A ⟶?B\")
    proof(rule impI)+
      assume b0:\"?A\""
  "
  rname 
  pd_str 
  rIsa
  (if List.length nonAbsParams=0 
   then ""
   else sprintf "and a5:\"%s\"" pd_str1)
  rAbsIsa

    sprintf    
"lemma lemmaOnIdleGtNc1:
  assumes a1:\"i>NC\" and a2:\"s ∈ reachableSet (set (allInitSpecs N)) (rules N)\" and a3:\"NC<N\" and  
  a4:\"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s\"
  shows \"trans_sim_on1 %s\"  (%s_ABS NC) (set invariantsAbs) s\" (is \"trans_sim_on1 ?r ?r' (set ?F) s\")
proof(rule ruleSimCond1)
  show \" formEval (pre ?r) s ⟶formEval (pre ?r') s\" (is \"?A ⟶?B\")
  proof(rule impI)+
    assume b0:\"?A\""   (genRulenameWithParams rname) (rname)

let lemmaProofGen rulePds prop  result=
    let (proofStr,count)=result in
    let (pn,pds,pinv)=prop in  
    let actualPsRng=List.map ~f:(fun x -> x - 1)  (Utils.up_to (List.length pds)) in
    （*now let we only consider invariants with less than 2 *)
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
          then String.concat ~sep:" " ([pn]@rulePds) 
          else String.concat ~sep:" " ([pn]@[let Some(h)=rulePds in h]@[x])
          end ))      
      actualParasInConcretInv in
    (*if (List.length pds=1)  then*)
     
    let  proofG  invTarg result=
      let (proofStr,count)=result in
      let curStr=
        sprintf 
        "from a4  have tmp:\"formEval %s  s\"   
            by (force simp del:%s_def) 
        have tmp1:\"formEval (%s  ) s\" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf%d,force+)qed
        with b1  have c%d:\"formEval  (conclude (%s)) s\" by auto"
          invConconcrete  
          pn
          invTarg  
          (if List.length pds=1 then 1 else 2)
          count invTarg  in      
      let  count=count +1 in
        (proofStr^curStr,count)  in
    let proofGs invTargs   result=
      let (str,count)=result in
      match invTargs with 
      | [] -> result
      | x:xs -> 
          proofGens xs (prooG x result) in
    proofGs invTargs result


let lemmaProofGenProps rulePds props result=
  match props with
  |[]-> result
  |x:xs ->lemmaProofGenProps rulePds xs 
    (lemmaProofGen rulePds prop result)

 (*let lemmaPooofGen (invName,paraNum) count=
 let invName01=if (paraNum=0) then invName else if(paraNum=1) then (invName^"0") else (invName^"0 1") in
 let invNamei1= if (paraNum=0) then invName else if(paraNum=1) then (invName^"i") else (invName^"i 0") in
 let invNamei0=if (paraNum=0) then invName else if(paraNum=1) then (invName^"i") else (invName^"0 1") in
 sprintf 
   "from a4  have c%d:\"formEval %s  s\"   by (force simp del:%s_def) 
    have c%d:\"formEval (%s  ) s\" 
    proof(cut_tac a1 a2 a3 c%d,rule axiomOnf2,force+)qed
    with b1  have c%d:\"formEval  (consOfInv (%s)) s\" by auto
     have c%d:\"formEval %s s\" 
     proof(cut_tac a1 a2 a3 c%d,rule axiomOnf2,force+)qed
     with b1 have c%d:\"formEval (consOfInv (%s)) s\" by auto"
    count invName01  invName  
    (count+1) invNamei0  
    count
   (count+2) invNamei0  
    (count + 3)  invNamei1
    count
    (count+2) invNamei1

 let lemmaProofGens invNameList =
    let lenList=List.map  ~f:(fun i->4*i)  (up_to (List.length invNameList) )   in
    let m=List.zip invNameList lenList in 
    let str1=String.concat ~sep:"\n" (List.map ~f:(fun (invName,count)-> lemmaPooofGen invName count) ) in
    str1*)

let genPart1 r props1 proofStr=
    let (rn,pds, pr)=r in
    let (str1,count)=lemmaProofGenProps pds props1 (proofStr,3) in
    
    let strs=List.map ~f:(fun i-> "c"^(itoa i)) (up_to m) in
    let str2=String.concat ~sep:" " strs in
    let end1=sprintf "%s
      from b1 %s show \"formEval (pre ?r') s\" 
       by auto
     qed
   next 
    show \"∀v. v∈varOfForm (pre ?r') ⟶ v ∈(varOfFormList invariantsAbs)\"
      by auto"  in 
      str1
      str2  in
    end1
    

let genPart2 props2 proofStr=

  let proofStr1=
  match props2 with
  |[]->""
  |[prop]->
  let [pn,ppds,pinv]=prop in
        sprintf 
        "from a4  have tmp:\"formEval (%s 0  ) s\"   by (force simp del:%s_def)
     have b4:\"formEval (%s i  ) s\" 
     proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed"
          pn pn
          pn
  in 
  sprintf "%s
  %s
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 b4,auto) done
   qed
 next
   show "∀  v. v ∈  varOfSent (act ?r) ⟶  v ∈ varOfFormList ?F ⟶ v ∈  varOfSent (act ?r')" by(cut_tac a1, auto)

  
 next 
   show "∀ v va. v ∈ varOfSent (act ?r') ⟶va∈varOfExp ( substExpByStatement (IVar v)  (act ?r'))⟶ va ∈ (varOfFormList ?F)"
      by auto  
qed"     
  proofStr
  proofStr1

    

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
  let (rname,pds,r)=r in
  let pd_count_t = List.map absParams ~f:(fun x-> x^">NC") in
  let pd_str = String.concat ~sep:" & " pd_count_t in
  let nonAbsParams=List.filter (fun x -> (not (List.mem x absParams))) pds in 
  let pd_count_t1 = List.map nonAbsParams ~f:(fun x-> x^"\<le> NC") in
  let pd_str1 = String.concat ~sep:" & " pd_count_t1 in
  let rIsa=String.concat ~sep:" " ([rname]@pds)  in
  let (rnameAbs,pdsAbs,rAbs)=r in
  let rAbsIsa=String.concat ~sep:" " ([rnameAbs]@pdsAbs@["NC"])  in
  sprintf 
  "lemma lemmaOn%sGtNc:
  assumes a1:\"%s\" and a2:\"s ∈ reachableSet (set (allInitSpecs N)) (rules N)\"  and  
  a4:\"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s\" %s
shows \"trans_sim_on1 (%s  ) skip (set invariantsAbs) s\" (is \"trans_sim_on1 ?r ?r' ?F s\")
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
  rIsa


    let head=lemmaHeadGen2  r rAbs absParams in
    let part1= genPart1 r props1 head in
    let part2=genPart2 props2 part1 in
    part2

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


lemmaProofGenLt r =
  let (rn,pds,pr)=r in
  let pd_count_t = List.map absParams ~f:(fun x-> x^"\<le>NC") in
  let pd_str = String.concat ~sep:" & " pd_count_t in
  let rIsa=String.concat ~sep:" " ([rname]@pds)  in
  sprintf  
  "lemma lemmaOn%sLeNc:
  assumes a1:\"%s\" 
  shows \"trans_sim_on1 (%s) (%s) (set invariantsAbs) s\" (is \"trans_sim_on1 ?r ?r ?F s\")
proof(rule ruleSimId)
  show  \"∀v. v∈varOfForm (pre ?r) ⟶  v ∈(varOfFormList invariantsAbs) \"
    by(cut_tac a1, auto) 
    
next
  show  b1: \"∀v a. a ∈ set (statement2Assigns (act ?r)) ⟶ v∈varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))⟶v ∈varOfFormList invariantsAbs \"
   proof(cut_tac a1,(rule allI)+,(rule impI)+,auto) qed
    
 qed"
 rn
 pd_str 
 rIsa rIsa 





