
open Core.Std


let genRulenameWithParams rname=rname^" i"

let genAbsRuleName rname=rname^"_Abs NC"

let lemmaHeadGen rname =
    sprintf    
"lemma lemmaOnIdleGtNc1:
  assumes a1:\"i>NC\" and a2:\"s ∈ reachableSet (set (allInitSpecs N)) (rules N)\" and a3:\"NC<N\" and  
  a4:\"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s\"
  shows \"trans_sim_on1 %s\"  (%s_ABS NC) (set invariantsAbs) s\" (is \"trans_sim_on1 ?r ?r' (set ?F) s\")
proof(rule ruleSimCond1)
  show \" formEval (pre ?r) s ⟶formEval (pre ?r') s\" (is \"?A ⟶?B\")
  proof(rule impI)+
    assume b0:\"?A\""   (genRulenameWithParams rname) (rname)

 let lemmaPooofGen (invName,paraNum) count=
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
    str1

let genPart1 invNameList=
    let str1=lemmaProofGens invNameList in
    let strs=List.map ~f:(fun i-> "c"^(itoa i)) m in
    let str2=String.concat ~sep:" " strs in
    let end1=sprintf "
      from b1 %s show \"formEval (pre ?r') s\" 
       by auto
   qed
   next     
   show \"(∀  v. v ∈  varOfSent (act  ?r') ⟶  v ∈ varOfFormList ?F ⟶ formEval (pre ?r) s ⟶ 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)\"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:\"v∈ (varOfFormList invariantsAbs)\"  and b2:\"formEval (pre ?r) s\" and b3:\"v ∈varOfSent (act ?r')\"" str2 in
   str1^end1

let genPart2 invNameList=
    let str1=lemmaProofGens invNameList in
    let strs=List.map ~f:(fun i-> "c"^(itoa i)) (List.length invNameList) in
    let str2=String.concat ~sep:" " strs in
    let end1=sprintf "show \"expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s\"  
       apply (cut_tac  a1 b1 b2 %s,auto) done
   qed
 next
   show \"∀  v. v ∈  varOfSent (act ?r) ⟶  v ∈ varOfFormList ?F ⟶ v ∈  varOfSent (act ?r')\" by(cut_tac a1, auto) 
 next show \"∀ v va. v ∈ varOfSent (act ?r') ⟶va∈varOfExp ( substExpByStatement (IVar v)  (act ?r'))⟶ va ∈ (varOfFormList ?F)\"
      by auto  
  qed" str2 in
   str1^end1

let lemmaProof invNameList1 invNameList2 ruleName=
    let head=lemmaHeadGen ruleName in
    let part1= genPart1 invNameList1 in
    let part2=genPart2 invNameList1 in
    head^part1^part2

