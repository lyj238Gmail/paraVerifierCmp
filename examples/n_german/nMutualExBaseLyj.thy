theory nMutualExBaseLyj
  imports Symmetric
begin

text \<open>Represents four states: idle, try, critical, exit\<close>

definition I :: scalrValueType where [simp]: "I \<equiv> enum ''control'' ''I''"
definition T :: scalrValueType where [simp]: "T \<equiv> enum ''control'' ''T''"
definition C :: scalrValueType where [simp]: "C \<equiv> enum ''control'' ''C''"
definition E :: scalrValueType where [simp]: "E \<equiv> enum ''control'' ''E''"

definition true :: scalrValueType where [simp]: "true \<equiv> boolV True"
definition false :: scalrValueType where [simp]: "false \<equiv> boolV False"


text \<open>Initial condition: all processes in idle.
  \<forall>i. n[i] = I
\<close>
definition initSpec0 :: "nat \<Rightarrow> formula" where [simp]:
  "initSpec0 N \<equiv> forallForm  (\<lambda>i. eqn (IVar (Para ''n'' i)) (Const I)) N"

text \<open>Initial condition: x is True\<close>
definition initSpec1 :: formula where [simp]:
  "initSpec1 \<equiv> eqn (IVar (Ident ''x'')) (Const true)"

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
  "allInitSpecs N \<equiv> [initSpec0 N, initSpec1]"


text \<open>No two processes can be in the exit state in the same time.
  i \<noteq> j \<longrightarrow> n[i] = E \<longrightarrow> n[j] \<noteq> E
\<close>
definition inv_7 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
  "inv_7 i j \<equiv>
    implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para ''n'' i)) (Const E))) 
      (neg (eqn (IVar (Para ''n'' j)) (Const E)))"

text \<open>There cannot be one state in exit and another in critical.
  i \<noteq> j \<longrightarrow> n[i] = E \<longrightarrow> n[j] \<noteq> C
\<close>
definition inv_5 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
  "inv_5 i j \<equiv>
    implyForm (andForm (neg (eqn (Const (index i)) (Const (index j))))  
      (eqn (IVar (Para ''n'' i)) (Const E))) (neg (eqn (IVar (Para ''n'' j)) (Const C)))"

definition inv_57 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where
  "inv_57 i j = andForm (inv_5 i j) (inv_7 i j)"



lemma inv_57_symmetric2:
  "symmetricParamFormulas2 N inv_57"
  unfolding symmetricParamFormulas2_def inv_57_def by auto

(*lemma a1:
  shows "i\<le>N \<longrightarrow>strengthen2 (map (inv_57 i) (down N))  (eqn (IVar (Para ''n'' i)) (Const E)) =
 a " (is "i\<le>N \<longrightarrow>?P N")
proof (induct_tac N)
  show "i\<le>0\<longrightarrow>?P 0"
  proof
    assume a1:"i\<le>0"
    from a1 have a1:"i=0" by arith
    show "?P 0"
      apply(cut_tac a1,unfold inv_57_def,auto)*)

lemma forallLemmaInc:
  "formEval (forallForm pf (Suc N)) s =
  (formEval (forallForm pf ( N)) s \<and> formEval (pf (Suc N)) s)"
  sorry

lemma andFormCong:
  assumes a1: "formEval A s=formEval A' s" and  a2:"formEval B s=formEval B' s"
  shows "formEval (andForm A B) s=formEval (andForm A' B') s" 
  sorry
lemma "formEval
  (strengthen2' N (inv_57 i)  (eqn (IVar (Para ''n'' i)) (Const E)) ) s
=
 formEval ( andForm  (eqn (IVar (Para ''n'' i)) (Const E))
  (forallForm 
  (\<lambda>j. if (i=j) then 
      chaos 
      else andForm (neg (eqn (IVar (Para ''n'' j)) (Const C)))
  (neg (eqn (IVar (Para ''n'' j)) (Const E)))) N)) s" (is "?P N")
proof (induct_tac N)
  show " ?P 0"
    by (auto simp add:strengthenForm_def inv_57_def)
next 
  fix N
  assume a1:"?P N"
  show "?P (Suc N)"
    using a1 andFormCong 
    
    by (auto simp add:strengthenForm_def inv_57_def)

qed
  
(* andForm  (eqn (IVar (Para ''n'' i)) (Const E))
 (andList (map  (\<lambda>j. if (i=j) then chaos else andForm (neg (eqn (IVar (Para ''n'' j)) (Const C)))   
  (neg (eqn (IVar (Para ''n'' j)) (Const E)))) (down N)))

  apply simp*)

definition n_Try2 :: "nat \<Rightarrow> nat\<Rightarrow> rule" where [simp]:
  "n_Try2 i j\<equiv>
    let g = (eqn (IVar (Para ( ''n'') i)) (Const I)) in
    let s =(assign ((Para ( ''n'') i), (Const T))) in
      guard g s"

text \<open>Enter critical region
  n[i] = T \<and> x = True \<rightarrow> n[i] := C; x := False
\<close>
definition n_Crit2 :: "nat \<Rightarrow> nat\<Rightarrow>rule" where [simp]:
  "n_Crit2 i j\<equiv>
    let g = (andForm (eqn (IVar (Para ( ''n'') i)) (Const T))
   (eqn (IVar (Ident ''x'')) (Const true))) in
    let s = (parallel (assign ((Para ( ''n'') i), (Const C)))
     (assign ((Ident ''x''), (Const false)))) in
      guard g s"

text \<open>Exit critical region
  n[i] = C \<rightarrow> n[i] := E
\<close>
definition n_Exit2::"nat \<Rightarrow> nat\<Rightarrow>rule" where [simp]:
  "n_Exit2 i j\<equiv>
    let g = (eqn (IVar (Para ( ''n'') i)) (Const C)) in
    let s = (assign ((Para ( ''n'') i), (Const E))) in
      guard g s"

text \<open>Move to idle
  n[i] = E \<rightarrow> n[i] := I; x := True
\<close>
definition n_Idle2 :: "nat \<Rightarrow> nat\<Rightarrow>rule" where [simp]:
  "n_Idle2 i j \<equiv>
    let g = (eqn (IVar (Para ( ''n'') i)) (Const E)) in
    let s = (parallel
  (assign ((Para ( ''n'') i), (Const I)))
   (assign ((Ident ''x''), (Const true)))) in
      guard g s"

 

definition rules_i :: " nat\<Rightarrow> nat\<Rightarrow>rule set" where
  "rules_i   i j = {n_Try2 i j} Un { n_Crit2 i j} Un { n_Exit2 i j} Un{ n_Idle2 i j }"

subsection \<open>Strengthened rules\<close>



lemma rule_i2_symmetric':
  "symmetricParamRules2' N (rules_i )"
  unfolding symmetricParamRules2'_def rules_i_def
  using  alphaEqRuleSet_def by auto

definition rulesPP1 :: "nat \<Rightarrow> rule set" where
  "rulesPP1 N =
    (rulesOverDownN2 N (\<lambda> i j. {n_Try2 i j})) \<union>
    (rulesOverDownN2 N (\<lambda> i j. {n_Crit2 i j})) \<union>
    (rulesOverDownN2 N (\<lambda> i j. {n_Idle2 i j})) \<union>
    (rulesOverDownN2 N (\<lambda>i j. strengthenProtNormal1 N (\<lambda> i j. {n_Exit2 i j}) inv_57 i j))"

lemma n_n_Exit2_symmetric':
  "symmetricParamRules2' N ((\<lambda> i j. {n_Exit2 i j}) )"
  unfolding symmetricParamRules2'_def rules_i_def
  using  alphaEqRuleSet_def by auto

lemma n_n_Try2_symmetric':
  "symmetricParamRules2' N ((\<lambda> i j. {n_Try2 i j}) )"
  unfolding symmetricParamRules2'_def rules_i_def
  using  alphaEqRuleSet_def by auto


lemma n_n_Crit2_symmetric':
  "symmetricParamRules2' N ((\<lambda> i j. {n_Crit2 i j}) )"
  unfolding symmetricParamRules2'_def rules_i_def
  using  alphaEqRuleSet_def by auto

lemma n_n_Idle2_symmetric':
  "symmetricParamRules2' N ((\<lambda> i j. {n_Idle2 i j}) )"
  unfolding symmetricParamRules2'_def rules_i_def
  using  alphaEqRuleSet_def by auto

theorem rules2_symmetric:
  "symProtRules' N (rulesPP1 N)"
proof -
  have a0:"symProtRules' N 
    (rulesOverDownN2 N (\<lambda>i j. strengthenProtNormal1 N (\<lambda> i j. {n_Exit2 i j}) inv_57 i j))"
  unfolding rulesPP1_def  thm  symProtFromSymmetricParam2'
  apply (rule symProtFromSymmetricParam2')
  apply (rule strengthenProtSymmetric2') thm strengthenProtSymmetric2
  apply (rule n_n_Exit2_symmetric')
  by (rule inv_57_symmetric2)
  have a1:"symProtRules' N (rulesOverDownN2 N (\<lambda> i j. {n_Try2 i j}))"
    using n_n_Try2_symmetric' symProtFromSymmetricParam2' by blast
  have a3:"symProtRules' N (rulesOverDownN2 N (\<lambda> i j. {n_Idle2 i j}))"
    using n_n_Idle2_symmetric' symProtFromSymmetricParam2' by blast  
  have a4:"symProtRules' N (rulesOverDownN2 N (\<lambda> i j. {n_Crit2 i j}))"
    using n_n_Crit2_symmetric' symProtFromSymmetricParam2' by blast  
  


  show ?thesis
    using  a0 a1 a3 a4  rulesPP1_def symProtRulesUnion by presburger
qed

definition inv_5_7::"nat \<Rightarrow> paraFormula list" where
"inv_5_7 i\<equiv> [inv_5 i, inv_7 i]"

definition rulesPP2 :: "nat \<Rightarrow> rule set" where
  "rulesPP2 N =
    (rulesOverDownN2 N (\<lambda> i j. {n_Try2 i j})) \<union>
    (rulesOverDownN2 N (\<lambda> i j. {n_Crit2 i j})) \<union>
    (rulesOverDownN2 N (\<lambda> i j. {n_Exit2 i j})) \<union>
   (rulesOverDownN2 N (\<lambda>i j. strengthenProtNormal2 N (\<lambda> i j. {n_Idle2 i j}) inv_5_7 i j))"

subsection{*Definitions of each abstracted rule*}

definition  NC::"nat " where [simp]: "NC==1"


(*
definition n_Idle_abs::"rule" where [simp]:
"n_Idle_abs  \<equiv>
let g = (andForm (andForm (eqn (IVar (Ident ''x'')) (Const false)) 
(andList (map  (\<lambda>j. (neg (eqn (IVar (Para ( ''n'') j)) (Const E)))) (down NC))))
(andList (map  (\<lambda>j. (neg (eqn (IVar (Para ( ''n'') j)) (Const C)))) (down NC)))) in
let s = (parallelList [(assign ((Ident ''x''), (Const true)))]) in
guard g s"



 

definition n_Crit_abs::"rule" where [simp]:
"n_Crit_abs  \<equiv>
let g = (eqn (IVar (Ident ''x'')) (Const true)) in
let s = (parallelList [(assign ((Ident ''x''), (Const false)))]) in
guard g s"

definition rulesAbs_i' :: " nat\<Rightarrow> nat\<Rightarrow>rule set" where  [simp]:
  "rulesAbs_i'   i j = {n_Try2 i j} Un { n_Crit2 i j} Un
   { n_Exit2 i j} Un{ n_Idle2 i j }  Un { n_Crit_abs  } Un
   { n_Idle_abs }  "

subsection{*The set of All actual Rules w.r.t. a Protocol Instance with Size $N$*}
definition rulesAbs::" rule set" where [simp]:
"rulesAbs   \<equiv>  (rulesOverDownN2 NC (\<lambda> i j. {n_Try2 i j})) \<union>
    
    (rulesOverDownN2 NC (\<lambda> i j. {n_Exit2 i j})) \<union>
   (rulesOverDownN2 NC (\<lambda> i j. 
       {absTransfRule NC (strengthenR2 (formulasOverDownN2 NC inv_57 i ) [] (n_Idle2 i j)) })) \<union>
   (rulesOverDownN2 NC (\<lambda>i j.  {n_Crit2 i j}) )Un
   { n_Crit_abs  } Un
   { n_Idle_abs }
  "
*)
definition rulesAbs1::" nat\<Rightarrow>rule set" where [simp]:
"rulesAbs1 N  \<equiv>  
(rulesOverDownN2 N (\<lambda> i j. {absTransfRule NC (n_Exit2 i j)})) \<union>
 (rulesOverDownN2 N (\<lambda> i j. 
   {absTransfRule NC (strengthenR2' N [  inv_5 i, inv_7 i]  [] (n_Idle2 i j)) })) \<union>
(rulesOverDownN2 N (\<lambda> i j. {absTransfRule NC (n_Crit2 i j)})) \<union>
(rulesOverDownN2 N (\<lambda> i j. {absTransfRule NC (n_Try2 i j)})) 
  "
(*(rulesOverDownN2 N (\<lambda> i j. 
   {absTransfRule NC (strengthenR2 (formulasOverDownN2 N inv_57 i ) [] (n_Idle2 i j)) }))*)

lemma assumes a:"NC <N"

    shows "semanticRuleSetEq (rulesOverDownN2 N (\<lambda> i j. {absTransfRule NC (n_Exit2 i j)}) )
  (rulesOverDownN2 NC (\<lambda> i j. {  (n_Exit2 i j)}) Un {skipRule})"  (is "semanticRuleSetEq ?S1 ?S2")
proof(unfold semanticRuleSetEq_def,rule conjI)
  show "\<forall>r1 \<in>?S1. \<exists>r2\<in>?S2. semanticRuleEq r1 r2"
  proof(rule ballI )
    fix r1
    assume a1:"r1 \<in>?S1"
    have a2:"EX i j. i\<le>N \<and> j\<le>N \<and> r1=absTransfRule NC (n_Exit2 i j)"
      using a1 rulesOverDownN2_def by auto
    then obtain i j where a3:"i\<le>N \<and> j\<le>N \<and> r1=absTransfRule NC (n_Exit2 i j)"
      by blast

    have a4:"i\<le>NC |i>NC " 
      by arith
    moreover
    {assume a4:"i \<le>NC"
      have a5:"r1= (n_Exit2 i j)"
        by(cut_tac a3 a4,auto) 
      have " \<exists>r2\<in>rulesOverDownN2 NC (\<lambda>i j. {n_Exit2 i j}) \<union> {skipRule}. semanticRuleEq r1 r2"
        apply(rule_tac x="r1" in bexI)
        using semanticRuleEqReflex apply blast
        apply(cut_tac a4 a5,auto simp add:rulesOverDownN2_def)
        done
    }
   moreover
    {assume a4:"i >NC"
      have a5:"r1= skipRule"
       by(cut_tac a3 a4,auto) 
      have " \<exists>r2\<in>rulesOverDownN2 NC (\<lambda>i j. {n_Exit2 i j}) \<union> {skipRule}. semanticRuleEq r1 r2"
        apply(rule_tac x="r1" in bexI)
        using semanticRuleEqReflex apply blast
        apply(cut_tac a4 a5,auto simp add:rulesOverDownN2_def)
        done
    } 
    ultimately show " \<exists>r2\<in>rulesOverDownN2 NC (\<lambda>i j. {n_Exit2 i j}) \<union> {skipRule}. semanticRuleEq r1 r2"
      by blast
  qed
next
  show "\<forall>r2 \<in>?S2. \<exists>r1\<in>?S1. semanticRuleEq r1 r2"
  proof(rule ballI )
    fix r2
    assume a1:"r2 \<in>?S2"
    have a2:"(EX i j. i\<le>NC \<and> j\<le>NC \<and> r2=  (n_Exit2 i j))| r2=skipRule"
      using a1 rulesOverDownN2_def by auto
    
    moreover
    {assume a4:"(EX i j. i\<le>NC \<and> j\<le>NC \<and> r2=  (n_Exit2 i j))"
      from a4 obtain i j where a4:"i\<le>NC \<and> j\<le>NC \<and> r2=  (n_Exit2 i j)"
      by blast
        
      have " \<exists>r1\<in>rulesOverDownN2 N (\<lambda>i j. {absTransfRule NC (n_Exit2 i j)}). semanticRuleEq r1 r2 "
        apply(rule_tac x="absTransfRule NC r2" in bexI)
        using semanticRuleEqReflex apply(cut_tac a4,simp)
        apply(cut_tac a, simp add:a4  rulesOverDownN2_def)
        by blast 
        
    

    
    }
   moreover
    {assume a4:"r2=skipRule" 
      have " \<exists>r1\<in>rulesOverDownN2 N (\<lambda>i j. {absTransfRule NC (n_Exit2 i j)}). semanticRuleEq r1 r2"
        apply(rule_tac x="absTransfRule NC (n_Exit2 (Suc NC) 0)" in bexI)
        using semanticRuleEqReflex apply(cut_tac a4,simp)
        apply(cut_tac a, simp add:a4  rulesOverDownN2_def)
        by blast
         
    } 
    ultimately show "\<exists>r1\<in>rulesOverDownN2 N (\<lambda>i j. {absTransfRule NC (n_Exit2 i j)}). semanticRuleEq r1 r2"
      by blast
  qed
qed
  
axiomatization  where axiomOnReachOfAbsMutual [simp,intro]:
   "s \<in> reachableSet (set (allInitSpecs NC )) (rulesAbs  ) \<Longrightarrow>
  i\<le>NC \<Longrightarrow> j\<le>NC  \<Longrightarrow>  formEval (inv_57 i j) s "
 
axiomatization  where stateIsEnum  [simp,intro]:
  "isEnumVal s (IVar (Para ''n'' n1))"

axiomatization  where xIsBool  [simp,intro]:
  "isBoolVal s (IVar (Ident ''x''))"
lemma iINDown:
  shows a1:"j \<in> set (down N)\<longrightarrow> j \<le> N"
proof(induct_tac N,auto)qed


subsection\<open>Definitions of initial states
1.abs protocol can simulate mutualPP2\<close> 
lemma absMutualSimmutualPP2:
  assumes a1:"NC\<le>N"
  shows "protSim (andList (allInitSpecs N)) (andList (allInitSpecs NC))  
   (rulesPP2 N) (rulesAbs1 N) NC"
proof(unfold protSim_def,rule )
  have b1:"\<forall>s. formEval (andList (allInitSpecs N)) s \<longrightarrow>
    formEval  (andList (allInitSpecs NC)) s"
    apply(cut_tac a1,auto)
    done
    
  show "pred_sim_on (andList (allInitSpecs N)) (andList (allInitSpecs NC)) NC"
  proof(cut_tac a1 b1,unfold pred_sim_on_def,auto) qed
next
  show " \<forall>s. trans_sim_onRules (rulesPP2 N) (rulesAbs1 N) NC s "
  proof((rule allI)+)
    fix s 
    

    have c1:"trans_sim_onRules  (rulesOverDownN2 N (\<lambda> i j. {n_Try2 i j}))
    (rulesOverDownN2 N (\<lambda> i j. {absTransfRule NC (n_Try2 i j)})) NC s"
    proof(unfold trans_sim_onRules_def,rule allI,rule impI)
      fix r
      assume b1:"r \<in> rulesOverDownN2 N (\<lambda>i j. {n_Try2 i j}) "
      have b2:"\<exists> i j. i\<le>N\<and> j\<le>N \<and> r= n_Try2 i j"
        by(cut_tac b1,unfold rulesOverDownN2_def,auto)
       then obtain n1 n2 where b2:"n1\<le>N\<and> n2\<le>N \<and>
      r= n_Try2  n1 n2" by auto
       show "\<exists>r'. r' \<in> rulesOverDownN2 N (\<lambda>i j. {absTransfRule NC (n_Try2 i j)}) \<and> trans_sim_on1 r r' NC s"
       proof(rule_tac x="absTransfRule NC r" in exI,rule conjI)
         show "absTransfRule NC r \<in> rulesOverDownN2 N (\<lambda>i j. {absTransfRule NC (n_Try2 i j)})"
           using b2 rulesOverDownN2_def by auto
         show "trans_sim_on1 r (absTransfRule NC r) NC s" 
         proof( simp only:b2 n_Try2_def Let_def,
             rule_tac N="N" and i="n1" in   absRuleSim ,auto)
           show "wellFormedParallel s n1
             (Suc 0) N (assign (Para ''n'' n1, Const (enum ''control'' ''T'')))"
             apply(rule wellAssign,force) done
           show "wellFormedGuard s n1 (Suc 0) N (eqn (IVar (Para ''n'' n1)) (Const (enum ''control'' ''I''))) "
           proof(rule wellBound )
             have "isEnumVal s (IVar (Para ''n'' n1))"
               by blast
            
               
             then show "safeFormula s n1 (Suc 0) (eqn (IVar (Para ''n'' n1)) (Const (enum ''control'' ''I'')))"
               apply simp done
           qed
           show " Suc 0 \<le> N"
             using NC_def assms by linarith
              
         qed
       qed
     qed
               
     have c2:"trans_sim_onRules  
   (rulesOverDownN2 N (\<lambda>i j. strengthenProtNormal2 N (\<lambda> i j. {n_Idle2 i j}) inv_5_7 i j))
    (rulesOverDownN2 N (\<lambda> i j. 
   {absTransfRule NC (strengthenR2' N [  inv_5 i, inv_7 i] [] (n_Idle2 i j)) })) NC s"
    proof(unfold trans_sim_onRules_def,rule allI,rule impI)
      fix r
      assume b1:"r \<in>  (rulesOverDownN2 N (\<lambda>i j. strengthenProtNormal2 N (\<lambda> i j. {n_Idle2 i j}) inv_5_7 i j)) "
      have b2:"\<exists> i j. i\<le>N\<and> j\<le>N \<and> r=strengthenR2' N ( inv_5_7 i ) [] (n_Idle2 i j)"
        by(cut_tac b1,unfold rulesOverDownN2_def  strengthenProtNormal2_def,auto)
       then obtain n1 n2 where b2:"n1\<le>N\<and> n2\<le>N \<and>
      r= strengthenR2' N (inv_5_7 n1 ) [] (n_Idle2 n1 n2)" by auto
       show "\<exists>r'. r' \<in> (rulesOverDownN2 N (\<lambda> i j. 
   {absTransfRule NC (strengthenR2' N  ( [inv_5 i, inv_7 i] ) [] (n_Idle2 i j)) })) 
   \<and> trans_sim_on1 r r' NC s"
       proof(rule_tac x="absTransfRule NC 
  (strengthenR2' N ( [inv_5 n1, inv_7 n1] ) [] (n_Idle2 n1 n2))" in exI,rule conjI)
         let ?r="absTransfRule NC (strengthenR2' N  ([inv_5 n1, inv_7 n1]) [] (n_Idle2 n1 n2))"
         show "?r
    \<in> rulesOverDownN2 N
        (\<lambda>i j. {absTransfRule NC (strengthenR2' N ([inv_5 i, inv_7 i]) [] (n_Idle2 i j))})"
           by (meson b2 rulesOverDownN2Ext singletonI)
            
         show "trans_sim_on1 r ?r NC s" 
         proof( simp only:b2 inv_5_7_def, rule_tac N="N" and i="n1" in   absRuleSim )
          
           show "wellFormedParallel s n1
             NC N (act (strengthenR2' N (  inv_57 n1) [] (n_Idle2 n1 n2)))"
             apply(simp)
             apply(rule wellParallel,rule wellAssign,simp,rule wellGlobal,simp) 
             apply simp
             done
           show "wellFormedGuard s n1 NC N 
              (pre (strengthenR2' N ( inv_57 n1) [] (n_Idle2 n1 n2))) "
           proof(simp, rule wellAndForm )
             have d1:"isEnumVal s (IVar (Para ''n'' n1))"
               by blast
             then show "wellFormedGuard s n1 (Suc 0)  N
              (eqn (IVar (Para ''n'' n1)) (Const (enum ''control'' ''E'')))"
               by (simp add: d1 wellBound) 
             show " wellFormedGuard s n1 (Suc 0) N
     (forallForm
       (\<lambda>j. strengthenForm (inv_57 n1 j) (eqn (IVar (Para ''n'' n1)) (Const (enum ''control'' ''E'')))) N)"
               apply(rule wellForallForm1) 
               apply(rule allI,case_tac "i=n1")
               apply( simp add:inv_57_def  inv_5_def inv_7_def )
               using d1 apply auto[1]
               apply( simp add:inv_57_def  inv_5_def inv_7_def )
               using stateIsEnum by auto
                
             
           qed
           show " mutualDiffDefinedStm (act (strengthenR2' N (inv_57 n1) [] (n_Idle2 n1 n2)))"
           proof(simp)qed
         qed
       qed
     qed 

have c3:"trans_sim_onRules  (rulesOverDownN2 N (\<lambda> i j. {n_Crit2 i j}))
    (rulesOverDownN2 N (\<lambda> i j. {absTransfRule NC (n_Crit2 i j)})) NC s"
    proof(unfold trans_sim_onRules_def,rule allI,rule impI)
      fix r
      assume b1:"r \<in> rulesOverDownN2 N (\<lambda>i j. {n_Crit2 i j}) "
      have b2:"\<exists> i j. i\<le>N\<and> j\<le>N \<and> r= n_Crit2 i j"
        by(cut_tac b1,unfold rulesOverDownN2_def,auto)
       then obtain n1 n2 where b2:"n1\<le>N\<and> n2\<le>N \<and>
      r= n_Crit2  n1 n2" by auto
       show "\<exists>r'. r' \<in> rulesOverDownN2 N (\<lambda>i j. {absTransfRule NC (n_Crit2 i j)}) \<and> trans_sim_on1 r r' NC s"
       proof(rule_tac x="absTransfRule NC r" in exI,rule conjI)
         show "absTransfRule NC r \<in> rulesOverDownN2 N (\<lambda>i j. {absTransfRule NC (n_Crit2 i j)})"
           using b2 rulesOverDownN2_def by auto
         show "trans_sim_on1 r (absTransfRule NC r) NC s" 
           apply( simp only:b2 n_Crit2_def Let_def,
             rule_tac N="N" and i="n1" in   absRuleSim,simp )
            apply(simp,rule wellAndForm)
             apply(rule wellBound)
           using stateIsEnum apply auto[1]
            apply(rule wellBound)
           using xIsBool apply auto[1]
           apply(simp,rule wellParallel)
           apply (simp add: wellFormedParallel.intros(3))
           by (simp add: wellFormedParallel.intros(1))
            
           
           qed
         qed


have c4:"trans_sim_onRules  (rulesOverDownN2 N (\<lambda> i j. {n_Exit2 i j}))
    (rulesOverDownN2 N (\<lambda> i j. {absTransfRule NC (n_Exit2 i j)})) NC s"
    proof(unfold trans_sim_onRules_def,rule allI,rule impI)
      fix r
      assume b1:"r \<in> rulesOverDownN2 N (\<lambda>i j. {n_Exit2 i j}) "
      have b2:"\<exists> i j. i\<le>N\<and> j\<le>N \<and> r= n_Exit2 i j"
        by(cut_tac b1,unfold rulesOverDownN2_def,auto)
       then obtain n1 n2 where b2:"n1\<le>N\<and> n2\<le>N \<and>
      r= n_Exit2  n1 n2" by auto
       show "\<exists>r'. r' \<in> rulesOverDownN2 N (\<lambda>i j. {absTransfRule NC (n_Exit2 i j)}) \<and> trans_sim_on1 r r' NC s"
       proof(rule_tac x="absTransfRule NC r" in exI,rule conjI)
         show "absTransfRule NC r \<in> rulesOverDownN2 N (\<lambda>i j. {absTransfRule NC (n_Exit2 i j)})"
           using b2 rulesOverDownN2_def by auto
         show "trans_sim_on1 r (absTransfRule NC r) NC s" 
           apply( simp only:b2 n_Exit2_def Let_def,
             rule_tac N="N" and i="n1" in   absRuleSim ,auto)
           apply(rule wellBound)
           using stateIsEnum apply auto[1]
           by (simp add: wellFormedParallel.intros(3)) 
           qed
         qed
       
         show "trans_sim_onRules (rulesPP2 N) (rulesAbs1 N) NC s"
           apply(simp only:rulesPP2_def rulesAbs1_def)
           using tranSimOnrulesUn c1 c2 c3 c4 by auto
       qed
     qed

lemma absMutualSimmutualPP21:
  assumes a1:"s \<in> reachableSetUpTo (andList (allInitSpecs N)) (rulesPP2 N) i" and a2:"N>1"
  shows "s \<in> reachableSetUpTo (andList (allInitSpecs NC)) (rulesAbs ) i \<and>
 (\<forall>i j. i\<le>NC \<longrightarrow> j\<le>NC \<longrightarrow>  formEval (inv_57 i j) s)"
  sorry unfold formulasOverDownN2_def,rule conjI ,
              unfold rulesAbs_def rulesOverDownN2_def,force  ,cut_tac b3 c1,
(*definition rulesAbs::"nat \<Rightarrow> rule set" where [simp]:
"rulesAbs N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_Try  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Crit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Exit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Idle  i) \<or>
(r=n_Crit_abs  ) \<or>
(r=n_Idle_abs )\<or> r=skipRule
}"*)





end
