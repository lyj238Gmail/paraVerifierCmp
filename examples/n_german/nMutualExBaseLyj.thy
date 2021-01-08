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

 
lemma "strengthen2' N (inv_57 i)  (eqn (IVar (Para ''n'' i)) (Const E)) =
  a
  "
  apply auto
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


definition rulesPP2 :: "nat \<Rightarrow> rule set" where
  "rulesPP2 N =
    (rulesOverDownN2 N (\<lambda> i j. {n_Try2 i j})) \<union>
    (rulesOverDownN2 N (\<lambda> i j. {n_Crit2 i j})) \<union>
    (rulesOverDownN2 N (\<lambda> i j. {n_Exit2 i j})) \<union>
   (rulesOverDownN2 N (\<lambda>i j. strengthenProtNormal2 N (\<lambda> i j. {n_Idle2 i j}) inv_57 i j))"

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
   {absTransfRule N (strengthenR2 (formulasOverDownN2 N inv_57 i ) [] (n_Idle2 i j)) })) \<union>
(rulesOverDownN2 N (\<lambda> i j. {absTransfRule N (n_Crit2 i j)})) \<union>
(rulesOverDownN2 N (\<lambda> i j. {absTransfRule N (n_Try2 i j)})) 
  "


axiomatization  where axiomOnReachOfAbsMutual [simp,intro]:
   "s \<in> reachableSet (set (allInitSpecs NC )) (rulesAbs  ) \<Longrightarrow>
  i\<le>NC \<Longrightarrow> j\<le>NC  \<Longrightarrow>  formEval (inv_57 i j) s "
 
axiomatization  where stateIsEnum  [simp,intro]:
  "isEnumVal s (IVar (Para ''n'' n1))"
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
    assume a1:"r \<in>rulesPP2 N"
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
             then show "isBoundFormula s n1 (Suc 0) (eqn (IVar (Para ''n'' n1)) (Const (enum ''control'' ''I'')))"
               by simp 
           qed
         qed
       qed
     qed
               
     have c1:"trans_sim_onRules  
   (rulesOverDownN2 N (\<lambda>i j. strengthenProtNormal2 N (\<lambda> i j. {n_Idle2 i j}) inv_57 i j))
    (rulesOverDownN2 N (\<lambda> i j. 
   {absTransfRule N (strengthenR2 (formulasOverDownN2 N inv_57 i ) [] (n_Idle2 i j)) })) NC s"
    proof(unfold trans_sim_onRules_def,rule allI,rule impI)
      fix r
      assume b1:"r \<in>  (rulesOverDownN2 N (\<lambda>i j. strengthenProtNormal2 N (\<lambda> i j. {n_Idle2 i j}) inv_57 i j)) "
      have b2:"\<exists> i j. i\<le>N\<and> j\<le>N \<and> r=strengthenR2 (formulasOverDownN2 N inv_57 i ) [] (n_Idle2 i j)"
        by(cut_tac b1,unfold rulesOverDownN2_def  strengthenProtNormal2_def,auto)
       then obtain n1 n2 where b2:"n1\<le>N\<and> n2\<le>N \<and>
      r= strengthenR2 (formulasOverDownN2 N inv_57 n1 ) [] (n_Idle2 n1 n2)" by auto
       show "\<exists>r'. r' \<in> (rulesOverDownN2 N (\<lambda> i j. 
   {absTransfRule N (strengthenR2 (formulasOverDownN2 N inv_57 i ) [] (n_Idle2 i j)) })) 
   \<and> trans_sim_on1 r r' NC s"
       proof(rule_tac x="absTransfRule N 
  (strengthenR2 (formulasOverDownN2 N inv_57 n1 ) [] (n_Idle2 n1 n2))" in exI,rule conjI)
         let ?r="absTransfRule N (strengthenR2 (formulasOverDownN2 N inv_57 n1) [] (n_Idle2 n1 n2))"
         show "?r
    \<in> rulesOverDownN2 N
        (\<lambda>i j. {absTransfRule N (strengthenR2 (formulasOverDownN2 N inv_57 i) [] (n_Idle2 i j))})"
           by (meson b2 rulesOverDownN2Ext singletonI)
            
         show "trans_sim_on1 r ?r NC s" 
         proof( simp only:b2 n_Idle2_def Let_def,
             rule_tac N="N" and i="n1" in   absRuleSim ,auto)
           show "wellFormedParallel s n1
             (Suc 0) N (assign (Para ''n'' n1, Const (enum ''control'' ''T'')))"
             apply(rule wellAssign,force) done
           show "wellFormedGuard s n1 (Suc 0) N (eqn (IVar (Para ''n'' n1)) (Const (enum ''control'' ''I''))) "
           proof(rule wellBound )
             have "isEnumVal s (IVar (Para ''n'' n1))"
               by blast
             then show "isBoundFormula s n1 (Suc 0) (eqn (IVar (Para ''n'' n1)) (Const (enum ''control'' ''I'')))"
               by simp 
           qed
         qed
       qed
     qed           
    have "r \<in>(rulesOverDownN2 N (\<lambda> i j. {n_Try2 i j})) \<or>
    r \<in>(rulesOverDownN2 N (\<lambda> i j. {n_Idle2 i j})) \<or>
    
    r \<in>(rulesOverDownN2 N (\<lambda> i j. {n_Crit2 i j})) \<or>
    
    r \<in>(rulesOverDownN2 N (\<lambda>i j. strengthenProtNormal2 N (\<lambda> i j. {n_Exit2 i j}) inv_57 i j)) "
      by(cut_tac a1, unfold rulesPP2_def,auto)
    moreover
    {assume b1:" r \<in>(rulesOverDownN2 N (\<lambda>i j. strengthenProtNormal2 N (\<lambda> i j. {n_Exit2 i j}) inv_57 i j)) "
      have b1:"\<exists> i j. i\<le>N\<and> j\<le>N \<and>
      r \<in> strengthenProtNormal2 N (\<lambda> i j. {n_Exit2 i j}) inv_57 i j"
        by(cut_tac b1,unfold rulesOverDownN2_def,auto)
      then obtain n1 n2 where b2:"n1\<le>N\<and> n2\<le>N \<and>
      r \<in> strengthenProtNormal2 N (\<lambda> i j. {n_Exit2 i j}) inv_57 n1 n2"
        by blast
      then have b3:"r=(strengthenR2 (formulasOverDownN2 N inv_57 n1 ) [])  (n_Exit2 n1 n2)"
        apply(unfold strengthenProtNormal2_def, simp)done

      have "\<exists>r'. r' \<in> rulesAbs \<and> trans_sim_on1 r r' NC s "
      proof -
        have c1:"n1 \<le>NC\<or> n1>NC"  by arith
        moreover
        {assume c1:"n1 \<le>NC"
         have "\<exists>r'. r' \<in> rulesAbs \<and> trans_sim_on1 r r' NC s "
         proof(rule_tac 
             x="absTransfRule NC (strengthenR2 (formulasOverDownN2 NC inv_57 n1 ) [] (n_Exit2 n1 n2))" 
              in exI,rule conjI
              )
           show "absTransfRule NC (strengthenR2 (formulasOverDownN2 NC inv_57 n1) [] (n_Exit2 n1 n2)) \<in> rulesAbs"
             apply(cut_tac c1,unfold rulesAbs_def rulesOverDownN2_def,auto simp del:n_Exit2_def)
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
