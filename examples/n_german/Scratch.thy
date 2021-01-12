have c4:"trans_sim_onRules  (rulesOverDownN2 N (\<lambda> i j. {n_Exit i j}))
    (rulesOverDownN2 N (\<lambda> i j. {absTransfRule NC (n_Exit i j)})) NC s"
    proof(unfold trans_sim_onRules_def,rule allI,rule impI)
      fix r
      assume b1:"r \<in> rulesOverDownN2 N (\<lambda>i j. {n_Exit i j}) "
      have b2:"\<exists> i j. i\<le>N\<and> j\<le>N \<and> r= n_Exit i j"
        by(cut_tac b1,unfold rulesOverDownN2_def,auto)
       then obtain n1 n2 where b2:"n1\<le>N\<and> n2\<le>N \<and>
      r= n_Exit  n1 n2" by auto
       show "\<exists>r'. r' \<in> rulesOverDownN2 N (\<lambda>i j. {absTransfRule NC (n_Exit i j)}) \<and> trans_sim_on1 r r' NC s"
       proof(rule_tac x="absTransfRule NC r" in exI,rule conjI)
         show "absTransfRule NC r \<in> rulesOverDownN2 N (\<lambda>i j. {absTransfRule NC (n_Exit i j)})"
           using b2 rulesOverDownN2_def by auto
         show "trans_sim_on1 r (absTransfRule NC r) NC s" 
           apply( simp only:b2 n_Exit_def Let_def,
             rule_tac N="N" and i="n1" in   absRuleSim ,auto)
           apply (meson andFormCong evalNeg)
           apply (meson andFormCong evalNeg)
           done
           qed
         qed
