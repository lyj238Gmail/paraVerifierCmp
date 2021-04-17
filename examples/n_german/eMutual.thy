theory eMutual
  imports ECMP
begin


subsection \<open>Definitions\<close>

text \<open>type definitions \<close>

definition I :: scalrValueType where [simp]: "I \<equiv> enum ''control'' ''I''"
definition T :: scalrValueType where [simp]: "T \<equiv> enum ''control'' ''T''"
definition C :: scalrValueType where [simp]: "C \<equiv> enum ''control'' ''C''"
definition E :: scalrValueType where [simp]: "E \<equiv> enum ''control'' ''E''"

definition true :: scalrValueType where [simp]: "true \<equiv> boolV True"
definition false :: scalrValueType where [simp]: "false \<equiv> boolV False"

text \<open>initial state \<close>
definition initSpec0 :: "nat \<Rightarrow> formula" where
  "initSpec0 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''n'' i) =\<^sub>f Const I) N"


definition initSpec1 :: formula where
  "initSpec1 \<equiv> IVar (Ident ''x'') =\<^sub>f Const true"



definition allInitSpecs :: "nat \<Rightarrow> formula list" where
  "allInitSpecs N \<equiv> [
    (initSpec0 N),
    (initSpec1 ) 
  ]"


lemma symPreds:
  "symPredSet' N ({initSpec0 N} \<union> {initSpec1})"
  apply (rule symPredsUnion)
  subgoal
    unfolding initSpec0_def
    apply (rule symPredSetForall)
    unfolding symParamForm_def by auto    
  subgoal
    unfolding symPredSet'_def initSpec1_def by auto
  done


lemma symPreds':
  "symPredSet' N (set (allInitSpecs N))"
  proof -
    have b1:"(set (allInitSpecs N)) =
      {(initSpec0 N)} \<union>
    {initSpec1}" (is "?LHS=?RHS")
      using allInitSpecs_def by auto
    have b2:"symPredSet' N ?RHS"
      using symPreds by blast
    show "symPredSet' N (set (allInitSpecs N))"
      using b1 b2 by auto  
  qed    

definition env::"nat\<Rightarrow>envType" where [simp]:
"env N\<equiv> \<lambda>v. (case v of
    (Para n i) \<Rightarrow> if (n=''n'' \<and>i \<le>N) then enumType else anyType|
    (Ident n) \<Rightarrow> if n=''x'' then boolType  else anyType|
    _ \<Rightarrow> anyType)"

lemma absInitSpec:
  assumes "M \<le> N"
  shows "absTransfForm (env N) M (initSpec0 N) = initSpec0 M"
        "absTransfForm (env N)M initSpec1 = initSpec1"
  unfolding initSpec0_def initSpec1_def using assms by auto
 

text \<open>rules \<close>

 

definition n_Try :: "nat \<Rightarrow> rule" where
  "n_Try i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const I
   \<triangleright>
    assign (Para ''n'' i, Const T)"



lemma symTry:
  "symParamRule  N n_Try"
  "wellFormedRule (env N) N (n_Try i)"
  "absTransfRule (env N) M (n_Try i) = (if i \<le> M then n_Try i else chaos \<triangleright> skip)"
  unfolding n_Try_def symParamRule_def by auto


 
definition n_Crit :: "nat \<Rightarrow> rule" where
  "n_Crit i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const T \<and>\<^sub>f
    IVar (Ident ''x'') =\<^sub>f Const true
   \<triangleright>
    assign (Para ''n'' i, Const C) ||
    assign (Ident ''x'', Const false)"

definition n_Crit_abs :: rule where
  "n_Crit_abs \<equiv>
    IVar (Ident ''x'') =\<^sub>f Const (boolV True)
   \<triangleright>
    assign (Ident ''x'', Const (boolV False))"


lemma symCrit:
  "symParamRule N n_Crit"
  "wellFormedRule (env N) N (n_Crit i)"
  "absTransfRule (env N) M (n_Crit i) = (if i \<le> M then n_Crit i else n_Crit_abs)"
  unfolding n_Crit_def n_Crit_abs_def symParamRule_def by auto


 
definition n_Exit :: "nat \<Rightarrow> rule" where
  "n_Exit i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const C
   \<triangleright>
    assign (Para ''n'' i, Const E)"



lemma symExit:
  "symParamRule N n_Exit"
  "wellFormedRule (env N)  N (n_Exit i)"
  "absTransfRule (env N) M (n_Exit i) = (if i \<le> M then n_Exit i else chaos \<triangleright> skip)"
  unfolding n_Exit_def symParamRule_def by auto


definition n_Idle :: "nat \<Rightarrow> rule" where
  "n_Idle i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const E
   \<triangleright>
    assign (Para ''n'' i, Const I) ||
    assign (Ident ''x'', Const true)"

text \<open>aux invs\<close>

definition invAux1 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where
  "invAux1 N i \<equiv> IVar (Para ''n'' i) =\<^sub>f Const E \<longrightarrow>\<^sub>f forallFormExcl 
    (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C \<and>\<^sub>f \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N"  


lemma symInvAux1:
  "symParamForm N (invAux1 N)"
  unfolding invAux1_def
  apply (auto intro!: symParamFormImply symParamFormAnd symParamFormForall symParamFormForallExcl)
  unfolding symParamForm_def symParamForm2_def equivForm_def by auto
 
definition n_Idle2_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_Idle2_ref N i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const E \<and>\<^sub>f
    forallFormExcl (\<lambda>j.( \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C)  \<and>\<^sub>f
       \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N
   \<triangleright>
    assign (Para ''n'' i, Const I) ||
    assign (Ident ''x'', Const true)"
 
lemma n_Idle2Eq:
  "strengthenRule2 (invAux1 N i) (n_Idle i) = n_Idle2_ref N i"
  by (auto simp add: strengthenRule2.simps invAux1_def n_Idle_def n_Idle2_ref_def)

definition n_Idle_abs2 :: "nat \<Rightarrow> rule" where
"n_Idle_abs2 M \<equiv>
    (\<forall>\<^sub>fj. ((\<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const (enum ''control'' ''C''))\<and>\<^sub>f
      (\<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const (enum ''control'' ''E'')))) M 
   \<triangleright>
    assign (Ident ''x'', Const (boolV True))"

 

lemma symIdle:
  "symParamRule N n_Idle"
  "wellFormedRule (env N) N (n_Idle i)" 
  unfolding n_Idle_def  symParamRule_def by auto

 

lemma symIdle2_ref:
  "symParamRule N (n_Idle2_ref N)"
  "wellFormedRule (env N) N (n_Idle2_ref N i)"
  "M \<le> N \<Longrightarrow> absTransfRule (env N) M (n_Idle2_ref N i) = (if i \<le> M then n_Idle i else n_Idle_abs2 M)"
  unfolding n_Idle2_ref_def
   apply (auto intro!: symParamRuleI symParamFormAnd symParamFormForallExcl)
  unfolding symParamForm_def symParamForm2_def symParamStatement_def apply auto[1]
   unfolding n_Idle_def n_Idle_abs2_def n_Idle2_ref_def by auto 


subsection \<open>Putting everything together ---definition of rules\<close>

definition n_Trys :: "nat \<Rightarrow> rule set" where
  "n_Trys N \<equiv> oneParamCons N n_Try"

definition n_Crits :: "nat \<Rightarrow> rule set" where
  "n_Crits N \<equiv> oneParamCons N n_Crit"

definition n_Exits :: "nat \<Rightarrow> rule set" where
  "n_Exits N \<equiv> oneParamCons N n_Exit"

definition n_Idles :: "nat \<Rightarrow> rule set" where
  "n_Idles N \<equiv> oneParamCons N n_Idle"

definition rules' :: "nat \<Rightarrow> rule set" where
  "rules' N \<equiv> n_Trys N \<union> n_Crits N \<union> n_Exits N \<union> n_Idles N"

lemma n_TrysIsSym:
  "symProtRules' N (n_Trys N)"
  using symTry(1) n_Trys_def symParaRuleInfSymRuleSet by auto

lemma n_CritsIsSym:
  "symProtRules' N (n_Crits N)"
  using n_Crits_def symCrit(1) symParaRuleInfSymRuleSet by auto 

lemma n_ExitsIsSym:
  "symProtRules' N (n_Exits N)"
  using n_Exits_def symExit(1) symParaRuleInfSymRuleSet by auto 

lemma n_IdlesIsSym:
  "symProtRules' N (n_Idles N)"
  using n_Idles_def symIdle(1) symParaRuleInfSymRuleSet by auto

lemma rulesSym':
  "symProtRules' N (rules' N)"
  unfolding rules'_def apply (intro symProtRulesUnion)
  using n_CritsIsSym n_ExitsIsSym n_IdlesIsSym n_TrysIsSym by auto

text \<open>strengthened rules with auxiliary invariants\<close>

definition pair1 :: "(nat \<Rightarrow> formula) \<times> (nat \<Rightarrow> formula)" where
  "pair1 \<equiv> (\<lambda>i. IVar (Para ''n'' i) =\<^sub>f Const E,
            \<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C \<and>\<^sub>f \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E)"

definition F :: "((nat \<Rightarrow> formula) \<times> (nat \<Rightarrow> formula)) set" where
  "F \<equiv> {pair1}"


definition n_Idle2s :: "nat \<Rightarrow> rule set" where
  "n_Idle2s N \<equiv> oneParamCons N (\<lambda>i. strengthenRule2 (constrInvByExcl pair1 i N) (n_Idle i))"


definition rules2' :: "nat \<Rightarrow> rule set" where
  "rules2' N \<equiv> n_Trys N \<union> n_Crits N \<union> n_Exits N \<union> n_Idle2s N"

lemma n_Idle2sIsSym:
  "symProtRules' N (n_Idle2s N)"
  unfolding n_Idle2s_def
  apply (rule symParaRuleInfSymRuleSet)
  using invAux1_def n_Idle2Eq symIdle2_ref(1) constrInvByExcl_def
  by (auto simp add: pair1_def)
 
lemma rule2'IsSym:
  "symProtRules' N (rules2' N)"
  unfolding rules2'_def
  apply (intro symProtRulesUnion)
  using n_CritsIsSym n_ExitsIsSym n_Idle2sIsSym n_TrysIsSym by auto 


text\<open>abstract rules\<close>

lemma absTrys:
  "M < N \<Longrightarrow> absTransfRule (env N) M ` (n_Trys N) = (n_Trys M) \<union> {chaos \<triangleright> skip}"
  unfolding n_Trys_def apply (rule absGen) using symTry(3) by auto

lemma absExits:
  "M < N \<Longrightarrow> absTransfRule (env N) M ` (n_Exits N) = (n_Exits M) \<union> {chaos \<triangleright> skip}"
  unfolding n_Exits_def apply (rule absGen) using symExit(3) by auto

lemma absCrits:
  "M < N \<Longrightarrow> absTransfRule (env N) M ` (n_Crits N) = (n_Crits M) \<union> {n_Crit_abs}"
  unfolding n_Crits_def apply (rule absGen) using symCrit(3) by auto

lemma n_Idle2_ref':
  "strengthenRule2 (constrInvByExcl pair1 i N) (n_Idle i) = n_Idle2_ref N i"
  unfolding n_Idle2_ref_def n_Idle_def constrInvByExcl_def pair1_def fst_conv snd_conv
  by (auto simp add: strengthenRule2.simps)

lemma absIdle2s:
  "M < N \<Longrightarrow> absTransfRule (env N) M ` (n_Idle2s N) = (n_Idles M) \<union> {n_Idle_abs2 M}"
  unfolding n_Idle2s_def n_Idles_def n_Idle2_ref'
  apply (rule absGen) using symIdle2_ref(3) by auto

definition absRules :: "nat \<Rightarrow> rule set" where
  "absRules M \<equiv> n_Trys M \<union> n_Exits M \<union> n_Crits M \<union> n_Idles M \<union>
    {chaos \<triangleright> skip, n_Crit_abs, n_Idle_abs2 M}"

lemma absAll:
  "M < N \<Longrightarrow> absTransfRule (env N) M ` rules2' N = absRules M"
  unfolding rules2'_def absRules_def image_Un absTrys absExits absCrits absIdle2s by auto

text \<open>type value information on variables occurring in aux(0,1)\<close>

definition type_inv :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv N s = (\<forall>i. i \<le> N \<longrightarrow> s (Para ''n'' i) = I \<or> s (Para ''n'' i) = T \<or> s (Para ''n'' i) = C \<or> s (Para ''n'' i) = E)"

thm strengthenRule2.simps
lemma invOnStateOfN' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: allInitSpecs_def type_inv_def initSpec0_def)
  subgoal for r sk
    unfolding rules2'_def apply auto
    subgoal unfolding n_Trys_def apply auto unfolding type_inv_def n_Try_def by auto
    subgoal unfolding n_Crits_def apply auto unfolding type_inv_def n_Crit_def by auto
    subgoal unfolding n_Exits_def apply auto unfolding type_inv_def n_Exit_def by auto
    subgoal unfolding n_Idle2s_def apply auto unfolding type_inv_def strengthenRule2.simps n_Idle_def by auto
    done
  done

lemma invOnStateOfN1 [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "fitEnv s (env N)"
proof(rule invIntro[OF _ _ assms])
  fix s0
  assume a0:" \<forall>f\<in>set (allInitSpecs N). formEval f s0 "
  show " fitEnv s0 (env N)"
  proof(unfold fitEnv_def,rule allI,rule impI)
    fix v
    assume a1:"env N v \<noteq> anyType"
    show "typeOf s0 v = env N v"
    proof(case_tac v)
      fix x1
      assume a2:"v = Ident x1"
      show "typeOf s0 v = env N v"
       by (cut_tac a0 a1 a2, auto simp add: allInitSpecs_def  
              initSpec0_def initSpec1_def)
    next
      fix x21 x22
      assume a2:"v = Para x21 x22"
      show "typeOf s0 v = env N v"
       by (cut_tac a0 a1 a2, auto simp add: allInitSpecs_def  
              initSpec0_def initSpec1_def)
    next
      assume a2:"v =dontCareVar"
      show "typeOf s0 v = env N v"
       by (cut_tac a0 a1 a2, auto simp add: allInitSpecs_def  
              initSpec0_def initSpec1_def)
   qed 
 qed   
next
  fix r sk
  assume a1:"r \<in> rules2' N" and a2:" formEval (pre r) sk" and
  a3:"fitEnv sk (env N)" 
  show "fitEnv (trans1 (act r) sk) (env N)"
    apply ( cut_tac a1 a2 a3,unfold rules2'_def, auto,unfold fitEnv_def)
    apply( unfold n_Trys_def, unfold  n_Try_def ,auto)
    apply( unfold n_Crits_def,    unfold n_Crit_def ,auto)
    apply( unfold n_Exits_def,    unfold n_Exit_def ,auto)
    by( unfold n_Idle2s_def strengthenRule2.simps n_Idle_def ,auto)
qed

lemma invOnStateOfN'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs = (set (allInitSpecs N)) \<longrightarrow> rs = rules2' N \<longrightarrow> i \<le> N \<longrightarrow> isEnumVal s (Para ''n'' i)"
  using invOnStateOfN' unfolding type_inv_def C_def E_def I_def T_def
  by (metis assms getValueType.simps(1) isEnumVal_def typeOf_def)

lemma deriveTry:
  assumes a:"r \<in> n_Trys N"
  shows "deriveRule (env N) r"
  using a by(unfold deriveRule_def deriveForm_def deriveStmt_def n_Trys_def n_Try_def,auto)

lemma deriveCrit:
  assumes a:"r \<in> n_Crits N"
  shows "deriveRule (env N) r"
  using a by(unfold deriveRule_def deriveForm_def deriveStmt_def n_Crits_def n_Crit_def,auto)

lemma deriveExit:
  assumes a:"r \<in> n_Exits N"
  shows "deriveRule (env N) r"
  using a by(unfold deriveRule_def deriveForm_def deriveStmt_def n_Exits_def n_Exit_def,auto)

lemma deriveIdle2:
  assumes a:"r \<in> n_Idle2s N"
  shows "deriveRule (env N) r"
  using a apply(unfold n_Idle2s_def deriveRule_def deriveForm_def deriveStmt_def deriveExp_def
          constrInvByExcl_def pair1_def n_Idle_def,auto simp add:strengthenRule2.simps)
  done

text \<open>Final result for nMutual
  a4 to be checked using model checker
\<close>
lemma absProtSim:
  assumes a2: "M < N"
    and a3: "M = 1"
    and a4: "\<forall>i f s.
       f \<in> F \<longrightarrow>
       reachableUpTo {f'. \<exists>f. f \<in> (set (allInitSpecs N)) \<and> f' = absTransfForm (env N) M f}
        (absRules M) i s \<longrightarrow>
       formEval (constrInv f 0 1) s"
  shows "\<forall>f s. f \<in> constrInvByExcls F N \<longrightarrow> 
    reachableUpTo (set (allInitSpecs N)) (rules' N) i s \<longrightarrow> formEval f s"
proof (rule_tac ?rs2.0="rules2' N" in CMP)
  show "\<And>r. r \<in> rules' N \<longrightarrow> wellFormedRule (env N) N r"
    apply (auto simp add: rules'_def n_Trys_def symTry(2) n_Crits_def symCrit(2)
                       n_Exits_def symExit(2) n_Idles_def symIdle(2))
    using symTry(2) apply auto[1]
    using symCrit(2) apply auto[1]
    using symExit(2) apply auto[1]
    using symIdle(2) by auto
next
  show "\<forall>f. f \<in> F \<longrightarrow> symPair f N"
    by (auto simp add: F_def pair1_def symParamForm_def)
next
  show "symProtRules' N (rules' N)"
    using rulesSym' by blast
next
  show "symPredSet' N (set (allInitSpecs N))"
    using symPreds' by blast
next
  show "M \<le> N"
    using a2 by arith
next
  show "\<forall>s i f. reachableUpTo (set (allInitSpecs N)) (rules2' N) i s \<longrightarrow>
        f \<in> F \<longrightarrow> (\<forall>v. v \<in> varOfForm (constrInv f 0 1) \<longrightarrow> s v = abs1 M s v)"
    using invOnStateOfN'' enumValAbsRemainSame
    unfolding F_def pair1_def using a2 a3 by auto
next
  show "\<forall>r'. r' \<in> rules2' N \<longrightarrow>
         (\<exists>r f i. f \<in> F \<and> r \<in> rules' N \<and> i \<le> N \<and> r' = strengthenRule2 (constrInvByExcl f i N) r) \<or>
         r' \<in> rules' N"
  proof -
    have "\<exists>r f i. f \<in> F \<and> r \<in> rules' N \<and> i \<le> N \<and> r' = strengthenRule2 (constrInvByExcl f i N) r"
      if "r' \<in> n_Idle2s N" for r'
      using that apply (auto simp add: n_Idle2s_def)
      subgoal for i
        apply (rule exI[where x="n_Idle i"])
        unfolding F_def pair1_def 
        by (auto simp add: constrInvByExcl_def strengthenRule2.simps n_Idle_def rules'_def n_Idles_def)
      done
    then show ?thesis
      apply (unfold rules2'_def rules'_def) by auto
  qed
next
  show "symProtRules' N (rules2' N)"
    using rule2'IsSym by blast 
next
  show "\<forall>r. r \<in> rules' N \<longrightarrow>
    (\<exists>f. f \<in> constrInvByExcls F N \<and> strengthenRule2 f r \<in> rules2' N) \<or> r \<in> rules2' N"
  proof -
    have "\<exists>f. f \<in> constrInvByExcls F N \<and> 
    strengthenRule2 f r \<in> n_Trys N \<union> n_Crits N \<union> n_Exits N \<union> n_Idle2s N"
      if "r \<in> n_Idles N" for r
      using that apply (auto simp add: n_Idles_def)
      subgoal for i
        apply (rule exI[where x="constrInvByExcl pair1 i N"])
        by (auto simp add: F_def pair1_def constrInvByExcl_def strengthenRule2.simps n_Idle2s_def)
      done
    then show ?thesis
      apply (unfold rules2'_def rules'_def) by auto
  qed
next 
  show "1 \<le> N"
    using a2 a3 by arith  
next 
  show "\<forall>i f s.
       f \<in> F \<longrightarrow>
       reachableUpTo {f'. \<exists>f. f \<in>set (allInitSpecs N) \<and> f' = absTransfForm (env N) M f}
        {r'. \<exists>r. r \<in> rules2' N \<and> r' = absTransfRule (env N) M r} i s \<longrightarrow>
       formEval (constrInv f 0 1) s"
  proof -
    have a: "{r'. \<exists>r. r \<in> rules2' N \<and> r' = absTransfRule  (env N)  M r} =
   absTransfRule  (env N)  M ` (rules2' N)"
      by auto
    show ?thesis
      unfolding a absAll[OF a2]
      using a2 a3 a4 absAll by auto
  qed
next
  fix r
  show "r \<in> rules2' N \<longrightarrow> deriveRule (env N) r"
    apply (unfold rules2'_def, auto simp  del:env_def)
    using deriveTry apply auto[1]
    using deriveCrit apply auto[1]
    using deriveExit apply auto[1]
    using deriveIdle2 by auto[1]
next
  fix f
  show "f \<in> set (allInitSpecs N) \<longrightarrow> deriveForm (env N) f"
   by(unfold allInitSpecs_def  
              initSpec0_def initSpec1_def deriveForm_def deriveExp_def,auto)

next
  show "\<forall>s i. reachableUpTo (set (allInitSpecs N)) (rules2' N) i s \<longrightarrow> fitEnv s (env N) "
    using invOnStateOfN1 by auto
    
qed

end
