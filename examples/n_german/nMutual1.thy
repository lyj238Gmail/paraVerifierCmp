theory nMutual1
  imports CMP
begin


subsection \<open>Definitions\<close>

text \<open>Represents the four states: idle, try, critical, exit\<close>

definition I :: scalrValueType where [simp]: "I \<equiv> enum ''control'' ''I''"
definition T :: scalrValueType where [simp]: "T \<equiv> enum ''control'' ''T''"
definition C :: scalrValueType where [simp]: "C \<equiv> enum ''control'' ''C''"
definition E :: scalrValueType where [simp]: "E \<equiv> enum ''control'' ''E''"

definition true :: scalrValueType where [simp]: "true \<equiv> boolV True"
definition false :: scalrValueType where [simp]: "false \<equiv> boolV False"

text \<open>Initial condition: all processes in idle.
  \<forall>i. n[i] = I
\<close>
definition initSpec0 :: "nat \<Rightarrow> formula" where
  "initSpec0 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''n'' i) =\<^sub>f Const I) N"

text \<open>Initial condition: x is True
  x = True
\<close>
definition initSpec1 :: formula where
  "initSpec1 \<equiv> IVar (Ident ''x'') =\<^sub>f Const true"

text \<open>There cannot be one state in exit and another in critical or exit.
  n[i] = E \<longrightarrow> (\<forall>j. i \<noteq> j \<longrightarrow> n[j] \<noteq> C \<and> n[j] \<noteq> E)
\<close>
definition invAux :: "nat \<Rightarrow> nat \<Rightarrow> formula" where
  "invAux N i \<equiv> IVar (Para ''n'' i) =\<^sub>f Const E \<longrightarrow>\<^sub>f forallFormExcl 
    (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C \<and>\<^sub>f \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N"  

text \<open>Try enter critical region
  n[i] = I \<rightarrow> n[i] := T
\<close>
definition n_Try :: "nat \<Rightarrow> rule" where
  "n_Try i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const I
   \<triangleright>
    assign (Para ''n'' i, Const T)"

text \<open>Enter critical region
  n[i] = T \<and> x = True \<rightarrow> n[i] := C; x := False
\<close>
definition n_Crit :: "nat \<Rightarrow> rule" where
  "n_Crit i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const T \<and>\<^sub>f
    IVar (Ident ''x'') =\<^sub>f Const true
   \<triangleright>
    assign (Para ''n'' i, Const C) ||
    assign (Ident ''x'', Const false)"

text \<open>Exit critical region
  n[i] = C \<rightarrow> n[i] := E
\<close>
definition n_Exit :: "nat \<Rightarrow> rule" where
  "n_Exit i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const C
   \<triangleright>
    assign (Para ''n'' i, Const E)"

text \<open>Move to idle
  n[i] = E \<rightarrow> n[i] := I; x := True
\<close>
definition n_Idle :: "nat \<Rightarrow> rule" where
  "n_Idle i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const E
   \<triangleright>
    assign (Para ''n'' i, Const I) ||
    assign (Ident ''x'', Const true)"

subsection \<open>References\<close>

definition n_Crit_abs :: rule where
  "n_Crit_abs \<equiv>
    IVar (Ident ''x'') =\<^sub>f Const (boolV True)
   \<triangleright>
    assign (Ident ''x'', Const (boolV False))"

definition n_Idle_abs1 :: rule where
  "n_Idle_abs1 \<equiv>
    chaos \<triangleright> assign (Ident ''x'', Const true)"

definition n_Idle_abs2 :: "nat \<Rightarrow> rule" where
"n_Idle_abs2 M \<equiv>
    (\<forall>\<^sub>fj. ((\<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const (enum ''control'' ''C''))\<and>\<^sub>f
      (\<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const (enum ''control'' ''E'')))) M 
   \<triangleright>
    assign (Ident ''x'', Const (boolV True))"


subsection \<open>Individual tests\<close>

lemma absInitSpec:
  assumes "M \<le> N"
  shows "absTransfForm M (initSpec0 N) = initSpec0 M"
        "absTransfForm M initSpec1 = initSpec1"
  unfolding initSpec0_def initSpec1_def using assms by auto

lemma symInvAux:
  "symParamForm N (invAux N)"
  unfolding invAux_def
  apply (auto intro!: symParamFormImply symParamFormAnd symParamFormForall symParamFormForallExcl)
  unfolding symParamForm_def symParamForm2_def equivForm_def by auto

lemma symTry:
  "symParamRule N n_Try"
  "wellFormedRule N (n_Try i)"
  "absTransfRule M (n_Try i) = (if i \<le> M then n_Try i else chaos \<triangleright> skip)"
  unfolding n_Try_def symParamRule_def by auto

lemma symCrit:
  "symParamRule N n_Crit"
  "wellFormedRule N (n_Crit i)"
  "absTransfRule M (n_Crit i) = (if i \<le> M then n_Crit i else n_Crit_abs)"
  unfolding n_Crit_def n_Crit_abs_def symParamRule_def by auto

lemma symExit:
  "symParamRule N n_Exit"
  "wellFormedRule N (n_Exit i)"
  "absTransfRule M (n_Exit i) = (if i \<le> M then n_Exit i else chaos \<triangleright> skip)"
  unfolding n_Exit_def symParamRule_def by auto

lemma symIdle:
  "symParamRule N n_Idle"
  "wellFormedRule N (n_Idle i)"
  "absTransfRule M (n_Idle i) = (if i \<le> M then n_Idle i else n_Idle_abs1)"
  unfolding n_Idle_def n_Idle_abs1_def symParamRule_def by auto

text \<open>Move to idle, strengthened:
  n[i] = E \<and>
  (\<forall>j. i \<noteq> j \<longrightarrow> n[j] \<noteq> C) \<and>
  (\<forall>j. i \<noteq> j \<longrightarrow> n[j] \<noteq> E) \<rightarrow> n[i] := I; x := True
\<close>
definition n_Idle2_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_Idle2_ref N i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const E \<and>\<^sub>f
    forallFormExcl (\<lambda>j.( \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C)  \<and>\<^sub>f
       \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N
   \<triangleright>
    assign (Para ''n'' i, Const I) ||
    assign (Ident ''x'', Const true)"
 
lemma n_Idle2Eq:
  "strengthenRule2 (invAux N i) (n_Idle i) = n_Idle2_ref N i"
  by (auto simp add: strengthenRule2.simps invAux_def n_Idle_def n_Idle2_ref_def)

lemma wellFormedIdle2:
  "symParamRule N (n_Idle2_ref N)"
  "wellFormedRule N (n_Idle2_ref N i)"
  unfolding n_Idle2_ref_def
   apply (auto intro!: symParamRuleI symParamFormAnd symParamFormForallExcl)
  unfolding symParamForm_def symParamForm2_def symParamStatement_def by auto

lemma absIdle2:
  "M \<le> N \<Longrightarrow> absTransfRule M (n_Idle2_ref N i) = (if i \<le> M then n_Idle i else n_Idle_abs2 M)"
  unfolding n_Idle_def n_Idle_abs2_def n_Idle2_ref_def by auto


subsection \<open>Putting everything together\<close>

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
  using invAux_def n_Idle2Eq wellFormedIdle2(1) constrInvByExcl_def
  by (auto simp add: pair1_def)
 
lemma rule2'IsSym:
  "symProtRules' N (rules2' N)"
  unfolding rules2'_def
  apply (intro symProtRulesUnion)
  using n_CritsIsSym n_ExitsIsSym n_Idle2sIsSym n_TrysIsSym by auto 

definition type_inv :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv N s = (\<forall>i. i \<le> N \<longrightarrow> s (Para ''n'' i) = I \<or> s (Para ''n'' i) = T \<or> s (Para ''n'' i) = C \<or> s (Para ''n'' i) = E)"

lemma invOnStateOfN' [simp,intro]:
  assumes "reachableUpTo ({initSpec0 N} \<union> {initSpec1}) (rules2' N) k s"
  shows "type_inv N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_def initSpec0_def)
  subgoal for r sk
    unfolding rules2'_def apply auto
    subgoal unfolding n_Trys_def apply auto unfolding type_inv_def n_Try_def by auto
    subgoal unfolding n_Crits_def apply auto unfolding type_inv_def n_Crit_def by auto
    subgoal unfolding n_Exits_def apply auto unfolding type_inv_def n_Exit_def by auto
    subgoal unfolding n_Idle2s_def apply auto unfolding type_inv_def strengthenRule2.simps n_Idle_def by auto
    done
  done

lemma invOnStateOfN'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs = {initSpec0 N} \<union> {initSpec1} \<longrightarrow> rs = rules2' N \<longrightarrow> i \<le> N \<longrightarrow> isEnumVal s (Para ''n'' i)"
  using invOnStateOfN' unfolding type_inv_def C_def E_def I_def T_def
  by (metis assms getValueType.simps(1) isEnumVal_def typeOf_def)

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

definition absTransfRuleSet :: "nat \<Rightarrow> rule set \<Rightarrow> rule set" where
  "absTransfRuleSet M rs = absTransfRule M ` rs"

lemma absGen:
  assumes "\<And>i. absTransfRule M (f i) = (if i \<le> M then g i else h)"
    and "M < N"
  shows "absTransfRule M ` (oneParamCons N f) = (oneParamCons M g) \<union> {h}"
  apply (auto simp add: assms image_def)
   apply (rule exI[where x="f (M + 1)"])
  apply (metis add_le_same_cancel1 assms(1) assms(2) discrete not_one_le_zero)
  subgoal for i apply (rule exI[where x="f i"])
    by (metis assms(1) assms(2) le_trans nat_le_linear not_le)
  done

lemma absTrys:
  "M < N \<Longrightarrow> absTransfRule M ` (n_Trys N) = (n_Trys M) \<union> {chaos \<triangleright> skip}"
  unfolding n_Trys_def apply (rule absGen) using symTry(3) by auto

lemma absExits:
  "M < N \<Longrightarrow> absTransfRule M ` (n_Exits N) = (n_Exits M) \<union> {chaos \<triangleright> skip}"
  unfolding n_Exits_def apply (rule absGen) using symExit(3) by auto

lemma absCrits:
  "M < N \<Longrightarrow> absTransfRule M ` (n_Crits N) = (n_Crits M) \<union> {n_Crit_abs}"
  unfolding n_Crits_def apply (rule absGen) using symCrit(3) by auto

lemma n_Idle2_ref':
  "strengthenRule2 (constrInvByExcl pair1 i N) (n_Idle i) = n_Idle2_ref N i"
  unfolding n_Idle2_ref_def n_Idle_def constrInvByExcl_def pair1_def fst_conv snd_conv
  by (auto simp add: strengthenRule2.simps)

lemma absIdle2s:
  "M < N \<Longrightarrow> absTransfRule M ` (n_Idle2s N) = (n_Idles M) \<union> {n_Idle_abs2 M}"
  unfolding n_Idle2s_def n_Idles_def n_Idle2_ref'
  apply (rule absGen) using absIdle2 by auto

definition absRules :: "nat \<Rightarrow> rule set" where
  "absRules M \<equiv> n_Trys M \<union> n_Exits M \<union> n_Crits M \<union> n_Idles M \<union>
    {chaos \<triangleright> skip, n_Crit_abs, n_Idle_abs2 M}"

lemma absAll:
  "M < N \<Longrightarrow> absTransfRule M ` rules2' N = absRules M"
  unfolding rules2'_def absRules_def image_Un absTrys absExits absCrits absIdle2s by auto

text \<open>Final result for nMutual
  a4 to be checked using model checker
\<close>
lemma absProtSim:
  assumes a2: "M < N"
    and a3: "M = 1"
    and a4: "\<forall>i f s.
       f \<in> F \<longrightarrow>
       reachableUpTo {f'. \<exists>f. f \<in> {initSpec0 N} \<union> {initSpec1} \<and> f' = absTransfForm M f}
        (absRules M) i s \<longrightarrow>
       formEval (constrInv f 0 1) s"
  shows "\<forall>f s. f \<in> constrInvByExcls F N \<longrightarrow> 
    reachableUpTo ({initSpec0 N} \<union> {initSpec1}) (rules' N) i s \<longrightarrow> formEval f s"
proof (rule_tac ?rs2.0="rules2' N" in CMP)
  show "\<And>r. r \<in> rules' N \<longrightarrow> wellFormedRule N r"
    by (auto simp add: rules'_def n_Trys_def symTry(2) n_Crits_def symCrit(2)
                       n_Exits_def symExit(2) n_Idles_def symIdle(2))
next
  show "\<forall>f. f \<in> F \<longrightarrow> symPair f N"
    by (auto simp add: F_def pair1_def symParamForm_def)
next
  show "symProtRules' N (rules' N)"
    using rulesSym' by blast
next
  show "symPredSet' N ({initSpec0 N} \<union> {initSpec1})"
    using symPreds by blast
next
  show "M \<le> N"
    using a2 by arith
next
  show "\<forall>s i f. reachableUpTo ({initSpec0 N} \<union> {initSpec1}) (rules2' N) i s \<longrightarrow>
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
        unfolding F_def pair1_def by (auto simp add: constrInvByExcl_def strengthenRule2.simps n_Idle_def rules'_def n_Idles_def)
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
    have "\<exists>f. f \<in> constrInvByExcls F N \<and> strengthenRule2 f r \<in> n_Trys N \<union> n_Crits N \<union> n_Exits N \<union> n_Idle2s N"
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
       reachableUpTo {f'. \<exists>f. f \<in> {initSpec0 N} \<union> {initSpec1} \<and> f' = absTransfForm M f}
        {r'. \<exists>r. r \<in> rules2' N \<and> r' = absTransfRule M r} i s \<longrightarrow>
       formEval (constrInv f 0 1) s"
  proof -
    have a: "{r'. \<exists>r. r \<in> rules2' N \<and> r' = absTransfRule M r} = absTransfRule M ` (rules2' N)"
      by auto
    show ?thesis
      unfolding a absAll[OF a2]
      using a2 a3 a4 absAll by auto
  qed
qed

end
