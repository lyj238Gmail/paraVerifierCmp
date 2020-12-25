theory Symmetric
  imports paraTheoryCmpzb
begin


subsection \<open>Rule set parameterized by processes\<close>

text \<open>We consider a special form of rule set, where there is a set associated
to each process i\<close>
definition rulesOverDownN :: "nat \<Rightarrow> (nat \<Rightarrow> rule set) \<Rightarrow> rule set" where
  "rulesOverDownN N f = {r. \<exists>n\<le>N. r \<in> f n}"


definition rulesOverDownN2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat\<Rightarrow>rule set) \<Rightarrow> rule set" where
  "rulesOverDownN2 N f = {r. \<exists>n1 n2. n1\<le>N \<and> n2\<le>N\<and> n1\<noteq>n2 \<and>  r \<in> f n1 n2}"

text \<open>There is a general theorem for showing symmetry\<close>
definition symmetricParamRules :: "nat \<Rightarrow> (nat \<Rightarrow> rule set) \<Rightarrow> bool" where
  "symmetricParamRules N f = (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> applySym2Rule p ` f i = f (p i))"

theorem symProtFromSymmetricParam:
  assumes "symmetricParamRules N f"
  shows "symProtRules N (rulesOverDownN N f)"
proof -
  have 1: "applySym2Rule p r \<in> f (p n)"
    if "p permutes {x. x \<le> N}" "n \<le> N" "r \<in> f n" for p r n
  proof -
    have "applySym2Rule p ` f n = f (p n)"
      using assms unfolding symmetricParamRules_def
      using that(1,2) by auto
    then show ?thesis
      using that(3) by auto
  qed
  show ?thesis
    unfolding symProtRules_def rulesOverDownN_def
    apply auto
    subgoal for p r n
      apply (rule exI[where x="p n"])
      apply auto
      using permutes_in_image apply fastforce
      using assms unfolding symmetricParamRules_def
      using 1 by auto
    done
qed

definition symmetricParamRules2 :: "nat \<Rightarrow> (nat \<Rightarrow>nat\<Rightarrow> rule set) \<Rightarrow> bool" where
  "symmetricParamRules2 N f = 
(\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow>j\<le>N
   \<longrightarrow>i\<noteq>j\<longrightarrow> applySym2Rule p ` (f i j) = f (p i) (p j))"


theorem symProtFromSymmetricParam2:
  assumes "symmetricParamRules2 N f"
  shows "symProtRules N (rulesOverDownN2 N f)"
proof -
  have 1: "applySym2Rule p r \<in> f (p n) (p m)"
    if "p permutes {x. x \<le> N}" "n \<le> N" "m \<le> N" "n\<noteq>m" "r \<in> f n m" for p r n m
  proof -
    have "applySym2Rule p ` (f n m)= f (p n) (p m)"
      using assms symmetricParamRules2_def that(1) that(2) that(3) that(4) by auto
      
  (*    using assms unfolding symmetricParamRules2_def
      using that(1,2) by auto*)
    then show ?thesis
      using that(5) by blast 
  qed
  show ?thesis
    unfolding symProtRules_def rulesOverDownN2_def
    apply auto
    subgoal for p r n m
      apply (rule exI[where x="p n "])
      apply(rule conjI)
      apply (metis mem_Collect_eq permutes_def)
      
      apply (rule exI[where x="p m "])
      apply auto
      using permutes_in_image apply fastforce
      apply (metis permutes_inv permutes_inv_inv permutes_inverses(1))
      using assms unfolding symmetricParamRules2_def
      using 1 by auto
    done
qed
subsection \<open>Formula set parameterized by two processes\<close>

text \<open>Likewise, we consider special cases of parameterized formulas.\<close>
definition symmetricParamFormulas2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "symmetricParamFormulas2 N f =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N
   \<longrightarrow> applySym2Form p (f i j) = f (p i) (p j))"

definition formulasOverDownN2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> (nat \<Rightarrow> formula list)" where
  "formulasOverDownN2 N f i = map (f i) (down N)"

lemma set_down: "set (down N) = {x. x \<le> N}"
  apply (induction N)
   apply auto[1] by fastforce

lemma symParamFormulas:
  assumes "symmetricParamFormulas2 N f"
    and "p permutes {x. x \<le> N}"
    and "i \<le> N"
  shows "set (map (applySym2Form p) (formulasOverDownN2 N f i)) = 
  set (formulasOverDownN2 N f (p i))"
proof -
  have a: "\<exists>x\<in>set (down N). applySym2Form p (f i j) = f (p i) x"
    if "j \<in> set (down N)" for j
  proof -
    have a1: "j \<le> N"
      using that set_down by auto 
    show ?thesis
      apply (rule bexI[where x="p j"])
      using assms a1 unfolding symmetricParamFormulas2_def
       apply simp
      using a1 assms(2)
      using permutes_in_image set_down by fastforce
  qed
  have b: "\<exists>x\<in>set (down N). f (p i) j = applySym2Form p (f i x)"
    if "j \<in> set (down N)" for j
  proof -
    have b1: "j \<le> N"
      using that set_down by auto
    have b2: "j = p (inv p j)"
      using assms(2) b1 permutes_inverses(1) by fastforce
    have b3: "inv p j \<le> N"
      using assms(2) b1
      by (metis b2 mem_Collect_eq permutes_def)
    show ?thesis
      apply (rule bexI[where x="inv p j"])
       apply (subst b2)
      using assms b3 unfolding symmetricParamFormulas2_def
      by (auto simp add: set_down)
  qed
  show ?thesis
    unfolding formulasOverDownN2_def
    apply (auto simp add: image_def)
    using a b by auto
qed


subsection \<open>Strengthening\<close>

text \<open>Next, consider the case of strengthening\<close>
definition strengthenProt :: "nat \<Rightarrow> (nat \<Rightarrow> rule set) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> (nat \<Rightarrow> rule set)" where
  "strengthenProt N rf invf i = (strengthenR1 (formulasOverDownN2 N invf i) []) ` (rf i)"


definition strengthenProt2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat\<Rightarrow>rule set) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> 
(nat \<Rightarrow> nat\<Rightarrow>rule set)" where
  "strengthenProt2 N rf invf i j= 
  (strengthenR1 (formulasOverDownN2 N invf i ) []) ` (rf i j)"

lemma applySym2FormList:
  "applySym2Form p (andList fs) = andList (map (applySym2Form p) fs)"
  apply (induction fs)
  by auto

definition alphaEqRuleSet :: "rule set \<Rightarrow> rule set \<Rightarrow> bool" where
  "alphaEqRuleSet rs1 rs2 \<longleftrightarrow>
    (\<forall>r1\<in>rs1. \<exists>r2\<in>rs2. alphaEqRule r1 r2) \<and>
    (\<forall>r2\<in>rs2. \<exists>r1\<in>rs1. alphaEqRule r1 r2)"

definition symmetricParamRules' :: "nat \<Rightarrow> (nat \<Rightarrow> rule set) \<Rightarrow> bool" where [simp]:
  "symmetricParamRules' N f = (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> 
i \<le> N \<longrightarrow> alphaEqRuleSet (applySym2Rule p ` f i) (f (p i)))"

lemma alphaEqStrengthenR1:
  assumes "applySym2Form p ` (set fs) = set fs2"
  shows "alphaEqRule (applySym2Rule p (strengthenR1 fs [] r)) (strengthenR1 fs2 [] (applySym2Rule p r))"
proof (cases r)
  case (guard cond act)
  have a: "and2ListF (applySym2Form p (andList fs)) = and2ListF (andList fs2)"
    unfolding applySym2FormList
    sorry
  show ?thesis
    unfolding guard apply simp
    using a by auto
qed

lemma alphaEqStrengthenR1Set:
  assumes "applySym2Form p ` (set fs) = set fs2"
  shows "alphaEqRuleSet (applySym2Rule p ` strengthenR1 fs [] ` rs) (strengthenR1 fs2 [] ` applySym2Rule p ` rs)"
proof -
  have a: "\<exists>r2\<in>(strengthenR1 fs2 [] ` applySym2Rule p ` rs). (alphaEqRule r1 r2)"
    if r1: "r1\<in>applySym2Rule p ` strengthenR1 fs [] ` rs" for r1
  proof -
    obtain r1' where r1': "r1' \<in> rs" "r1 = applySym2Rule p (strengthenR1 fs [] r1')"
      using r1 by blast
    show ?thesis
      apply (rule bexI[where x="strengthenR1 fs2 [] (applySym2Rule p r1')"])
      unfolding r1'(2)
       apply (rule alphaEqStrengthenR1[OF assms])
      using r1' by auto
  qed
  have b: "\<exists>r1\<in>applySym2Rule p ` strengthenR1 fs [] ` rs. alphaEqRule r1 r2"
    if r2: "r2\<in>strengthenR1 fs2 [] ` applySym2Rule p ` rs" for r2
  proof -
    obtain r2' where r2': "r2' \<in> rs" "r2 = strengthenR1 fs2 [] (applySym2Rule p r2')"
      using r2 by blast
    show ?thesis
      apply (rule bexI[where x="applySym2Rule p (strengthenR1 fs [] r2')"])
      unfolding r2'(2)
      apply (rule alphaEqStrengthenR1[OF assms])
      using r2' by auto
  qed
  show ?thesis
    unfolding alphaEqRuleSet_def
    using a b by auto
qed

theorem strengthenProtSymmetric:
  assumes "symmetricParamRules N rf"
    and "symmetricParamFormulas2 N invf"
  shows "symmetricParamRules' N (\<lambda>i. strengthenProt N rf invf i)"
proof -
  have a: "alphaEqRuleSet (applySym2Rule p ` strengthenProt N rf invf i)
   (strengthenProt N rf invf (p i))"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i
  proof -
    from assms(1)[unfolded symmetricParamRules_def]
    have a1: "applySym2Rule p ` rf i = rf (p i)"
      using that by auto
    show ?thesis
      unfolding strengthenProt_def a1[symmetric]
      apply (rule alphaEqStrengthenR1Set)
      apply (subst image_set)
      by (rule symParamFormulas[OF assms(2) that])
  qed
  show ?thesis
    unfolding symmetricParamRules'_def
    using a by auto
qed

theorem symProtFromSymmetricParam':
  assumes "symmetricParamRules' N f"
  shows "symProtRules' N (rulesOverDownN N f)"
proof -
  have a: "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOverDownN N f"
    if aa: "p permutes {x. x \<le> N}" "r \<in> rulesOverDownN N f" for p r
  proof -
    obtain i where i: "i \<le> N" "r \<in> f i"
      using aa(2) unfolding rulesOverDownN_def by auto 
    from assms[unfolded symmetricParamRules'_def]
    have a1: "alphaEqRuleSet (applySym2Rule p ` f i) (f (p i))"
      using aa(1) i(1) by auto
    have a2: "applySym2Rule p r \<in> applySym2Rule p ` f i"
      using i(2) by auto
    obtain r' where r': "r' \<in> f (p i)" "alphaEqRule (applySym2Rule p r) r'"
      using a1 a2 unfolding alphaEqRuleSet_def by auto
    have a3: "p i \<le> N"
      using i(1) aa(1)
      by (metis (full_types) mem_Collect_eq permutes_def)
    show ?thesis
      apply (rule exI[where x=r'])
      using r' a3 by (auto simp add: rulesOverDownN_def)
  qed
  show ?thesis
    unfolding symProtRules'_def
    using a by auto
qed

end
