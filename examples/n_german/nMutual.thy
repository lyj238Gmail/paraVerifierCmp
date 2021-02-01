theory nMutual
  imports CMP
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
definition initSpec0 :: "nat \<Rightarrow> formula" where
  "initSpec0 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''n'' i) =\<^sub>f Const I) N"

text \<open>Initial condition: x is True
  x = True
\<close>
definition initSpec1 :: formula where
  "initSpec1 \<equiv> IVar (Ident ''x'') =\<^sub>f Const true"

definition allInitSpecs :: "nat \<Rightarrow> formula list" where
  "allInitSpecs N \<equiv> [initSpec0 N, initSpec1]"


text \<open>There cannot be one state in exit and another in critical.
  n[i] = E \<longrightarrow> (\<forall>j. j \<noteq> i \<longrightarrow> n[j] \<noteq> C)
\<close>
definition inv_5 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where
  "inv_5 N i \<equiv> IVar (Para ''n'' i) =\<^sub>f Const E \<longrightarrow>\<^sub>f
               (\<forall>\<^sub>fj. \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<longrightarrow>\<^sub>f \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C) N"

text \<open>No two processes can be in the exit state in the same time.
  n[i] = E \<longrightarrow> (\<forall>j. j \<noteq> i \<longrightarrow> n[j] \<noteq> E)
\<close>
definition inv_7 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where
  "inv_7 N i \<equiv> IVar (Para ''n'' i) =\<^sub>f Const E \<longrightarrow>\<^sub>f
               (\<forall>\<^sub>fj. \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<longrightarrow>\<^sub>f \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) N"

lemma symInv5:
  "symParamForm N (inv_5 N)"
  unfolding inv_5_def
  apply (auto intro!: symParamFormImply symParamFormForall)
  unfolding symParamForm_def symParamForm2_def equivForm_def by auto

lemma symInv7:
  "symParamForm N (inv_7 N)"
  unfolding inv_7_def
  apply (auto intro!: symParamFormImply symParamFormForall)
  unfolding symParamForm_def symParamForm2_def equivForm_def by auto


text \<open>Try enter critical region
  n[i] = I \<rightarrow> n[i] := T
\<close>
definition n_Try :: "nat \<Rightarrow> rule" where
  "n_Try i \<equiv>
    let g = eqn (IVar (Para ''n'' i)) (Const I) in
    let s = assign (Para ''n'' i, Const T) in
      guard g s"

text \<open>Enter critical region
  n[i] = T \<and> x = True \<rightarrow> n[i] := C; x := False
\<close>
definition n_Crit :: "nat \<Rightarrow> rule" where
  "n_Crit i \<equiv>
    let g = andForm (eqn (IVar (Para ''n'' i)) (Const T))
                    (eqn (IVar (Ident ''x'')) (Const true)) in
    let s = parallel (assign (Para ''n'' i, Const C))
                     (assign (Ident ''x'', Const false)) in
      guard g s"

text \<open>Exit critical region
  n[i] = C \<rightarrow> n[i] := E
\<close>
definition n_Exit :: "nat \<Rightarrow> rule" where
  "n_Exit i \<equiv>
    let g = eqn (IVar (Para ''n'' i)) (Const C) in
    let s = (assign (Para ''n'' i, Const E)) in
      guard g s"

text \<open>Move to idle
  n[i] = E \<rightarrow> n[i] := I; x := True
\<close>
definition n_Idle :: "nat \<Rightarrow> rule" where
  "n_Idle i \<equiv>
    let g = eqn (IVar (Para ''n'' i)) (Const E) in
    let s = (parallel (assign (Para ''n'' i, Const I))
                      (assign (Ident ''x'', Const true))) in
      guard g s"

lemma symTry:
  "symParamRule N n_Try"
  unfolding n_Try_def symParamRule_def by auto

lemma symCrit:
  "symParamRule N n_Crit"
  unfolding n_Crit_def symParamRule_def by auto

lemma symExit:
  "symParamRule N n_Exit"
  unfolding n_Exit_def symParamRule_def by auto

lemma symIdle:
  "symParamRule N n_Idle"
  unfolding n_Idle_def symParamRule_def by auto


fun removeImplies1 :: "formula \<Rightarrow> formula \<Rightarrow> formula" where
  "removeImplies1 (implyForm f1 f2) g = (if equivForm f1 g then f2 else implyForm f1 f2)"
| "removeImplies1 invf g = invf"

fun removeImplies :: "formula \<Rightarrow> formula \<Rightarrow> formula" where
  "removeImplies invf (andForm g1 g2) = removeImplies (removeImplies1 invf g1) g2"
| "removeImplies invf g = removeImplies1 invf g"

fun strengthenForm2 :: "formula \<Rightarrow> formula \<Rightarrow> formula" where
  "strengthenForm2 invf g = andForm g (removeImplies invf g)"

fun strengthenRule2 :: "formula \<Rightarrow> rule \<Rightarrow> rule" where
  "strengthenRule2 invf (guard g a) = guard (strengthenForm2 invf g) a"


text \<open>Equivalence between strengthenRule and strengthenRule2\<close>

lemma removeImplies1Equiv [simp]:
  "formEval g s \<Longrightarrow> formEval (removeImplies1 invf g) s  \<longleftrightarrow> formEval invf s"
  apply (cases invf) by (auto simp add: equivForm_def)

lemma removeImpliesEquiv:
  "((e::expType) = e) \<and> (\<forall>invf. formEval g s \<longrightarrow> formEval (removeImplies invf g) s \<longleftrightarrow> formEval invf s)"
  apply (induct rule: expType_formula.induct) by auto

lemma strengthenForm2Equiv:
  "equivForm (strengthenForm2 invf g) (strengthenForm invf g)"
  using removeImpliesEquiv by (auto simp add: equivForm_def)

lemma strengthenRule2Equiv:
  "equivRule (strengthenRule2 invf r) (strengthenRule invf r)"
  apply (cases r) using strengthenForm2Equiv by auto

lemma equivApply2SymForm:
  assumes "p permutes {x. x \<le> N}"
    and "equivForm f1 f2"
  shows "equivForm (applySym2Form p f1) (applySym2Form p f2)"
proof -
  have "formEval (applySym2Form p f1) s \<longleftrightarrow> formEval (applySym2Form p f2) s" for s
    unfolding stFormSymCorrespondence3(2)[OF assms(1), symmetric]
    using assms(2) unfolding equivForm_def by auto
  then show ?thesis
    unfolding equivForm_def by auto
qed

lemma equivApply2SymRule:
  assumes "p permutes {x. x \<le> N}"
    and "equivRule r1 r2"
  shows "equivRule (applySym2Rule p r1) (applySym2Rule p r2)"
proof -
  show ?thesis
    apply (cases r1) subgoal for g1 a1
      apply (cases r2) subgoal for g2 a2
        using assms(2) equivApply2SymForm assms by auto
      done
    done
qed

lemma symParamStrengthenRule2:
  assumes "symParamRule N r"
    and "symParamForm N f"
  shows "symParamRule N (\<lambda>i. strengthenRule2 (f i) (r i))"
proof -
  have a: "symParamRule N (\<lambda>i. strengthenRule (f i) (r i))"
    using symParamStrengthenRule[OF assms] by auto
  have b: "equivRule (applySym2Rule p (strengthenRule2 (f i) (r i))) (strengthenRule2 (f (p i)) (r (p i)))"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i 
  proof -
    have 1: "equivRule (applySym2Rule p (strengthenRule2 (f i) (r i))) (applySym2Rule p (strengthenRule (f i) (r i)))"
      apply (rule equivApply2SymRule[OF that(1)])
      using strengthenRule2Equiv by auto
    have 2: "equivRule (applySym2Rule p (strengthenRule (f i) (r i))) (strengthenRule (f (p i)) (r (p i)))"
      using a that unfolding symParamRule_def by auto
    have 3: "equivRule (strengthenRule (f (p i)) (r (p i))) (strengthenRule2 (f (p i)) (r (p i)))"
      apply (subst equivRuleSym)
      using strengthenRule2Equiv by auto
    show ?thesis
      using 1 2 3 equivRuleTrans by blast
  qed
  show ?thesis
    unfolding symParamRule_def using b by auto
qed

definition n_Idle2 :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_Idle2 N i = fold strengthenRule2 [inv_5 N i, inv_7 N i] (n_Idle i)"

lemma symIdle2:
  "symParamRule N (n_Idle2 N)" 
  unfolding n_Idle2_def
  by (auto intro!: symParamStrengthenRule2 symIdle symInv5 symInv7)

text \<open>Move to idle, strengthened:
  n[i] = E \<and>
  (\<forall>j. j \<noteq> i \<longrightarrow> n[j] \<noteq> C) \<and>
  (\<forall>j. j \<noteq> i \<longrightarrow> n[j] \<noteq> E) \<rightarrow> n[i] := I; x := True
\<close>
definition n_Idle2_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_Idle2_ref N i \<equiv>
    let g = andForm (andForm (eqn (IVar (Para ''n'' i)) (Const E))
                    (forallForm (\<lambda>j. implyForm (neg (eqn (Const (index i)) (Const (index j))))
                                     (neg (eqn (IVar (Para ''n'' j)) (Const C)))) N))
                    (forallForm (\<lambda>j. implyForm (neg (eqn (Const (index i)) (Const (index j)))) 
                                     (neg (eqn (IVar (Para ''n'' j)) (Const E)))) N) in
    let s = (parallel (assign (Para ''n'' i, Const I))
                      (assign (Ident ''x'', Const true))) in
      guard g s"

lemma n_Idle2Eq:
  "n_Idle2 N i = n_Idle2_ref N i"
  by (auto simp add: inv_5_def inv_7_def n_Idle_def n_Idle2_def n_Idle2_ref_def)



(*
definition rules_i :: "nat \<Rightarrow> nat \<Rightarrow> rule set" where
  "rules_i i j = {n_Try2 i j, n_Crit2 i j, n_Exit2 i j, n_Idle2 i j}"

lemma rule_i_symmetric:
  "symParamRules2 N rules_i"
  unfolding rules_i_def
  apply (auto intro!: symParamRules2Insert symParamRules2Empty)
  unfolding n_Try2_def n_Crit2_def n_Exit2_def n_Idle2_def symParamRule2_def by auto

definition rules_i_st :: "nat \<Rightarrow> nat \<Rightarrow> rule set" where
  "rules_i_st i j = {n_Try2 i j, n_Crit2 i j, n_Exit2 i j,
                     fold strengthenRule [inv_5 i j, inv_7 i j] (n_Idle2 i j)}"

lemma rule_i_st_symmetric:
  "symParamRules2 N rules_i_st"
  unfolding rules_i_st_def
  apply (auto intro!: symParamRules2Insert symParamRules2Empty)
*)

end
