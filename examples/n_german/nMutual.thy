theory nMutual
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
  "invAux N i \<equiv> IVar (Para ''n'' i) =\<^sub>f Const E \<longrightarrow>\<^sub>f
                forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C) i N \<and>\<^sub>f
                forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N"

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
    (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const (enum ''control'' ''C'')) M \<and>\<^sub>f
    (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const (enum ''control'' ''E'')) M
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

lemma Try:
  "symParamRule N n_Try"
  "wellFormedStatement N (act (n_Try i))"
  "absTransfRule M (n_Try i) = (if i \<le> M then n_Try i else chaos \<triangleright> skip)"
  unfolding n_Try_def symParamRule_def by auto

lemma symCrit:
  "symParamRule N n_Crit"
  "wellFormedStatement N (act (n_Crit i))"
  "absTransfRule M (n_Crit i) = (if i \<le> M then n_Crit i else n_Crit_abs)"
  unfolding n_Crit_def n_Crit_abs_def symParamRule_def by auto

lemma symExit:
  "symParamRule N n_Exit"
  "wellFormedStatement N (act (n_Exit i))"
  "absTransfRule M (n_Exit i) = (if i \<le> M then n_Exit i else chaos \<triangleright> skip)"
  unfolding n_Exit_def symParamRule_def by auto

lemma symIdle:
  "symParamRule N n_Idle"
  "wellFormedStatement N (act (n_Idle i))"
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
    forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C) i N \<and>\<^sub>f
    forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N
   \<triangleright>
    assign (Para ''n'' i, Const I) ||
    assign (Ident ''x'', Const true)"

lemma n_Idle2Eq:
  "strengthenRule2 (invAux N i) (n_Idle i) = n_Idle2_ref N i"
  by (auto simp add: invAux_def n_Idle_def n_Idle2_ref_def)

lemma wellFormedIdle2:
  "symParamRule N (n_Idle2_ref N)"
  "wellFormedStatement N (act (n_Idle2_ref N i))"
  unfolding n_Idle2_ref_def
   apply (auto intro!: symParamRuleI symParamFormAnd symParamFormForallExcl)
  unfolding symParamForm_def symParamForm2_def symParamStatement_def by auto

lemma absIdle2:
  "M \<le> N \<Longrightarrow> absTransfRule M (n_Idle2_ref N i) = (if i \<le> M then n_Idle i else n_Idle_abs2 M)"
  unfolding n_Idle_def n_Idle_abs2_def n_Idle2_ref_def by auto

end
