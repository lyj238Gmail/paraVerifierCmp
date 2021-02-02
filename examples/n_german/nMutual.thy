theory nMutual
  imports CMP
begin


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

definition allInitSpecs :: "nat \<Rightarrow> formula list" where
  "allInitSpecs N \<equiv> [initSpec0 N, initSpec1]"


text \<open>There cannot be one state in exit and another in critical or exit.
  n[i] = E \<longrightarrow> (\<forall>j. i \<noteq> j \<longrightarrow> n[j] \<noteq> C \<and> n[j] \<noteq> E)
\<close>
definition invAux :: "nat \<Rightarrow> nat \<Rightarrow> formula" where
  "invAux N i \<equiv> IVar (Para ''n'' i) =\<^sub>f Const E \<longrightarrow>\<^sub>f
                forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C) i N \<and>\<^sub>f
                forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N"

lemma symInvAux:
  "symParamForm N (invAux N)"
  unfolding invAux_def
  apply (auto intro!: symParamFormImply symParamFormForall)
  unfolding symParamForm_def symParamForm2_def equivForm_def sorry


text \<open>Try enter critical region
  n[i] = I \<rightarrow> n[i] := T
\<close>
definition n_Try :: "nat \<Rightarrow> rule" where
  "n_Try i \<equiv>
    let g = IVar (Para ''n'' i) =\<^sub>f Const I in
    let s = assign (Para ''n'' i, Const T) in
      guard g s"

text \<open>Enter critical region
  n[i] = T \<and> x = True \<rightarrow> n[i] := C; x := False
\<close>
definition n_Crit :: "nat \<Rightarrow> rule" where
  "n_Crit i \<equiv>
    let g = IVar (Para ''n'' i) =\<^sub>f Const T \<and>\<^sub>f
            IVar (Ident ''x'') =\<^sub>f Const true in
    let s = parallel (assign (Para ''n'' i, Const C))
                     (assign (Ident ''x'', Const false)) in
      guard g s"

text \<open>Exit critical region
  n[i] = C \<rightarrow> n[i] := E
\<close>
definition n_Exit :: "nat \<Rightarrow> rule" where
  "n_Exit i \<equiv>
    let g = IVar (Para ''n'' i) =\<^sub>f Const C in
    let s = (assign (Para ''n'' i, Const E)) in
      guard g s"

text \<open>Move to idle
  n[i] = E \<rightarrow> n[i] := I; x := True
\<close>
definition n_Idle :: "nat \<Rightarrow> rule" where
  "n_Idle i \<equiv>
    let g = IVar (Para ''n'' i) =\<^sub>f Const E in
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

lemma absTry:
  "absTransfForm M (pre (n_Try i)) =
    (if i > M then dontCareForm
     else IVar (Para ''n'' i) =\<^sub>f Const I)"
  by (auto simp add: n_Try_def)

lemma absCrit:
  "absTransfForm M (pre (n_Crit i)) =
    (if i > M then IVar (Ident ''x'') =\<^sub>f Const (boolV True)
     else IVar (Para ''n'' i) =\<^sub>f Const T \<and>\<^sub>f IVar (Ident ''x'') =\<^sub>f Const true)"
  by (auto simp add: n_Crit_def)

lemma absExit:
  "absTransfForm M (pre (n_Exit i)) =
    (if i > M then dontCareForm
     else IVar (Para ''n'' i) =\<^sub>f Const C)"
  by (auto simp add: n_Exit_def)

lemma absIdle:
  "absTransfForm M (pre (n_Idle i)) =
    (if i > M then dontCareForm
     else IVar (Para ''n'' i) =\<^sub>f Const E)"
  by (auto simp add: n_Idle_def)

definition n_Idle_st :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_Idle_st N i = strengthenRule2 (invAux N i) (n_Idle i)"

lemma symIdle2:
  "symParamRule N (n_Idle_st N)" 
  unfolding n_Idle_st_def
  by (auto intro!: symParamStrengthenRule2 symIdle symInvAux)

text \<open>Move to idle, strengthened:
  n[i] = E \<and>
  (\<forall>j. i \<noteq> j \<longrightarrow> n[j] \<noteq> C) \<and>
  (\<forall>j. i \<noteq> j \<longrightarrow> n[j] \<noteq> E) \<rightarrow> n[i] := I; x := True
\<close>
definition n_Idle_st_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_Idle_st_ref N i \<equiv>
    let g = IVar (Para ''n'' i) =\<^sub>f Const E \<and>\<^sub>f
            forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C) i N \<and>\<^sub>f
            forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N in
    let a = (parallel (assign (Para ''n'' i, Const I))
                      (assign (Ident ''x'', Const true))) in
      guard g a"

lemma n_Idle_stEq:
  "n_Idle_st N i = n_Idle_st_ref N i"
  by (auto simp add: invAux_def n_Idle_def n_Idle_st_def n_Idle_st_ref_def)

lemma absIdle2:
  "absTransfForm M (pre (n_Idle_st_ref N i)) =
    (if i \<le> M then (IVar (Para ''n'' i) =\<^sub>f Const E)
     else (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C) M \<and>\<^sub>f
          (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) M)"
  by (auto simp add: n_Idle_st_ref_def)

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
