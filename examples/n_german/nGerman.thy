theory nGerman
  imports CMP
begin

text \<open>Represents the three states: idle, shared, exclusive\<close>

definition I :: scalrValueType where [simp]: "I \<equiv> enum ''control'' ''I''"
definition S :: scalrValueType where [simp]: "S \<equiv> enum ''control'' ''S''"
definition E :: scalrValueType where [simp]: "E \<equiv> enum ''control'' ''E''"

text \<open>Control states\<close>

definition Empty :: scalrValueType where [simp]: "Empty \<equiv> enum ''control'' ''Empty''"
definition ReqS :: scalrValueType where [simp]: "ReqS \<equiv> enum ''control'' ''ReqS''"
definition ReqE :: scalrValueType where [simp]: "ReqE \<equiv> enum ''control'' ''ReqE''"
definition Inv :: scalrValueType where [simp]: "Inv \<equiv> enum ''control'' ''Inv''"
definition InvAck :: scalrValueType where [simp]: "InvAck \<equiv> enum ''control'' ''InvAck''"
definition GntS :: scalrValueType where [simp]: "GntS \<equiv> enum ''control'' ''GntS''"
definition GntE ::scalrValueType where [simp]: "GntE \<equiv> enum ''control'' ''GntE''"

definition true :: scalrValueType where [simp]: "true \<equiv> boolV True"
definition false :: scalrValueType where [simp]: "false \<equiv> boolV False"

definition n_RecvGntE :: "nat \<Rightarrow> rule" where
  "n_RecvGntE i \<equiv>
    IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const GntE
   \<triangleright>
    assign (Para ''Cache.State'' i, Const E) ||
    assign (Para ''Chan2.Cmd'' i, Const Empty)"

lemma RecvGntE:
  "symParamRule N n_RecvGntE"
  "wellFormedStatement N (act (n_RecvGntE i))"
  "absTransfRule M (n_RecvGntE i) = (if i \<le> M then n_RecvGntE i else chaos \<triangleright> skip)"
  unfolding n_RecvGntE_def symParamRule_def by auto

definition n_RecvGntS :: "nat \<Rightarrow> rule" where
  "n_RecvGntS i \<equiv>
    IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const GntS
   \<triangleright>
    assign (Para ''Cache.State'' i, Const S) ||
    assign (Para ''Chan2.Cmd'' i, Const Empty)"

lemma RecvGntS:
  "symParamRule N n_RecvGntS"
  "wellFormedStatement N (act (n_RecvGntS i))"
  "absTransfRule M (n_RecvGntS i) = (if i \<le> M then n_RecvGntS i else chaos \<triangleright> skip)"
  unfolding n_RecvGntS_def symParamRule_def by auto

definition n_SendGntE :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_SendGntE N i \<equiv>
    IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE \<and>\<^sub>f
    IVar (Ident ''CurPtr'') =\<^sub>f Const (index i) \<and>\<^sub>f
    IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
    IVar (Ident ''ExGntd'') =\<^sub>f Const false \<and>\<^sub>f
    (\<forall>\<^sub>fj. IVar (Para ''ShrSet'' j) =\<^sub>f Const false) N
   \<triangleright>
    assign (Para ''Chan2.Cmd'' i, Const GntE) ||
    assign (Para ''ShrSet'' i, Const true) ||
    assign (Ident ''ExGntd'', Const true) ||
    assign (Ident ''CurCmd'', Const Empty)"

definition n_SendGntE_abs :: "nat \<Rightarrow> rule" where
  "n_SendGntE_abs M \<equiv>
    IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE \<and>\<^sub>f
    IVar (Ident ''CurPtr'') =\<^sub>f Const (index (M+1)) \<and>\<^sub>f
    IVar (Ident ''ExGntd'') =\<^sub>f Const false \<and>\<^sub>f
    (\<forall>\<^sub>fj. IVar (Para ''ShrSet'' j) =\<^sub>f Const false) M
   \<triangleright>
    assign (Ident ''ExGntd'', Const true) ||
    assign (Ident ''CurCmd'', Const Empty)"

lemma wellFormedSendGntE:
  "symParamRule N (n_SendGntE N)"
  "wellFormedStatement N (act (n_SendGntE N i))"
  unfolding n_SendGntE_def
  apply (auto intro!: symParamRuleI symParamFormAnd symParamFormForall)
  unfolding symParamForm_def symParamForm2_def symParamStatement_def by auto

lemma absSendGntE:
  "M \<le> N \<Longrightarrow> absTransfRule M (n_SendGntE N i) =
     (if i \<le> M then n_SendGntE M i else n_SendGntE_abs M)"
  unfolding n_SendGntE_def n_SendGntE_abs_def by auto

definition n_SendGntS :: "nat \<Rightarrow> rule" where
  "n_SendGntS i \<equiv>
    IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
    IVar (Ident ''CurPtr'') =\<^sub>f Const (index i) \<and>\<^sub>f
    IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
    IVar (Ident ''ExGntd'') =\<^sub>f Const false
   \<triangleright>
    assign (Para ''Chan2.Cmd'' i, Const GntS) ||
    assign (Para ''ShrSet'' i, Const true) ||
    assign (Ident ''CurCmd'', Const Empty)"

definition n_SendGntS_abs :: "nat \<Rightarrow> rule" where
  "n_SendGntS_abs M \<equiv>
    IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
    IVar (Ident ''CurPtr'') =\<^sub>f Const (index (M+1)) \<and>\<^sub>f
    IVar (Ident ''ExGntd'') =\<^sub>f Const false
   \<triangleright>
    assign (Ident ''CurCmd'', Const Empty)"

lemma wellFormedSendGntS:
  "symParamRule N n_SendGntS"
  "wellFormedStatement N (act (n_SendGntS i))"
  unfolding n_SendGntS_def
  by (auto intro!: symParamRuleI simp add: symParamForm_def symParamStatement_def)

lemma absSendGntS:
  "M \<le> N \<Longrightarrow> absTransfRule M (n_SendGntS i) =
    (if i \<le> M then n_SendGntS i else n_SendGntS_abs M)"
  unfolding n_SendGntS_def n_SendGntS_abs_def by auto

definition n_RecvInvAck1 :: "nat \<Rightarrow> rule" where
  "n_RecvInvAck1 i \<equiv>
    IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
    \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
    IVar (Ident ''ExGntd'') =\<^sub>f Const true
   \<triangleright>
    assign (Para ''Chan3.Cmd'' i, Const Empty) ||
    assign (Para ''ShrSet'' i, Const false) ||
    assign (Ident ''ExGntd'', Const false)"

definition n_RecvInvAck1_abs :: rule where
  "n_RecvInvAck1_abs \<equiv>
    \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
    IVar (Ident ''ExGntd'') =\<^sub>f Const true
   \<triangleright>
    assign (Ident ''ExGntd'', Const false)"

lemma RecvInvAck1:
  "symParamRule N n_RecvInvAck1"
  "wellFormedStatement N (act (n_RecvInvAck1 i))"
  "absTransfRule M (n_RecvInvAck1 i) = (if i \<le> M then n_RecvInvAck1 i else n_RecvInvAck1_abs)"
  unfolding n_RecvInvAck1_def n_RecvInvAck1_abs_def symParamRule_def by auto

definition n_RecvInvAck2 :: "nat \<Rightarrow> rule" where
  "n_RecvInvAck2 i \<equiv>
    IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
    \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
    \<not>\<^sub>f IVar (Ident ''ExGntd'') =\<^sub>f Const true
   \<triangleright>
    assign (Para ''Chan3.Cmd'' i, Const Empty) ||
    assign (Para ''ShrSet'' i, Const false)"

definition n_RecvInvAck2_abs :: rule where
  "n_RecvInvAck2_abs \<equiv>
    \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
    \<not>\<^sub>f IVar (Ident ''ExGntd'') =\<^sub>f Const true
   \<triangleright>
    skip"

lemma RecvInvAck2:
  "symParamRule N n_RecvInvAck2"
  "wellFormedStatement N (act (n_RecvInvAck2 i))"
  "absTransfRule M (n_RecvInvAck2 i) = (if i \<le> M then n_RecvInvAck2 i else n_RecvInvAck2_abs)"
  unfolding n_RecvInvAck2_def n_RecvInvAck2_abs_def symParamRule_def by auto

definition n_SendInvAck1 :: "nat \<Rightarrow> rule" where
  "n_SendInvAck1 i \<equiv>
    IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Inv \<and>\<^sub>f
    IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
    IVar (Para ''Cache.State'' i) =\<^sub>f Const E
   \<triangleright>
    assign (Para ''Chan2.Cmd'' i, Const Empty) ||
    assign (Para ''Chan3.Cmd'' i, Const InvAck) ||
    assign (Para ''Cache.State'' i, Const I)"

lemma SendInvAck1:
  "symParamRule N n_SendInvAck1"
  "wellFormedStatement N (act (n_SendInvAck1 i))"
  "absTransfRule M (n_SendInvAck1 i) = (if i \<le> M then n_SendInvAck1 i else chaos \<triangleright> skip)"
  unfolding n_SendInvAck1_def symParamRule_def by auto

definition n_SendInvAck2 :: "nat \<Rightarrow> rule" where
  "n_SendInvAck2 i \<equiv>
    IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Inv \<and>\<^sub>f
    IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
    \<not>\<^sub>f IVar (Para ''Cache.State'' i) =\<^sub>f Const E
   \<triangleright>
    assign (Para ''Chan2.Cmd'' i, Const Empty) ||
    assign (Para ''Chan3.Cmd'' i, Const InvAck) ||
    assign (Para ''Cache.State'' i, Const I)"

lemma SendInvAck2:
  "symParamRule N n_SendInvAck2"
  "wellFormedStatement N (act (n_SendInvAck2 i))"
  "absTransfRule M (n_SendInvAck2 i) = (if i \<le> M then n_SendInvAck2 i else chaos \<triangleright> skip)"
  unfolding n_SendInvAck2_def symParamRule_def by auto

definition n_SendInv1 :: "nat \<Rightarrow> rule" where
  "n_SendInv1 i \<equiv>
    IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
    IVar (Para ''InvSet'' i) =\<^sub>f Const true \<and>\<^sub>f
    IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE
   \<triangleright>
    assign (Para ''Chan2.Cmd'' i, Const Inv) ||
    assign (Para ''InvSet'' i, Const false)"

definition n_SendInv1_abs :: rule where
  "n_SendInv1_abs \<equiv>
    IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE
   \<triangleright>
    skip"

lemma SendInv1:
  "symParamRule N n_SendInv1"
  "wellFormedStatement N (act (n_SendInv1 i))"
  "absTransfRule M (n_SendInv1 i) = (if i \<le> M then n_SendInv1 i else n_SendInv1_abs)"
  unfolding n_SendInv1_def n_SendInv1_abs_def symParamRule_def by auto

definition n_SendInv2 :: "nat \<Rightarrow> rule" where
  "n_SendInv2 i \<equiv>
    IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
    IVar (Para ''InvSet'' i) =\<^sub>f Const true \<and>\<^sub>f
    IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
    IVar (Ident ''ExGntd'') =\<^sub>f Const true
   \<triangleright>
    assign (Para ''Chan2.Cmd'' i, Const Inv) ||
    assign (Para ''InvSet'' i, Const false)"

definition n_SendInv2_abs :: rule where
  "n_SendInv2_abs \<equiv>
    IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
    IVar (Ident ''ExGntd'') =\<^sub>f Const true
   \<triangleright>
    skip"

lemma SendInv2:
  "symParamRule N n_SendInv2"
  "wellFormedStatement N (act (n_SendInv2 i))"
  "absTransfRule M (n_SendInv2 i) = (if i \<le> M then n_SendInv2 i else n_SendInv2_abs)"
  unfolding n_SendInv2_def n_SendInv2_abs_def symParamRule_def by auto

definition n_RecvReqE :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_RecvReqE N i \<equiv>
    IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
    IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const ReqE
   \<triangleright>
    assign (Ident ''CurCmd'', Const ReqE) ||
    assign (Ident ''CurPtr'', Const (index i)) ||
    assign (Para ''Chan1.Cmd'' i, Const Empty) ||
    forallStm (\<lambda>j. assign (Para ''InvSet'' j, IVar (Para ''ShrSet'' j))) N"

definition n_RecvReqE_abs :: "nat \<Rightarrow> rule" where
  "n_RecvReqE_abs M \<equiv>
    IVar (Ident ''CurCmd'') =\<^sub>f Const Empty
   \<triangleright>
    assign (Ident ''CurCmd'', Const ReqE) ||
    assign (Ident ''CurPtr'', Const (index (M+1))) ||
    forallStm (\<lambda>j. assign (Para ''InvSet'' j, IVar (Para ''ShrSet'' j))) M"

lemma wellFormedReqE:
  "symParamRule N (n_RecvReqE N)"
  "wellFormedStatement N (act (n_RecvReqE N i))"
  unfolding n_RecvReqE_def
  apply (auto intro!: symParamRuleI symParamStatementParallel symParamStatementForall)
  unfolding symParamForm_def symParamStatement_def symParamStatement2_def mutualDiffVars_def by auto

lemma absRecvReqE:
  "absTransfRule M (n_RecvReqE N i) = (if i \<le> M then n_RecvReqE M i else n_RecvReqE_abs M)"
  unfolding n_RecvReqE_def n_RecvReqE_abs_def by auto

definition n_RecvReqS :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_RecvReqS N i \<equiv>
    IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
    IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const ReqS
   \<triangleright>
    assign (Ident ''CurCmd'', Const ReqS) ||
    assign (Ident ''CurPtr'', Const (index i)) ||
    assign (Para ''Chan1.Cmd'' i, Const Empty) ||
    forallStm (\<lambda>j. assign (Para ''InvSet'' j, IVar (Para ''ShrSet'' j))) N"

definition n_RecvReqS_abs :: "nat \<Rightarrow> rule" where
  "n_RecvReqS_abs M \<equiv>
    IVar (Ident ''CurCmd'') =\<^sub>f Const Empty
   \<triangleright>
    assign (Ident ''CurCmd'', Const ReqS) ||
    assign (Ident ''CurPtr'', Const (index (M+1))) ||
    forallStm (\<lambda>j. assign (Para ''InvSet'' j, IVar (Para ''ShrSet'' j))) M"

lemma wellFormedRecvReqS:
  "symParamRule N (n_RecvReqS N)"
  "wellFormedStatement N (act (n_RecvReqS N i))"
  unfolding n_RecvReqS_def
  apply (auto intro!: symParamRuleI symParamStatementParallel symParamStatementForall)
  unfolding symParamForm_def symParamStatement_def symParamStatement2_def mutualDiffVars_def by auto

lemma absRecvReqS:
  "absTransfRule M (n_RecvReqS N i) =
    (if i \<le> M then n_RecvReqS M i else n_RecvReqS_abs M)"
  unfolding n_RecvReqS_def n_RecvReqS_abs_def by auto

definition n_SendReqE1 :: "nat \<Rightarrow> rule" where
  "n_SendReqE1 i \<equiv>
    IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
    IVar (Para ''Cache.State'' i) =\<^sub>f Const I
   \<triangleright>
    assign (Para ''Chan1.Cmd'' i, Const ReqE)"

lemma SendReqE1:
  "symParamRule N n_SendReqE1"
  "wellFormedStatement N (act (n_SendReqE1 i))"
  "absTransfRule M (n_SendReqE1 i) = (if i \<le> M then n_SendReqE1 i else chaos \<triangleright> skip)"
  unfolding n_SendReqE1_def symParamRule_def by auto

definition n_SendReqE2 :: "nat \<Rightarrow> rule" where
  "n_SendReqE2 i \<equiv>
    IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
    IVar (Para ''Cache.State'' i) =\<^sub>f Const S
   \<triangleright>
    assign (Para ''Chan1.Cmd'' i, Const ReqE)"

lemma SendReqE2:
  "symParamRule N n_SendReqE2"
  "wellFormedStatement N (act (n_SendReqE2 i))"
  "absTransfRule M (n_SendReqE2 i) = (if i \<le> M then n_SendReqE2 i else chaos \<triangleright> skip)"
  unfolding n_SendReqE2_def symParamRule_def by auto

definition n_SendReqS :: "nat \<Rightarrow> rule" where
  "n_SendReqS i \<equiv>
    IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
    IVar (Para ''Cache.State'' i) =\<^sub>f Const I
   \<triangleright>
    assign (Para ''Chan1.Cmd'' i, Const ReqS)"

lemma symSendReqS:
  "symParamRule N n_SendReqS"
  "wellFormedStatement N (act (n_SendReqS i))"
  "absTransfRule M (n_SendReqS i) = (if i \<le> M then n_SendReqS i else chaos \<triangleright> skip)"
  unfolding n_SendReqS_def symParamRule_def by auto 

definition rules :: "nat \<Rightarrow> rule set" where
  "rules N \<equiv> {r.
    (\<exists>i. i\<le>N \<and> r=n_RecvGntE i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_RecvGntS i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_SendGntE N i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_SendGntS i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_RecvInvAck1 i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_RecvInvAck2 i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_SendInvAck1 i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_SendInvAck2 i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_SendInv1 i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_SendInv2 i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_RecvReqE N i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_RecvReqS N i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_SendReqE1 i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_SendReqE2 i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_SendReqS i)
  }"

definition initSpec0 :: "nat \<Rightarrow> formula" where
  "initSpec0 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty) N"

definition initSpec1 :: "nat \<Rightarrow> formula" where
  "initSpec1 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty) N"

definition initSpec2 :: "nat \<Rightarrow> formula" where
  "initSpec2 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const Empty) N"

definition initSpec3 :: "nat \<Rightarrow> formula" where
  "initSpec3 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''Cache.State'' i) =\<^sub>f Const I) N"

definition initSpec4 :: "nat \<Rightarrow> formula" where
  "initSpec4 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''InvSet'' i) =\<^sub>f Const false) N"

definition initSpec5 :: "nat \<Rightarrow> formula" where
  "initSpec5 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''ShrSet'' i) =\<^sub>f Const false) N"

definition initSpec6 :: formula where
  "initSpec6 \<equiv> IVar (Ident ''ExGntd'') =\<^sub>f Const false"

definition initSpec7 :: formula where
  "initSpec7 \<equiv> IVar (Ident ''CurCmd'') =\<^sub>f Const Empty"

lemma absInitSpec:
  assumes "M \<le> N"
  shows "absTransfForm M (initSpec0 N) = initSpec0 M"
        "absTransfForm M (initSpec1 N) = initSpec1 M"
        "absTransfForm M (initSpec2 N) = initSpec2 M"
        "absTransfForm M (initSpec3 N) = initSpec3 M"
        "absTransfForm M (initSpec4 N) = initSpec4 M"
        "absTransfForm M (initSpec5 N) = initSpec5 M"
        "absTransfForm M initSpec6 = initSpec6"
        "absTransfForm M initSpec7 = initSpec7"
  unfolding initSpec0_def initSpec1_def initSpec2_def initSpec3_def
            initSpec4_def initSpec5_def initSpec6_def initSpec7_def
  using assms by auto

definition allInitSpecs :: "nat \<Rightarrow> formula list" where
  "allInitSpecs N \<equiv> [
    (initSpec0 N),
    (initSpec1 N),
    (initSpec2 N),
    (initSpec3 N),
    (initSpec4 N),
    (initSpec5 N),
    initSpec6,
    initSpec7
  ]"

definition invAux :: "nat \<Rightarrow> nat \<Rightarrow> formula" where
  "invAux N i \<equiv>
     IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
     \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
     IVar (Ident ''ExGntd'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
     forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Cache.State'' j) =\<^sub>f Const E) i N \<and>\<^sub>f
     forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE) i N \<and>\<^sub>f
     forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck) i N"

definition n_RecvInvAck1' :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_RecvInvAck1' N i = strengthenRule2 (invAux N i) (n_RecvInvAck1 i)"

definition n_RecvInvAck1'_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_RecvInvAck1'_ref N i \<equiv>
    (IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
     \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
     IVar (Ident ''ExGntd'') =\<^sub>f Const true) \<and>\<^sub>f
    forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Cache.State'' j) =\<^sub>f Const E) i N \<and>\<^sub>f
    forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE) i N \<and>\<^sub>f
    forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck) i N
   \<triangleright>
    assign (Para ''Chan3.Cmd'' i, Const Empty) ||
    assign (Para ''ShrSet'' i, Const false) ||
    assign (Ident ''ExGntd'', Const false)"

definition n_RecvInvAck1'_abs :: "nat \<Rightarrow> rule" where
  "n_RecvInvAck1'_abs M \<equiv>
    (\<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
     IVar (Ident ''ExGntd'') =\<^sub>f Const true) \<and>\<^sub>f
    forallForm (\<lambda>j. \<not>\<^sub>f IVar (Para ''Cache.State'' j) =\<^sub>f Const E) M \<and>\<^sub>f
    forallForm (\<lambda>j. \<not>\<^sub>f IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE) M \<and>\<^sub>f
    forallForm (\<lambda>j. \<not>\<^sub>f IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck) M
   \<triangleright>
    assign (Ident ''ExGntd'', Const false)"

lemma n_RecvInvAck1'Eq:
  "n_RecvInvAck1' N i = n_RecvInvAck1'_ref N i"
  by (auto simp add: n_RecvInvAck1'_def invAux_def n_RecvInvAck1_def n_RecvInvAck1'_ref_def)

lemma wellFormedSendReqE2:
  "symParamRule N (n_RecvInvAck1'_ref N)"
  "wellFormedStatement N (act (n_RecvInvAck1'_ref N i))"
  unfolding n_RecvInvAck1'_ref_def
  apply (auto intro!: symParamRuleI symParamFormAnd symParamFormForallExcl)
  unfolding symParamForm_def symParamForm2_def symParamStatement_def by auto

lemma absRecvInvAck1'b:
  "M \<le> N \<Longrightarrow> absTransfRule M (n_RecvInvAck1'_ref N i) =
    (if i \<le> M then n_RecvInvAck1 i else n_RecvInvAck1'_abs M)"
  unfolding n_RecvInvAck1_def n_RecvInvAck1'_ref_def n_RecvInvAck1'_abs_def by auto

end
