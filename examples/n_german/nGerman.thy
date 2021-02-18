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

lemma symRecvGntE:
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

lemma symRecvGntS:
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

lemma symSendGntE:
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

lemma symSendGntS:
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

lemma symRecvInvAck1:
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

lemma symRecvInvAck2:
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

lemma symSendInvAck1:
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

lemma symSendInvAck2:
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

lemma symSendInv1:
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

lemma symSendInv2:
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

lemma symRecvReqE:
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

lemma symRecvReqS:
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

lemma symSendReqE1:
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

lemma symSendReqE2:
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
definition n_RecvGntEs::" nat\<Rightarrow>rule set" where [simp]:
  "n_RecvGntEs N== oneParamCons N  n_RecvGntE"

definition n_RecvGntSs::" nat\<Rightarrow>rule set" where [simp]:
  "n_RecvGntSs N== oneParamCons N  n_RecvGntS"

definition n_SendGntEs::" nat\<Rightarrow>rule set" where [simp]:
  "n_SendGntEs N== oneParamCons N  (n_SendGntE N)"

definition n_SendGntSs::" nat\<Rightarrow>rule set" where [simp]:
  "n_SendGntSs N== oneParamCons N  n_SendGntS"

definition n_RecvInvAck1s::" nat\<Rightarrow>rule set" where [simp]:
  "n_RecvInvAck1s N== oneParamCons N  n_RecvInvAck1"

definition n_RecvInvAck2s::" nat\<Rightarrow>rule set" where [simp]:
  "n_RecvInvAck2s N== oneParamCons N  n_RecvInvAck2"

definition n_SendInvAck1s::" nat\<Rightarrow>rule set" where [simp]:
  "n_SendInvAck1s N== oneParamCons N  (n_SendInvAck1 )"

definition n_SendInvAck2s::" nat\<Rightarrow>rule set" where [simp]:
  "n_SendInvAck2s N== oneParamCons N  (n_SendInvAck2 )"

definition n_SendInv1s::" nat\<Rightarrow>rule set" where [simp]:
  "n_SendInv1s N== oneParamCons N n_SendInv1"

definition n_SendInv2s::" nat\<Rightarrow>rule set" where [simp]:
  "n_SendInv2s N== oneParamCons N  (n_SendInv2 )"

definition n_RecvReqEs::" nat\<Rightarrow>rule set" where [simp]:
  "n_RecvReqEs N== oneParamCons N  (n_RecvReqE N )"

definition n_RecvReqSs::" nat\<Rightarrow>rule set" where [simp]:
  "n_RecvReqSs N== oneParamCons N (n_RecvReqS N)"

definition n_SendReqE1s::" nat\<Rightarrow>rule set" where [simp]:
  "n_SendReqE1s N== oneParamCons N n_SendReqE1"

definition n_SendReqE2s::" nat\<Rightarrow>rule set" where [simp]:
  "n_SendReqE2s N== oneParamCons N  n_SendReqE2 "

definition n_SendReqSs::" nat\<Rightarrow>rule set" where [simp]:
  "n_SendReqSs N== oneParamCons N  (n_SendReqS )"

 
definition rules' :: "nat \<Rightarrow> rule set" where [simp]:
  "rules' N \<equiv>  (n_RecvGntEs N) \<union>
    (n_RecvGntSs N) \<union>
    (n_SendGntEs  N) \<union>
    (n_SendGntSs N) \<union>
    ( n_RecvInvAck1s N)\<union>
    ( n_RecvInvAck2s N) \<union>
    ( n_SendInvAck1s N) \<union>
    ( n_SendInvAck2s N) \<union>
    ( n_SendInv1s N) \<union>
    ( n_SendInv2s N) \<union>
    ( n_RecvReqEs  N) \<union>
    ( n_RecvReqSs  N) \<union>
    ( n_SendReqE1s N) \<union>
    ( n_SendReqE2s N) \<union>
    ( n_SendReqSs N)  
   "
lemma n_RecvGntEsIsSym:
  "symProtRules' N (n_RecvGntEs N)"
  using symRecvGntE(1) n_RecvGntEs_def symParaRuleInfSymRuleSet by auto

lemma n_RecvGntSsIsSym:
  "symProtRules' N (n_RecvGntSs N)"
  using n_RecvGntSs_def symRecvGntS(1) symParaRuleInfSymRuleSet by auto 

lemma n_SendGntEsIsSym:
  "symProtRules' N (n_SendGntEs N)"
  using n_SendGntEs_def symSendGntE(1) symParaRuleInfSymRuleSet by auto 

lemma n_SendGntSsIsSym:
  "symProtRules' N (n_SendGntSs N)"  
  using n_SendGntSs_def symSendGntS(1) symParaRuleInfSymRuleSet by auto

lemma  n_RecvInvAck1sIsSym:
  "symProtRules' N ( n_RecvInvAck1s N)"
  using symRecvInvAck1(1)  n_RecvInvAck1s_def symParaRuleInfSymRuleSet by auto

lemma n_RecvInvAck2sIsSym:
  "symProtRules' N (n_RecvInvAck2s N)"
  using n_RecvInvAck2s_def symRecvInvAck2(1) symParaRuleInfSymRuleSet by auto 

lemma n_SendInvAck1sIsSym:
  "symProtRules' N (n_SendInvAck1s N)"
  using n_SendInvAck1s_def symSendInvAck1(1) symParaRuleInfSymRuleSet by auto 

lemma n_SendInvAck2sIsSym:
  "symProtRules' N (n_SendInvAck2s N)"
  using n_SendInvAck2s_def symSendInvAck2(1) symParaRuleInfSymRuleSet by auto 

lemma n_SendInv1sIsSym:
  "symProtRules' N (n_SendInv1s N)"
  using n_SendInv1s_def symSendInv1(1) symParaRuleInfSymRuleSet by auto 

lemma n_SendInv2sIsSym:
  "symProtRules' N (n_SendInv2s N)"
  using n_SendInv2s_def symSendInv2(1) symParaRuleInfSymRuleSet by auto 

lemma n_RecvReqEsIsSym:
  "symProtRules' N (n_RecvReqEs N)"
  using n_RecvReqEs_def symRecvReqE(1) symParaRuleInfSymRuleSet by auto 

lemma n_RecvReqSsIsSym:
  "symProtRules' N (n_RecvReqSs N)"
  using n_RecvReqSs_def symRecvReqS(1) symParaRuleInfSymRuleSet by auto 

lemma n_SendReqE1sIsSym:
  "symProtRules' N (n_SendReqE1s N)"
  using n_SendReqE1s_def symSendReqE1(1) symParaRuleInfSymRuleSet by auto 

lemma n_SendReqE2sIsSym:
  "symProtRules' N (n_SendReqE2s N)"
  using n_SendReqE2s_def symSendReqE2(1) symParaRuleInfSymRuleSet by auto 

lemma n_SendReqSsIsSym:
  "symProtRules' N (n_SendReqSs N)"
  using n_SendReqSs_def symSendReqS(1) symParaRuleInfSymRuleSet by auto
 

lemma rulesSym':
  shows "symProtRules' N (rules' N)"
  using n_RecvGntEsIsSym n_RecvGntSsIsSym n_RecvInvAck1sIsSym n_RecvInvAck2sIsSym n_RecvReqEsIsSym n_RecvReqSsIsSym n_SendGntEsIsSym n_SendGntSsIsSym n_SendInv1sIsSym n_SendInv2sIsSym n_SendInvAck1sIsSym n_SendInvAck2sIsSym n_SendReqE1sIsSym 
n_SendReqE2sIsSym n_SendReqSsIsSym rules'_def symProtRulesUnion by presburger 
 

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
    forallFormExcl 
    (\<lambda>j. ((\<not>\<^sub>f (IVar (Para ''Cache.State'' j) =\<^sub>f Const E))  \<and>\<^sub>f
       ( \<not>\<^sub>f (IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE))  \<and>\<^sub>f
       ( \<not>\<^sub>f (IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck))
    )) i N"
     (*forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Cache.State'' j) =\<^sub>f Const E) i N \<and>\<^sub>f
     forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE) i N \<and>\<^sub>f
     forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck) i N"*)

definition n_RecvInvAck1' :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_RecvInvAck1' N i = strengthenRule2 (invAux N i) (n_RecvInvAck1 i)"

definition n_RecvInvAck1'_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_RecvInvAck1'_ref N i \<equiv>
    (IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
     \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
     IVar (Ident ''ExGntd'') =\<^sub>f Const true) \<and>\<^sub>f
   forallFormExcl 
    (\<lambda>j. ((\<not>\<^sub>f (IVar (Para ''Cache.State'' j) =\<^sub>f Const E))  \<and>\<^sub>f
       ( \<not>\<^sub>f (IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE))  \<and>\<^sub>f
       ( \<not>\<^sub>f (IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck))
    )) i N
   \<triangleright>
    assign (Para ''Chan3.Cmd'' i, Const Empty) ||
    assign (Para ''ShrSet'' i, Const false) ||
    assign (Ident ''ExGntd'', Const false)"

definition n_RecvInvAck1'_abs :: "nat \<Rightarrow> rule" where
  "n_RecvInvAck1'_abs M \<equiv>
    (\<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
     IVar (Ident ''ExGntd'') =\<^sub>f Const true) \<and>\<^sub>f
    forallForm(\<lambda>j. ((\<not>\<^sub>f (IVar (Para ''Cache.State'' j) =\<^sub>f Const E))  \<and>\<^sub>f
       ( \<not>\<^sub>f (IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE))  \<and>\<^sub>f
       ( \<not>\<^sub>f (IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck))
    )) M  
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


definition pair1:: "((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula))" where [simp]:
 "pair1 ==(%i. IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
     \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
     IVar (Ident ''ExGntd'') =\<^sub>f Const true  ,
                  (\<lambda>j. ((\<not>\<^sub>f (IVar (Para ''Cache.State'' j) =\<^sub>f Const E))  \<and>\<^sub>f
       ( \<not>\<^sub>f (IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE))  \<and>\<^sub>f
       ( \<not>\<^sub>f (IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck))))
    ) "

definition F::"((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula)) set" where [simp]:
"F \<equiv> {pair1}"

  
definition n_RecvInvAck12s::" nat \<Rightarrow>rule set" where [simp]:
  "n_RecvInvAck12s N==
  (oneParamCons N  (%i. (strengthenRule2  (constrInvByExcl pair1 i N) (n_RecvInvAck1 i))))"

  
definition rules2' :: "nat \<Rightarrow> rule set" where [simp]:
  "rules2' N \<equiv>  (n_RecvGntEs N) \<union>
    (n_RecvGntSs N) \<union>
    (n_SendGntEs  N) \<union>
    (n_SendGntSs N) \<union>
    ( n_RecvInvAck12s N)\<union>
    ( n_RecvInvAck2s N) \<union>
    ( n_SendInvAck1s N) \<union>
    ( n_SendInvAck2s N) \<union>
    ( n_SendInv1s N) \<union>
    ( n_SendInv2s N) \<union>
    ( n_RecvReqEs  N) \<union>
    ( n_RecvReqSs  N) \<union>
    ( n_SendReqE1s N) \<union>
    ( n_SendReqE2s N) \<union>
    ( n_SendReqSs N)  
    "


end
