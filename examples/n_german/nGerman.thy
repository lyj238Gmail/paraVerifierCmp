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
definition n_RecvGntEs::" nat\<Rightarrow>rule set" where  
  "n_RecvGntEs N== oneParamCons N  n_RecvGntE"

definition n_RecvGntSs::" nat\<Rightarrow>rule set" where 
  "n_RecvGntSs N== oneParamCons N  n_RecvGntS"

definition n_SendGntEs::" nat\<Rightarrow>rule set" where  
  "n_SendGntEs N== oneParamCons N  (n_SendGntE N)"

definition n_SendGntSs::" nat\<Rightarrow>rule set" where  
  "n_SendGntSs N== oneParamCons N  n_SendGntS"

definition n_RecvInvAck1s::" nat\<Rightarrow>rule set" where  
  "n_RecvInvAck1s N== oneParamCons N  n_RecvInvAck1"

definition n_RecvInvAck2s::" nat\<Rightarrow>rule set" where 
  "n_RecvInvAck2s N== oneParamCons N  n_RecvInvAck2"

definition n_SendInvAck1s::" nat\<Rightarrow>rule set" where  
  "n_SendInvAck1s N== oneParamCons N  (n_SendInvAck1 )"

definition n_SendInvAck2s::" nat\<Rightarrow>rule set" where  
  "n_SendInvAck2s N== oneParamCons N  (n_SendInvAck2 )"

definition n_SendInv1s::" nat\<Rightarrow>rule set" where  
  "n_SendInv1s N== oneParamCons N n_SendInv1"

definition n_SendInv2s::" nat\<Rightarrow>rule set" where  
  "n_SendInv2s N== oneParamCons N  (n_SendInv2 )"

definition n_RecvReqEs::" nat\<Rightarrow>rule set" where  
  "n_RecvReqEs N== oneParamCons N  (n_RecvReqE N )"

definition n_RecvReqSs::" nat\<Rightarrow>rule set" where  
  "n_RecvReqSs N== oneParamCons N (n_RecvReqS N)"

definition n_SendReqE1s::" nat\<Rightarrow>rule set" where  
  "n_SendReqE1s N== oneParamCons N n_SendReqE1"

definition n_SendReqE2s::" nat\<Rightarrow>rule set" where  
  "n_SendReqE2s N== oneParamCons N  n_SendReqE2 "

definition n_SendReqSs::" nat\<Rightarrow>rule set" where  
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
 

definition initSpec0 :: "nat \<Rightarrow> formula" where [simp]:
  "initSpec0 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty) N"

definition initSpec1 :: "nat \<Rightarrow> formula" where [simp]:
  "initSpec1 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty) N"

definition initSpec2 :: "nat \<Rightarrow> formula" where [simp]:
  "initSpec2 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const Empty) N"

definition initSpec3 :: "nat \<Rightarrow> formula" where [simp]:
  "initSpec3 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''Cache.State'' i) =\<^sub>f Const I) N"

definition initSpec4 :: "nat \<Rightarrow> formula" where [simp]:
  "initSpec4 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''InvSet'' i) =\<^sub>f Const false) N"

definition initSpec5 :: "nat \<Rightarrow> formula" where [simp]:
  "initSpec5 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''ShrSet'' i) =\<^sub>f Const false) N"

definition initSpec6 :: formula where [simp]:
  "initSpec6 \<equiv> IVar (Ident ''ExGntd'') =\<^sub>f Const false"

definition initSpec7 :: formula where [simp]:
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

(*lemma n_RecvInvAck1'Eq:
  "n_RecvInvAck1' N i = n_RecvInvAck1'_ref N i"
  apply (auto simp add: n_RecvInvAck1'_def invAux_def n_RecvInvAck1_def 
      n_RecvInvAck1'_ref_def )
  sorry*)

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

definition F::"((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula)) set" where  
"F \<equiv> {pair1}"

  
definition n_RecvInvAck12s::" nat \<Rightarrow>rule set" where 
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


definition absRules' :: " nat\<Rightarrow>rule set" where [simp]:
  
  "absRules' M \<equiv> (n_RecvGntEs M) \<union>
    (n_RecvGntSs M) \<union>
    (n_SendGntEs  M) \<union>
    (n_SendGntSs M) \<union>
    ( n_RecvInvAck1s M)\<union>
    ( n_RecvInvAck2s M) \<union>
    ( n_SendInvAck1s M) \<union>
    ( n_SendInvAck2s M) \<union>
    ( n_SendInv1s M) \<union>
    ( n_SendInv2s M) \<union>
    ( n_RecvReqEs  M) \<union>
    ( n_RecvReqSs  M) \<union>
    ( n_SendReqE1s M) \<union>
    ( n_SendReqE2s M) \<union>
    ( n_SendReqSs M) \<union>
    {  n_SendGntE_abs M}\<union>
    {n_SendGntS_abs M} \<union> 
    {n_RecvInvAck1'_abs M }\<union> 
    {n_RecvInvAck2_abs }\<union>
    { n_SendInv1_abs}\<union>
    { n_SendInv2_abs}\<union>
    {n_RecvReqE_abs M}\<union>
    {n_RecvReqS_abs M}\<union>
    {chaos \<triangleright> skip}
    "

 

   

lemma absRecvGntEs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_RecvGntEs N) = (n_RecvGntEs M) \<union> {chaos \<triangleright> skip}"
  unfolding n_RecvGntEs_def apply (rule absGen) 
  using symRecvGntE(3) apply blast
  by simp  

lemma absRecvGntSs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_RecvGntSs N) = (n_RecvGntSs M) \<union> {chaos \<triangleright> skip}"
  unfolding n_RecvGntSs_def apply (rule absGen) 
  using symRecvGntS(3) apply blast
  by simp 

lemma absSendGntEs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_SendGntEs N) = (n_SendGntEs M) \<union> {n_SendGntE_abs M}"
  unfolding n_SendGntEs_def apply (rule absGen) thm absSendGntE
  using absSendGntE apply auto[1]
    by (simp  )

lemma absSendGntSs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_SendGntSs N) = (n_SendGntSs M) \<union> {n_SendGntS_abs M}"
  unfolding n_SendGntSs_def apply (rule absGen) thm absSendGntS
  using absSendGntS apply blast
    by (simp  )
   

lemma absRecvInvAck2s:
  "M < N \<Longrightarrow> absTransfRule M ` (n_RecvInvAck2s N) = (n_RecvInvAck2s M) \<union> {n_RecvInvAck2_abs }"
  unfolding n_RecvInvAck2s_def apply (rule absGen)
  using symRecvInvAck2(3) apply blast
  by simp  

lemma n_RecvInvAck12_ref':
  "strengthenRule2 (constrInvByExcl pair1 i N) (n_RecvInvAck1 i) = n_RecvInvAck1'_ref N i"
  unfolding n_RecvInvAck1'_ref_def n_RecvInvAck1_def constrInvByExcl_def pair1_def fst_conv snd_conv
  by (auto simp add: strengthenRule2.simps)
 
lemma absRecvInvAck1s:
  "M < N \<Longrightarrow> absTransfRule M ` (n_RecvInvAck12s N) = (n_RecvInvAck1s M) \<union> {n_RecvInvAck1'_abs M}"
  unfolding n_RecvInvAck12s_def n_RecvInvAck1s_def apply (rule absGen)
  using absRecvInvAck1'b n_RecvInvAck12_ref' apply auto[1]
  by simp

lemma absSendInvAck1s:
  "M < N \<Longrightarrow> absTransfRule M ` (n_SendInvAck1s N) = (n_SendInvAck1s M) \<union> {chaos \<triangleright> skip}"
  unfolding n_SendInvAck1s_def  apply (rule absGen)
  using symSendInvAck1(3) apply blast
  by simp 

lemma absSendInvAck2s:
  "M < N \<Longrightarrow> absTransfRule M ` (n_SendInvAck2s N) = (n_SendInvAck2s M) \<union> {chaos \<triangleright> skip}"
  unfolding n_SendInvAck2s_def  apply (rule absGen)
  using symSendInvAck2(3) apply blast
  by simp 

lemma absSendInv1s:
  "M < N \<Longrightarrow> absTransfRule M ` (n_SendInv1s N) = (n_SendInv1s M) \<union> {n_SendInv1_abs}"
  unfolding n_SendInv1s_def  apply (rule absGen)
  using symSendInv1(3) apply blast
  by simp 
 
lemma absSendInv2s:
  "M < N \<Longrightarrow> absTransfRule M ` (n_SendInv2s N) = (n_SendInv2s M) \<union> {n_SendInv2_abs}"
  unfolding n_SendInv2s_def  apply (rule absGen)
  using symSendInv2(3) apply blast
  by simp  

lemma absRecvReqEs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_RecvReqEs N) = (n_RecvReqEs M) \<union> {n_RecvReqE_abs M}"
  unfolding n_RecvReqEs_def  apply (rule absGen)
  using absRecvReqE apply blast 
  by simp

lemma absRecvReqSs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_RecvReqSs N) = (n_RecvReqSs M) \<union> {n_RecvReqS_abs M}"
  unfolding n_RecvReqSs_def  apply (rule absGen)
  using absRecvReqS apply blast 
  by simp

lemma absSendReqE1s:
  "M < N \<Longrightarrow> absTransfRule M ` (n_SendReqE1s N) = (n_SendReqE1s M) \<union> {chaos \<triangleright> skip}"
  unfolding n_SendReqE1s_def  apply (rule absGen)
  using symSendReqE1(3) apply blast 
  by simp 

lemma absSendReqE2s:
  "M < N \<Longrightarrow> absTransfRule M ` (n_SendReqE2s N) = (n_SendReqE2s M) \<union> {chaos \<triangleright> skip}"
  unfolding n_SendReqE2s_def  apply (rule absGen)
  using symSendReqE2(3) apply blast 
  by simp

lemma absSendReqSs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_SendReqSs N) = (n_SendReqSs M) \<union> {chaos \<triangleright> skip}"
  unfolding n_SendReqSs_def  apply (rule absGen)
  using symSendReqS(3) apply blast 
  by simp
thm strengthenRule2.simps 
 
definition absRules :: "nat \<Rightarrow> rule set" where
  "absRules N \<equiv> (n_RecvGntEs N) \<union>
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
    ( n_SendReqSs N)\<union>{  n_SendGntE_abs N}\<union>
    {n_SendGntS_abs N} \<union> 
    {n_RecvInvAck1'_abs N}\<union> 
    {n_RecvInvAck2_abs }\<union>
    { n_SendInv1_abs}\<union>
    { n_SendInv2_abs}\<union>
    {n_RecvReqE_abs N}\<union>
    {n_RecvReqS_abs N}\<union>
    {chaos \<triangleright> skip}
    "

lemma absAll:
  "M < N \<Longrightarrow> absTransfRule M ` rules2' N = absRules M"
  unfolding rules2'_def absRules_def absRules_def image_Un 
    absRecvGntEs
    absRecvGntSs
    absSendGntEs
    absSendGntSs
    absRecvInvAck1s
    absRecvInvAck2s
    absSendInvAck1s
    absSendInvAck2s
    absSendInv1s
    absSendInv2s
    absRecvReqEs
    absRecvReqSs
    absSendReqE1s
    absSendReqE2s
    absSendReqSs by auto

lemma symPreds0[intro]:
  "symPredSet' N ({(initSpec0 N)} )"
unfolding initSpec0_def
    apply (rule symPredSetForall)
  unfolding symParamForm_def by auto 

lemma symPreds1[intro]:
  "symPredSet' N ({(initSpec1 N)} )"
unfolding initSpec1_def
    apply (rule symPredSetForall)
  unfolding symParamForm_def by auto

lemma symPreds2[intro]:
  "symPredSet' N ({(initSpec2 N)} )"
unfolding initSpec2_def
    apply (rule symPredSetForall)
  unfolding symParamForm_def by auto 

lemma symPreds3[intro]:
  "symPredSet' N ({(initSpec3 N)} )"
unfolding initSpec3_def
    apply (rule symPredSetForall)
  unfolding symParamForm_def by auto 

lemma symPreds4[intro]:
  "symPredSet' N ({(initSpec4 N)} )"
unfolding initSpec4_def
    apply (rule symPredSetForall)
  unfolding symParamForm_def by auto 

lemma symPreds5[intro]:
  "symPredSet' N ({(initSpec5 N)} )"
unfolding initSpec5_def
    apply (rule symPredSetForall)
  unfolding symParamForm_def by auto 

lemma symPreds6[intro]:
  "symPredSet' N ({(initSpec6 )} )"
  unfolding symPredSet'_def initSpec6_def by auto

lemma symPreds7[intro]:
  "symPredSet' N ({(initSpec7 )} )"
  unfolding symPredSet'_def initSpec7_def by auto

lemma symPreds:
  "symPredSet' N ({(initSpec0 N)} \<union>
    {(initSpec1 N)}\<union>
    {(initSpec2 N)}\<union>
    {(initSpec3 N)}\<union>
    {(initSpec4 N)}\<union>
    {(initSpec5 N)}\<union>
    {initSpec6} \<union>
    {initSpec7})"
  
  apply (meson symPreds0 symPreds1 symPreds2 symPreds3 symPreds4 symPreds5 symPreds6 symPreds7 symPredsUnion)
   
  done 

definition type_inv_Chan3_Cmd :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_Chan3_Cmd N s = 
(\<forall>i. i \<le> N \<longrightarrow> s (Para ''Chan3.Cmd'' i) = InvAck \<or> s (Para ''Chan3.Cmd'' i) = Empty)
 "

lemma n_RecvGntE_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_RecvGntE i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_RecvGntE_def by auto

lemma n_RecvGntS_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_RecvGntS i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_RecvGntS_def by auto


lemma n_SendGntE_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_SendGntE N i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_SendGntE_def by auto

lemma n_SendGntS_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_SendGntS  i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_SendGntS_def by auto

lemma n_RecvInvAck12_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
  type_inv_Chan3_Cmd N 
  (trans1 (act ( (strengthenRule2  (constrInvByExcl pair1 i N) (n_RecvInvAck1 i)))) sk)"
  unfolding type_inv_Chan3_Cmd_def n_RecvInvAck1_def apply (auto simp add:strengthenRule2.simps )
  done

lemma n_RecvInvAck2_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
  type_inv_Chan3_Cmd N 
  (trans1 (act (  (n_RecvInvAck2 i))) sk)"
  unfolding type_inv_Chan3_Cmd_def n_RecvInvAck2_def apply (auto simp add:strengthenRule2.simps )
  done
lemma n_SendInvAck1_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_SendInvAck1 i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_SendInvAck1_def by auto

lemma n_SendInvAck2_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_SendInvAck2 i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_SendInvAck2_def by auto

lemma n_SendInv1_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_SendInv1 i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_SendInv1_def by auto

lemma n_SendInv2_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_SendInv2 i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_SendInv2_def by auto


lemma n_RecvReqE_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_RecvReqE N i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_RecvReqE_def by auto 

lemma n_RecvReqS_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_RecvReqS N i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_RecvReqS_def by auto

lemma n_SendReqE1_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_SendReqE1  i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_SendReqE1_def by auto

lemma n_SendReqE2_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_SendReqE2  i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_SendReqE2_def by auto

lemma n_SendReqS_type_inv_Chan3_Cmd [intro]:
  "type_inv_Chan3_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan3_Cmd N (trans1 (act (n_SendReqS  i)) sk)"
  unfolding type_inv_Chan3_Cmd_def n_SendReqS_def by auto 


lemma inv_Chan3_Cmd' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_Chan3_Cmd N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_Chan3_Cmd_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
    subgoal unfolding n_RecvGntEs_def  by auto
    subgoal unfolding n_RecvGntSs_def   by auto
    subgoal unfolding  n_SendGntEs_def by auto 
    subgoal unfolding  n_SendGntSs_def by auto  
    subgoal unfolding   n_RecvInvAck12s_def
      using n_RecvInvAck12_type_inv_Chan3_Cmd by auto  
    subgoal
      using   n_RecvInvAck2s_def by auto
    subgoal
      using  n_SendInvAck1s_def by auto  
    subgoal
      using n_SendInvAck2s_def by auto 
    subgoal
      using  n_SendInv1s_def by auto  
    subgoal
      using n_SendInv2s_def by auto 
    subgoal
      using  n_RecvReqEs_def by auto  
    subgoal
      using n_RecvReqSs_def by auto 
    subgoal
      using n_SendReqE1s_def by auto 
    subgoal
      using n_SendReqE2s_def by auto  
    subgoal
      using n_SendReqSs_def by auto 

    
    done
  done
   

lemma inv_Chan3_Cmd'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N \<longrightarrow> i \<le> N \<longrightarrow> isEnumVal s (Para ''Chan3.Cmd'' i)"
  using inv_Chan3_Cmd' unfolding type_inv_Chan3_Cmd_def InvAck_def InvAck_def
  by (metis Empty_def assms getValueType.simps(1) isEnumVal_def typeOf_def)   

 

definition type_inv_Chan2_Cmd :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_Chan2_Cmd N s = 
(\<forall>i. i \<le> N \<longrightarrow> s (Para ''Chan2.Cmd'' i) = GntS \<or> s (Para ''Chan2.Cmd'' i) = GntE \<or>
s (Para ''Chan2.Cmd'' i) = Inv \<or>
s (Para ''Chan2.Cmd'' i) = Empty)
 "

lemma n_RecvGntE_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_RecvGntE i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_RecvGntE_def by auto

lemma n_RecvGntS_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_RecvGntS i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_RecvGntS_def by auto


lemma n_SendGntE_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_SendGntE N i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_SendGntE_def by auto

lemma n_SendGntS_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_SendGntS  i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_SendGntS_def by auto

lemma n_RecvInvAck12_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
  type_inv_Chan2_Cmd N 
  (trans1 (act ( (strengthenRule2  (constrInvByExcl pair1 i N) (n_RecvInvAck1 i)))) sk)"
  unfolding type_inv_Chan2_Cmd_def n_RecvInvAck1_def apply (auto simp add:strengthenRule2.simps )
  done

lemma n_RecvInvAck2_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
  type_inv_Chan2_Cmd N 
  (trans1 (act (  (n_RecvInvAck2 i))) sk)"
  unfolding type_inv_Chan2_Cmd_def n_RecvInvAck2_def apply (auto simp add:strengthenRule2.simps )
  done
lemma n_SendInvAck1_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_SendInvAck1 i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_SendInvAck1_def by auto

lemma n_SendInvAck2_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_SendInvAck2 i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_SendInvAck2_def by auto

lemma n_SendInv1_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_SendInv1 i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_SendInv1_def by auto

lemma n_SendInv2_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_SendInv2 i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_SendInv2_def by auto


lemma n_RecvReqE_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_RecvReqE N i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_RecvReqE_def by auto 

lemma n_RecvReqS_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_RecvReqS N i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_RecvReqS_def by auto

lemma n_SendReqE1_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_SendReqE1  i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_SendReqE1_def by auto

lemma n_SendReqE2_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_SendReqE2  i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_SendReqE2_def by auto

lemma n_SendReqS_type_inv_Chan2_Cmd [intro]:
  "type_inv_Chan2_Cmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Chan2_Cmd N (trans1 (act (n_SendReqS  i)) sk)"
  unfolding type_inv_Chan2_Cmd_def n_SendReqS_def by auto 


lemma inv_Chan2_Cmd' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_Chan2_Cmd N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_Chan2_Cmd_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
    subgoal unfolding n_RecvGntEs_def  by auto
    subgoal unfolding n_RecvGntSs_def   by auto
    subgoal unfolding  n_SendGntEs_def by auto 
    subgoal unfolding  n_SendGntSs_def by auto  
    subgoal unfolding   n_RecvInvAck12s_def
      using n_RecvInvAck12_type_inv_Chan2_Cmd by auto  
    subgoal
      using   n_RecvInvAck2s_def by auto
    subgoal
      using  n_SendInvAck1s_def by auto  
    subgoal
      using n_SendInvAck2s_def by auto 
    subgoal
      using  n_SendInv1s_def by auto  
    subgoal
      using n_SendInv2s_def by auto 
    subgoal
      using  n_RecvReqEs_def by auto  
    subgoal
      using n_RecvReqSs_def by auto 
    subgoal
      using n_SendReqE1s_def by auto 
    subgoal
      using n_SendReqE2s_def by auto  
    subgoal
      using n_SendReqSs_def by auto 

    
    done
  done
   

lemma inv_Chan2_Cmd'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N \<longrightarrow> i \<le> N \<longrightarrow> isEnumVal s (Para ''Chan2.Cmd'' i)"
  using inv_Chan2_Cmd' unfolding type_inv_Chan2_Cmd_def Inv_def GntS_def GntE_def
  by (metis Empty_def assms getValueType.simps(1) isEnumVal_def typeOf_def)   


definition type_inv_Cache_State :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_Cache_State N s = 
(\<forall>i. i \<le> N \<longrightarrow> s ((Para ''Cache.State'' i)) = I  \<or> s (Para ''Cache.State'' i) = S \<or>
  s (Para ''Cache.State'' i) = E)
 "

lemma n_RecvGntE_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_RecvGntE i)) sk)"
  unfolding type_inv_Cache_State_def n_RecvGntE_def by auto

lemma n_RecvGntS_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_RecvGntS i)) sk)"
  unfolding type_inv_Cache_State_def n_RecvGntS_def by auto


lemma n_SendGntE_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_SendGntE N i)) sk)"
  unfolding type_inv_Cache_State_def n_SendGntE_def by auto

lemma n_SendGntS_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_SendGntS  i)) sk)"
  unfolding type_inv_Cache_State_def n_SendGntS_def by auto

lemma n_RecvInvAck12_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
  type_inv_Cache_State N 
  (trans1 (act ( (strengthenRule2  (constrInvByExcl pair1 i N) (n_RecvInvAck1 i)))) sk)"
  unfolding type_inv_Cache_State_def n_RecvInvAck1_def apply (auto simp add:strengthenRule2.simps )
  done

lemma n_RecvInvAck2_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
  type_inv_Cache_State N 
  (trans1 (act (  (n_RecvInvAck2 i))) sk)"
  unfolding type_inv_Cache_State_def n_RecvInvAck2_def apply (auto simp add:strengthenRule2.simps )
  done
lemma n_SendInvAck1_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_SendInvAck1 i)) sk)"
  unfolding type_inv_Cache_State_def n_SendInvAck1_def by auto

lemma n_SendInvAck2_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_SendInvAck2 i)) sk)"
  unfolding type_inv_Cache_State_def n_SendInvAck2_def by auto

lemma n_SendInv1_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_SendInv1 i)) sk)"
  unfolding type_inv_Cache_State_def n_SendInv1_def by auto

lemma n_SendInv2_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_SendInv2 i)) sk)"
  unfolding type_inv_Cache_State_def n_SendInv2_def by auto


lemma n_RecvReqE_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_RecvReqE N i)) sk)"
  unfolding type_inv_Cache_State_def n_RecvReqE_def by auto 

lemma n_RecvReqS_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_RecvReqS N i)) sk)"
  unfolding type_inv_Cache_State_def n_RecvReqS_def by auto

lemma n_SendReqE1_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_SendReqE1  i)) sk)"
  unfolding type_inv_Cache_State_def n_SendReqE1_def by auto

lemma n_SendReqE2_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_SendReqE2  i)) sk)"
  unfolding type_inv_Cache_State_def n_SendReqE2_def by auto

lemma n_SendReqS_type_inv_Cache_State [intro]:
  "type_inv_Cache_State N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_Cache_State N (trans1 (act (n_SendReqS  i)) sk)"
  unfolding type_inv_Cache_State_def n_SendReqS_def by auto 


lemma inv_Cache_State' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_Cache_State N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_Cache_State_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
    subgoal unfolding n_RecvGntEs_def  by auto
    subgoal unfolding n_RecvGntSs_def   by auto
    subgoal unfolding  n_SendGntEs_def by auto 
    subgoal unfolding  n_SendGntSs_def by auto  
    subgoal unfolding   n_RecvInvAck12s_def
      using n_RecvInvAck12_type_inv_Cache_State by auto  
    subgoal
      using   n_RecvInvAck2s_def by auto
    subgoal
      using  n_SendInvAck1s_def by auto  
    subgoal
      using n_SendInvAck2s_def by auto 
    subgoal
      using  n_SendInv1s_def by auto  
    subgoal
      using n_SendInv2s_def by auto 
    subgoal
      using  n_RecvReqEs_def by auto  
    subgoal
      using n_RecvReqSs_def by auto 
    subgoal
      using n_SendReqE1s_def by auto 
    subgoal
      using n_SendReqE2s_def by auto  
    subgoal
      using n_SendReqSs_def by auto 

    
    done
  done
   

lemma inv_Cache_State'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N \<longrightarrow> i \<le> N \<longrightarrow> isEnumVal s (Para ''Cache.State'' i)"
  using inv_Cache_State' unfolding type_inv_Cache_State_def I_def S_def E_def
  by (metis  assms getValueType.simps(1) isEnumVal_def typeOf_def)   






 
definition type_inv_CurCmd :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_CurCmd N s = 
(\<forall>i. i \<le> N \<longrightarrow> s ((Ident ''CurCmd'')) = Empty  \<or> s (Ident ''CurCmd'') = ReqS \<or>
  s (Ident ''CurCmd'') =  ReqE \<or> s ((Ident ''CurCmd'')) = InvAck  \<or> s (Ident ''CurCmd'') = GntS \<or>
  s (Ident ''CurCmd'') =   Inv \<or>  s (Ident ''CurCmd'') =  GntE)
 "

lemma n_RecvGntE_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_RecvGntE i)) sk)"
  unfolding type_inv_CurCmd_def n_RecvGntE_def by auto

lemma n_RecvGntS_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_RecvGntS i)) sk)"
  unfolding type_inv_CurCmd_def n_RecvGntS_def by auto


lemma n_SendGntE_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_SendGntE N i)) sk)"
  unfolding type_inv_CurCmd_def n_SendGntE_def by auto

lemma n_SendGntS_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_SendGntS  i)) sk)"
  unfolding type_inv_CurCmd_def n_SendGntS_def by auto

lemma n_RecvInvAck12_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
  type_inv_CurCmd N 
  (trans1 (act ( (strengthenRule2  (constrInvByExcl pair1 i N) (n_RecvInvAck1 i)))) sk)"
  unfolding type_inv_CurCmd_def n_RecvInvAck1_def apply (auto simp add:strengthenRule2.simps )
  done

lemma n_RecvInvAck2_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
  type_inv_CurCmd N 
  (trans1 (act (  (n_RecvInvAck2 i))) sk)"
  unfolding type_inv_CurCmd_def n_RecvInvAck2_def apply (auto simp add:strengthenRule2.simps )
  done
lemma n_SendInvAck1_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_SendInvAck1 i)) sk)"
  unfolding type_inv_CurCmd_def n_SendInvAck1_def by auto

lemma n_SendInvAck2_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_SendInvAck2 i)) sk)"
  unfolding type_inv_CurCmd_def n_SendInvAck2_def by auto

lemma n_SendInv1_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_SendInv1 i)) sk)"
  unfolding type_inv_CurCmd_def n_SendInv1_def by auto

lemma n_SendInv2_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_SendInv2 i)) sk)"
  unfolding type_inv_CurCmd_def n_SendInv2_def by auto


lemma n_RecvReqE_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_RecvReqE N i)) sk)"
  unfolding type_inv_CurCmd_def n_RecvReqE_def by auto 

lemma n_RecvReqS_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_RecvReqS N i)) sk)"
  unfolding type_inv_CurCmd_def n_RecvReqS_def by auto

lemma n_SendReqE1_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_SendReqE1  i)) sk)"
  unfolding type_inv_CurCmd_def n_SendReqE1_def by auto

lemma n_SendReqE2_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_SendReqE2  i)) sk)"
  unfolding type_inv_CurCmd_def n_SendReqE2_def by auto

lemma n_SendReqS_type_inv_CurCmd [intro]:
  "type_inv_CurCmd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_CurCmd N (trans1 (act (n_SendReqS  i)) sk)"
  unfolding type_inv_CurCmd_def n_SendReqS_def by auto 


lemma inv_CurCmd' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_CurCmd N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_CurCmd_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
    subgoal unfolding n_RecvGntEs_def  by auto
    subgoal unfolding n_RecvGntSs_def   by auto
    subgoal unfolding  n_SendGntEs_def by auto 
    subgoal unfolding  n_SendGntSs_def by auto  
    subgoal unfolding   n_RecvInvAck12s_def
      using n_RecvInvAck12_type_inv_CurCmd by auto  
    subgoal
      using   n_RecvInvAck2s_def by auto
    subgoal
      using  n_SendInvAck1s_def by auto  
    subgoal
      using n_SendInvAck2s_def by auto 
    subgoal
      using  n_SendInv1s_def by auto  
    subgoal
      using n_SendInv2s_def by auto 
    subgoal
      using  n_RecvReqEs_def by auto  
    subgoal
      using n_RecvReqSs_def by auto 
    subgoal
      using n_SendReqE1s_def by auto 
    subgoal
      using n_SendReqE2s_def by auto  
    subgoal
      using n_SendReqSs_def by auto 

    
    done
  done
   

lemma inv_CurCmd'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N \<longrightarrow> i \<le> N \<longrightarrow> isEnumVal s (Ident ''CurCmd'')"
  using inv_CurCmd' unfolding type_inv_CurCmd_def Empty_def ReqS_def
     ReqE_def Inv_def InvAck_def GntS_def GntE_def
  by (metis  assms getValueType.simps(1) isEnumVal_def typeOf_def)   






 
definition type_inv_ExGntd :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_ExGntd N s = 
(\<forall>i. i \<le> N \<longrightarrow> s ((Ident ''ExGntd'')) = true  \<or> s (Ident ''ExGntd'') = false)
 "

lemma n_RecvGntE_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_RecvGntE i)) sk)"
  unfolding type_inv_ExGntd_def n_RecvGntE_def by auto

lemma n_RecvGntS_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_RecvGntS i)) sk)"
  unfolding type_inv_ExGntd_def n_RecvGntS_def by auto


lemma n_SendGntE_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_SendGntE N i)) sk)"
  unfolding type_inv_ExGntd_def n_SendGntE_def by auto

lemma n_SendGntS_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_SendGntS  i)) sk)"
  unfolding type_inv_ExGntd_def n_SendGntS_def by auto

lemma n_RecvInvAck12_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
  type_inv_ExGntd N 
  (trans1 (act ( (strengthenRule2  (constrInvByExcl pair1 i N) (n_RecvInvAck1 i)))) sk)"
  unfolding type_inv_ExGntd_def n_RecvInvAck1_def apply (auto simp add:strengthenRule2.simps )
  done

lemma n_RecvInvAck2_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
  type_inv_ExGntd N 
  (trans1 (act (  (n_RecvInvAck2 i))) sk)"
  unfolding type_inv_ExGntd_def n_RecvInvAck2_def apply (auto simp add:strengthenRule2.simps )
  done
lemma n_SendInvAck1_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_SendInvAck1 i)) sk)"
  unfolding type_inv_ExGntd_def n_SendInvAck1_def by auto

lemma n_SendInvAck2_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_SendInvAck2 i)) sk)"
  unfolding type_inv_ExGntd_def n_SendInvAck2_def by auto

lemma n_SendInv1_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_SendInv1 i)) sk)"
  unfolding type_inv_ExGntd_def n_SendInv1_def by auto

lemma n_SendInv2_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_SendInv2 i)) sk)"
  unfolding type_inv_ExGntd_def n_SendInv2_def by auto


lemma n_RecvReqE_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_RecvReqE N i)) sk)"
  unfolding type_inv_ExGntd_def n_RecvReqE_def by auto 

lemma n_RecvReqS_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_RecvReqS N i)) sk)"
  unfolding type_inv_ExGntd_def n_RecvReqS_def by auto

lemma n_SendReqE1_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_SendReqE1  i)) sk)"
  unfolding type_inv_ExGntd_def n_SendReqE1_def by auto

lemma n_SendReqE2_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_SendReqE2  i)) sk)"
  unfolding type_inv_ExGntd_def n_SendReqE2_def by auto

lemma n_SendReqS_type_inv_ExGntd [intro]:
  "type_inv_ExGntd N sk \<Longrightarrow> i \<le> N \<Longrightarrow> type_inv_ExGntd N (trans1 (act (n_SendReqS  i)) sk)"
  unfolding type_inv_ExGntd_def n_SendReqS_def by auto 


lemma inv_ExGntd' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_ExGntd N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_ExGntd_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
    subgoal unfolding n_RecvGntEs_def  by auto
    subgoal unfolding n_RecvGntSs_def   by auto
    subgoal unfolding  n_SendGntEs_def by auto 
    subgoal unfolding  n_SendGntSs_def by auto  
    subgoal unfolding   n_RecvInvAck12s_def
      using n_RecvInvAck12_type_inv_ExGntd by auto  
    subgoal
      using   n_RecvInvAck2s_def by auto
    subgoal
      using  n_SendInvAck1s_def by auto  
    subgoal
      using n_SendInvAck2s_def by auto 
    subgoal
      using  n_SendInv1s_def by auto  
    subgoal
      using n_SendInv2s_def by auto 
    subgoal
      using  n_RecvReqEs_def by auto  
    subgoal
      using n_RecvReqSs_def by auto 
    subgoal
      using n_SendReqE1s_def by auto 
    subgoal
      using n_SendReqE2s_def by auto  
    subgoal
      using n_SendReqSs_def by auto 

    
    done
  done
   

lemma inv_ExGntd'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N \<longrightarrow> i \<le> N \<longrightarrow> isBoolVal s (Ident ''ExGntd'')"
  using inv_ExGntd' unfolding type_inv_ExGntd_def true_def false_def
  using assms by fastforce    


lemma rule2'IsSym:
  "symProtRules' N (rules2' N)"
  unfolding rules2'_def
  apply (intro symProtRulesUnion)
  using n_RecvGntEsIsSym apply blast
  using n_RecvGntSsIsSym apply blast
  using n_SendGntEsIsSym apply blast
  using n_SendGntSsIsSym apply blast
  using n_RecvInvAck12_ref' n_RecvInvAck12s_def symParaRuleInfSymRuleSet wellFormedSendReqE2(1) apply auto[1]
  using n_RecvInvAck2sIsSym apply blast
  using n_SendInvAck1sIsSym apply blast
  using n_SendInvAck2sIsSym apply blast
  using n_SendInv1sIsSym apply blast
  using n_SendInv2sIsSym apply blast
  using n_RecvReqEsIsSym apply blast
  using n_RecvReqSsIsSym apply blast
  using n_SendReqE1sIsSym apply blast
  using n_SendReqE2sIsSym apply blast
  using n_SendReqSsIsSym by blast
  

lemma absProtSim:
  assumes a2: "M < N"
    and a3: "M = 1"
    and a4: "\<forall>i f s.
       f \<in> F \<longrightarrow>
       reachableUpTo {f'. \<exists>f. f \<in> (set (allInitSpecs N))\<and> f' = absTransfForm M f}
        (absRules M) i s \<longrightarrow>
       formEval (constrInv f 0 1) s"
  shows "\<forall>f s. f \<in> constrInvByExcls F N \<longrightarrow> 
    reachableUpTo (set (allInitSpecs N)) (rules' N) i s \<longrightarrow> formEval f s"
proof (rule_tac ?rs2.0="rules2' N" in CMP)
  show "\<And>r. r \<in> rules' N \<longrightarrow> wellFormedRule N r"
    apply (auto simp add: rules'_def 
          n_RecvGntEs_def symRecvGntE(2)
   n_RecvGntSs_def n_RecvGntS_def  symRecvGntS(2)
   n_SendGntEs_def n_SendGntE_def symSendGntE(2)
   n_SendGntSs_def n_SendGntS_def symSendGntS(2)
   n_RecvInvAck1s_def n_RecvInvAck1_def symRecvInvAck1(2)
   n_RecvInvAck2s_def n_RecvInvAck2_def symRecvInvAck2(2)
   n_SendInvAck1s_def n_SendInvAck1_def symSendInvAck1(2)
   n_SendInvAck2s_def n_SendInvAck2_def symSendInvAck2(2)
   n_SendInv1s_def n_SendInv1_def symSendInv1(2)
   n_SendInv2s_def n_SendInv2_def symSendInv2(2)
   n_RecvReqEs_def n_RecvReqE_def symRecvReqE(2)
    n_RecvReqSs_def n_RecvReqS_def symRecvReqS(2)
   n_SendReqE1s_def n_SendReqE1_def symSendReqE1(2)
   n_SendReqE2s_def n_SendReqE2_def symSendReqE2(2)
   n_SendReqSs_def n_SendReqS_def symSendReqS(2))
    by (metis act.simps symRecvGntE(2) wellFormedRule.elims(3))
next
  show "\<forall>f. f \<in> F \<longrightarrow> symPair f N"
    by (auto simp add: F_def pair1_def symParamForm_def)
next
  show "symProtRules' N (rules' N)"
    using rulesSym' by blast
next
  show "symPredSet' N (set (allInitSpecs N))"
  proof -
    have b1:"(set (allInitSpecs N)) =
      {(initSpec0 N)} \<union>
    {(initSpec1 N)}\<union>
    {(initSpec2 N)}\<union>
    {(initSpec3 N)}\<union>
    {(initSpec4 N)}\<union>
    {(initSpec5 N)}\<union>
    {initSpec6} \<union>
    {initSpec7}" (is "?LHS=?RHS")
      using allInitSpecs_def by auto
    have b2:"symPredSet' N ?RHS"
      using symPreds by blast
    show "symPredSet' N (set (allInitSpecs N))"
      using b1 b2 by auto  
  qed    
next
  show "M \<le> N"
    using a2 by auto
next
  show "\<forall>s i f. reachableUpTo ((set (allInitSpecs N))) (rules2' N) i s \<longrightarrow>
        f \<in> F \<longrightarrow> (\<forall>v. v \<in> varOfForm (constrInv f 0 1) \<longrightarrow> s v = abs1 M s v)"
    apply auto
    using inv_ExGntd''  inv_CurCmd'' inv_Cache_State'' inv_Chan2_Cmd'' inv_Chan3_Cmd'' 
      enumValAbsRemainSame boolValAbsRemainSame
    unfolding F_def pair1_def using a2 a3 apply auto
    apply (metis absTransfVar.simps(1) less_imp_le varType.distinct(3))
    by (metis absTransfVar.simps(1) less_imp_le varType.distinct(3))
next
  show "\<forall>r'. r' \<in> rules2' N \<longrightarrow>
         (\<exists>r f i. f \<in> F \<and> r \<in> rules' N \<and> i \<le> N \<and> r' = strengthenRule2 (constrInvByExcl f i N) r) \<or>
         r' \<in> rules' N"
  proof -
    have "\<exists>r f i. f \<in> F \<and> r \<in> rules' N \<and> i \<le> N \<and> r' = strengthenRule2 (constrInvByExcl f i N) r"
      if "r' \<in> n_RecvInvAck12s N" for r'
      using that apply (auto simp add: n_RecvInvAck12s_def)
      subgoal for i
        apply (rule exI[where x="n_RecvInvAck1   i"])
        unfolding F_def pair1_def 
        apply (auto simp add: constrInvByExcl_def strengthenRule2.simps 
             n_RecvInvAck12s_def n_RecvInvAck1_def rules'_def  )
        by (simp add: false_def n_RecvInvAck1_def n_RecvInvAck1s_def)
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
    have "\<exists>f. f \<in> constrInvByExcls F N \<and> strengthenRule2 f r \<in>
    rules2' N"
      if "r \<in> n_RecvInvAck1s N" for r
      using that apply (auto simp add: n_RecvInvAck1s_def)
      subgoal for i
        apply (rule exI[where x="constrInvByExcl pair1 i N"])
        by (auto simp add: F_def pair1_def constrInvByExcl_def strengthenRule2.simps n_RecvInvAck12s_def)
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
       reachableUpTo {f'. \<exists>f. f \<in>set (allInitSpecs N) \<and> f' = absTransfForm M f}
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

