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
    let g = IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const GntE in
    let a = assign (Para ''Cache.State'' i, Const E) ||
            assign (Para ''Cache.Data'' i, IVar (Para ''Chan2.Data'' i)) ||
            assign (Para ''Chan2.Cmd'' i, Const Empty) in
      (guard g a)"

lemma absRecvGntE:
  "absTransfForm M (pre (n_RecvGntE i)) =
    (if i > M then dontCareForm
     else IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const GntE)"
  by (auto simp add: n_RecvGntE_def)

definition n_RecvGntS :: "nat \<Rightarrow> rule" where
  "n_RecvGntS i \<equiv>
    let g = IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const GntS in
    let a = assign (Para ''Cache.State'' i, Const S) ||
            assign (Para ''Cache.Data'' i, IVar (Para ''Chan2.Data'' i)) ||
            assign (Para ''Chan2.Cmd'' i, Const Empty) in
      (guard g a)"

lemma absRecvGntS:
  "absTransfForm M (pre (n_RecvGntS i)) =
    (if i > M then dontCareForm
     else IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const GntS)"
  by (auto simp add: n_RecvGntS_def)

definition n_SendGntE:: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_SendGntE N i \<equiv>
    let g = IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE \<and>\<^sub>f
            IVar (Ident ''CurPtr'') =\<^sub>f Const (index i) \<and>\<^sub>f
            IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
            IVar (Ident ''ExGntd'') =\<^sub>f Const false \<and>\<^sub>f
            (\<forall>\<^sub>fj. IVar (Para ''ShrSet'' j) =\<^sub>f Const false) N in
    let a = assign (Para ''Chan2.Cmd'' i, Const GntE) ||
            assign (Para ''Chan2.Data'' i, IVar (Ident ''MemData'')) ||
            assign (Para ''ShrSet'' i, Const true) ||
            assign (Ident ''ExGntd'', Const true) ||
            assign (Ident ''CurCmd'', Const Empty) in
      (guard g a)"
  
lemma absSendGntE:
  "absTransfForm M (pre (n_SendGntE N i)) =
    (if i > M then
       IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE \<and>\<^sub>f
       IVar (Ident ''CurPtr'') =\<^sub>f Const (index (M+1)) \<and>\<^sub>f
       IVar (Ident ''ExGntd'') =\<^sub>f Const false \<and>\<^sub>f
       (\<forall>\<^sub>fj. IVar (Para ''ShrSet'' j) =\<^sub>f Const false) M
     else
       IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE \<and>\<^sub>f
       IVar (Ident ''CurPtr'') =\<^sub>f Const (index i) \<and>\<^sub>f
       IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
       IVar (Ident ''ExGntd'') =\<^sub>f Const false \<and>\<^sub>f
       (\<forall>\<^sub>fj. IVar (Para ''ShrSet'' j) =\<^sub>f Const false) M)"
  unfolding n_SendGntE_def by auto

definition n_SendGntS :: "nat \<Rightarrow> rule" where
  "n_SendGntS i \<equiv>
    let g = IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
            IVar (Ident ''CurPtr'') =\<^sub>f Const (index i) \<and>\<^sub>f
            IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
            IVar (Ident ''ExGntd'') =\<^sub>f Const false in
    let a = assign (Para ''Chan2.Cmd'' i, Const GntS) ||
            assign (Para ''Chan2.Data'' i, IVar (Ident ''MemData'')) ||
            assign (Para ''ShrSet'' i, Const true) ||
            assign (Ident ''CurCmd'', Const Empty) in
      (guard g a)"

lemma absSendGntS:
  "absTransfForm M (pre (n_SendGntS i)) =
    (if i > M then
       IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
       IVar (Ident ''CurPtr'') =\<^sub>f Const (index (M+1)) \<and>\<^sub>f
       IVar (Ident ''ExGntd'') =\<^sub>f Const false
     else
       IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
       IVar (Ident ''CurPtr'') =\<^sub>f Const (index i) \<and>\<^sub>f
       IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
       IVar (Ident ''ExGntd'') =\<^sub>f Const false)"
  unfolding n_SendGntS_def by auto

definition n_RecvInvAck1 :: "nat \<Rightarrow> rule" where
  "n_RecvInvAck1 i \<equiv>
    let g = IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
            \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
            IVar (Ident ''ExGntd'') =\<^sub>f Const true in
    let a = assign (Para ''Chan3.Cmd'' i, Const Empty) ||
            assign (Para ''ShrSet'' i, Const false) ||
            assign (Ident ''ExGntd'', Const false) ||
            assign (Ident ''MemData'', IVar (Para ''Chan3.Data'' i)) in
      (guard g a)"

lemma absRecvInvAck1:
  "absTransfForm M (pre (n_RecvInvAck1 i)) =
    (if i > M then
       \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
       IVar (Ident ''ExGntd'') =\<^sub>f Const true
     else
       IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
       \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
       IVar (Ident ''ExGntd'') =\<^sub>f Const true)"
  unfolding n_RecvInvAck1_def by auto

definition n_RecvInvAck2 :: "nat \<Rightarrow> rule" where
  "n_RecvInvAck2 i \<equiv>
    let g = IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
            \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
            \<not>\<^sub>f IVar (Ident ''ExGntd'') =\<^sub>f Const true in
    let a = assign (Para ''Chan3.Cmd'' i, Const Empty) ||
            assign (Para ''ShrSet'' i, Const false) in
      (guard g a)"

lemma absRecvInvAck2:
  "absTransfForm M (pre (n_RecvInvAck2 i)) =
    (if i > M then
       \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
       \<not>\<^sub>f IVar (Ident ''ExGntd'') =\<^sub>f Const true
     else
       IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
       \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
       \<not>\<^sub>f IVar (Ident ''ExGntd'') =\<^sub>f Const true)"
  unfolding n_RecvInvAck2_def by auto

definition n_SendInvAck1 :: "nat \<Rightarrow> rule" where
  "n_SendInvAck1 i \<equiv>
    let g = IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Inv \<and>\<^sub>f
            IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
            IVar (Para ''Cache.State'' i) =\<^sub>f Const E in
    let a = assign (Para ''Chan2.Cmd'' i, Const Empty) ||
            assign (Para ''Chan3.Cmd'' i, Const InvAck) ||
            assign (Para ''Chan3.Data'' i, IVar (Para ''Cache.Data'' i)) ||
            assign (Para ''Cache.State'' i, Const I) in
      (guard g a)"

lemma absSendInvAck1:
  "absTransfForm M (pre (n_SendInvAck1 i)) =
    (if i > M then
       dontCareForm
     else
       IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Inv \<and>\<^sub>f
       IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
       IVar (Para ''Cache.State'' i) =\<^sub>f Const E)"
  unfolding n_SendInvAck1_def by auto

definition n_SendInvAck2 :: "nat \<Rightarrow> rule" where
  "n_SendInvAck2 i \<equiv>
    let g = IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Inv \<and>\<^sub>f
            IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
            \<not>\<^sub>f IVar (Para ''Cache.State'' i) =\<^sub>f Const E in
    let a = assign (Para ''Chan2.Cmd'' i, Const Empty) ||
            assign (Para ''Chan3.Cmd'' i, Const InvAck) ||
            assign (Para ''Cache.State'' i, Const I) in
      (guard g a)"

lemma absSendInvAck2:
  "absTransfForm M (pre (n_SendInvAck2 i)) =
    (if i > M then
       dontCareForm
     else
       IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Inv \<and>\<^sub>f
       IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
       \<not>\<^sub>f IVar (Para ''Cache.State'' i) =\<^sub>f Const E)"
  unfolding n_SendInvAck2_def by auto

definition n_SendInv1 :: "nat \<Rightarrow> rule" where
  "n_SendInv1 i \<equiv>
    let g = IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
            IVar (Para ''InvSet'' i) =\<^sub>f Const true \<and>\<^sub>f
            IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE in
    let a = assign (Para ''Chan2.Cmd'' i, Const Inv) ||
            assign (Para ''InvSet'' i, Const false) in
      (guard g a)"

lemma absSendInv1:
  "absTransfForm M (pre (n_SendInv1 i)) =
    (if i > M then
       IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE
     else
       IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
       IVar (Para ''InvSet'' i) =\<^sub>f Const true \<and>\<^sub>f
       IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE)"
  unfolding n_SendInv1_def by auto

definition n_SendInv2 :: "nat \<Rightarrow> rule" where
  "n_SendInv2 i \<equiv>
    let g = IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
            IVar (Para ''InvSet'' i) =\<^sub>f Const true \<and>\<^sub>f
            IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
            IVar (Ident ''ExGntd'') =\<^sub>f Const true in
    let a = assign (Para ''Chan2.Cmd'' i, Const Inv) ||
            assign (Para ''InvSet'' i, Const false) in
      (guard g a)"

lemma absSendInv2:
  "absTransfForm M (pre (n_SendInv2 i)) =
    (if i > M then
       IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
       IVar (Ident ''ExGntd'') =\<^sub>f Const true
     else
       IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
       IVar (Para ''InvSet'' i) =\<^sub>f Const true \<and>\<^sub>f
       IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
       IVar (Ident ''ExGntd'') =\<^sub>f Const true)"
  unfolding n_SendInv2_def by auto

definition n_RecvReqE :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_RecvReqE N i \<equiv>
    let g = IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
            IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const ReqE in
    let a = assign (Ident ''CurCmd'', Const ReqE) ||
            assign (Ident ''CurPtr'', Const (index i)) ||
            assign (Para ''Chan1.Cmd'' i, Const Empty) ||
            forallStm (\<lambda>j. assign (Para ''InvSet'' j, IVar (Para ''ShrSet'' j))) N in
      (guard g a)"

lemma absRecvReqE:
  "absTransfForm M (pre (n_RecvReqE N i)) =
    (if i > M then
       IVar (Ident ''CurCmd'') =\<^sub>f Const Empty
     else
       IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
       IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const ReqE)"
  unfolding n_RecvReqE_def by auto

definition n_RecvReqS :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_RecvReqS N i \<equiv>
    let g = IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
            IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const ReqS in
    let a = assign (Ident ''CurCmd'', Const ReqS) ||
            assign (Ident ''CurPtr'', Const (index i)) ||
            assign (Para ''Chan1.Cmd'' i, Const Empty) ||
            forallStm (\<lambda>j. assign (Para ''InvSet'' j, IVar (Para ''ShrSet'' j))) N in
      (guard g a)"

lemma absRecvReqS:
  "absTransfForm M (pre (n_RecvReqS N i)) =
    (if i > M then
       IVar (Ident ''CurCmd'') =\<^sub>f Const Empty
     else
       IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
     IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const ReqS)"
  unfolding n_RecvReqS_def by auto

definition n_SendReqE1 :: "nat \<Rightarrow> rule" where
  "n_SendReqE1 i \<equiv>
    let g = IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
            IVar (Para ''Cache.State'' i) =\<^sub>f Const I in
    let a = assign (Para ''Chan1.Cmd'' i, Const ReqE) in
      (guard g a)"

lemma absSendReqE1:
  "absTransfForm M (pre (n_SendReqE1 i)) =
    (if i > M then
       dontCareForm
     else
       IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
       IVar (Para ''Cache.State'' i) =\<^sub>f Const I)"
  unfolding n_SendReqE1_def by auto

definition n_SendReqE2 :: "nat \<Rightarrow> rule" where
  "n_SendReqE2 i \<equiv>
    let g = IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
            IVar (Para ''Cache.State'' i) =\<^sub>f Const S in
    let a = assign (Para ''Chan1.Cmd'' i, Const ReqE) in
      (guard g a)"

lemma absSendReqE2:
  "absTransfForm M (pre (n_SendReqE2 i)) =
    (if i > M then
       dontCareForm
     else
       IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
       IVar (Para ''Cache.State'' i) =\<^sub>f Const S)"
  unfolding n_SendReqE2_def by auto

definition n_SendReqS :: "nat \<Rightarrow> rule" where
  "n_SendReqS i \<equiv>
    let g = IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
            IVar (Para ''Cache.State'' i) =\<^sub>f Const I in
    let a = assign (Para ''Chan1.Cmd'' i, Const ReqS) in
      (guard g a)"

lemma absSendReqS:
  "absTransfForm M (pre (n_SendReqS i)) =
    (if i > M then
       dontCareForm
     else
       IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
       IVar (Para ''Cache.State'' i) =\<^sub>f Const I)"
  unfolding n_SendReqS_def by auto

definition n_Store :: "nat \<Rightarrow> rule" where
  "n_Store i \<equiv>
    let g = IVar (Para ''Cache.State'' i) =\<^sub>f Const E in
    let a = assign (Para ''Cache.Data'' i, IVar (Ident ''d'')) ||
            assign (Ident ''AuxData'', IVar (Ident ''d'')) in
      (guard g a)"

definition rules::"nat \<Rightarrow> rule set" where
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
    (\<exists>i. i\<le>N \<and> r=n_SendReqS i) \<or>
    (\<exists>i. i\<le>N \<and> r=n_Store i)
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

definition invAux_1 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where
  "invAux_1 N i \<equiv>
     IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
     \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
     IVar (Ident ''ExGntd'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
     forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Cache.State'' j) =\<^sub>f Const E) i N \<and>\<^sub>f
     forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE) i N \<and>\<^sub>f
     forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck) i N"

definition n_RecvInvAck1_st :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_RecvInvAck1_st N i = strengthenRule2 (invAux_1 N i) (n_RecvInvAck1 i)"

definition n_RecvInvAck1_st_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_RecvInvAck1_st_ref N i \<equiv>
    let g =  (IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
              \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
              IVar (Ident ''ExGntd'') =\<^sub>f Const true) \<and>\<^sub>f
             forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Cache.State'' j) =\<^sub>f Const E) i N \<and>\<^sub>f
             forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE) i N \<and>\<^sub>f
             forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck) i N in
    let a = assign (Para ''Chan3.Cmd'' i, Const Empty) ||
            assign (Para ''ShrSet'' i, Const false) ||
            assign (Ident ''ExGntd'', Const false) ||
            assign (Ident ''MemData'', IVar (Para ''Chan3.Data'' i)) in
      (guard g a)"

lemma n_RecvInvAck1_stEq:
  "n_RecvInvAck1_st N i = n_RecvInvAck1_st_ref N i"
  by (auto simp add: n_RecvInvAck1_st_def invAux_1_def n_RecvInvAck1_def n_RecvInvAck1_st_ref_def)

lemma absRecvInvAck1_st:
  "absTransfForm M (pre (n_RecvInvAck1_st_ref N i)) =
    (if i > M then
       (\<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
        IVar (Ident ''ExGntd'') =\<^sub>f Const true) \<and>\<^sub>f
       (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''Cache.State'' j) =\<^sub>f Const E) M \<and>\<^sub>f
       (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE) M \<and>\<^sub>f
       (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck) M
     else
       IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
       \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
       IVar (Ident ''ExGntd'') =\<^sub>f Const true)"
  unfolding n_RecvInvAck1_st_ref_def by auto


end
