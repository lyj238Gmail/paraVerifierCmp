theory ABS_german_1
  imports CMP
begin

subsection \<open>Definitions\<close>

text \<open>type definitions \<close>

definition I :: scalrValueType where [simp]: "I\<equiv> enum ''control'' ''I''"
definition S :: scalrValueType where [simp]: "S\<equiv> enum ''control'' ''S''"
definition E :: scalrValueType where [simp]: "E\<equiv> enum ''control'' ''E''"
definition Empty :: scalrValueType where [simp]: "Empty\<equiv> enum ''control'' ''Empty''"
definition ReqS :: scalrValueType where [simp]: "ReqS\<equiv> enum ''control'' ''ReqS''"
definition ReqE :: scalrValueType where [simp]: "ReqE\<equiv> enum ''control'' ''ReqE''"
definition Inv :: scalrValueType where [simp]: "Inv\<equiv> enum ''control'' ''Inv''"
definition InvAck :: scalrValueType where [simp]: "InvAck\<equiv> enum ''control'' ''InvAck''"
definition GntS :: scalrValueType where [simp]: "GntS\<equiv> enum ''control'' ''GntS''"
definition GntE :: scalrValueType where [simp]: "GntE\<equiv> enum ''control'' ''GntE''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"

text \<open>initial state \<close>

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N\<equiv> (\<forall>\<^sub>fi. (IVar (Para (''Chan1.Cmd'') i)) =\<^sub>f  (Const Empty) ) N "

definition initSpec1::"nat \<Rightarrow> formula" where [simp]:
"initSpec1 N\<equiv> (\<forall>\<^sub>fi. (IVar (Para (''Chan2.Cmd'') i)) =\<^sub>f  (Const Empty) ) N "

definition initSpec2::"nat \<Rightarrow> formula" where [simp]:
"initSpec2 N\<equiv> (\<forall>\<^sub>fi. (IVar (Para (''Chan3.Cmd'') i)) =\<^sub>f  (Const Empty) ) N "

definition initSpec3::"nat \<Rightarrow> formula" where [simp]:
"initSpec3 N\<equiv> (\<forall>\<^sub>fi. (IVar (Para (''Cache.State'') i)) =\<^sub>f  (Const I) ) N "

definition initSpec4::"nat \<Rightarrow> formula" where [simp]:
"initSpec4 N\<equiv> (\<forall>\<^sub>fi. (IVar (Para (''InvSet'') i)) =\<^sub>f  (Const false) ) N "

definition initSpec5::"nat \<Rightarrow> formula" where [simp]:
"initSpec5 N\<equiv> (\<forall>\<^sub>fi. (IVar (Para (''ShrSet'') i)) =\<^sub>f  (Const false) ) N "

definition initSpec6::"nat \<Rightarrow> formula" where [simp]:
"initSpec6 N \<equiv> (IVar (Ident ''ExGntd'')) =\<^sub>f  (Const false) "

definition initSpec7::"nat \<Rightarrow> formula" where [simp]:
"initSpec7 N \<equiv> (IVar (Ident ''CurCmd'')) =\<^sub>f  (Const Empty) "

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
unfolding initSpec0_def initSpec1_def initSpec2_def initSpec3_def initSpec4_def initSpec5_def initSpec6_def initSpec7_def 
using assms by auto


definition allInitSpecs::"nat \<Rightarrow> formula list" where
"allInitSpecs N \<equiv> [
(initSpec0 N),
(initSpec1 N),
(initSpec2 N),
(initSpec3 N),
(initSpec4 N),
(initSpec5 N),
(initSpec6),
(initSpec7)
]"
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
  "symPredSet' N (    {(initSpec0 N)} \<union>
    {(initSpec1 N)} \<union>
    {(initSpec2 N)} \<union>
    {(initSpec3 N)} \<union>
    {(initSpec4 N)} \<union>
    {(initSpec5 N)} \<union>
    {initSpec6} \<union>
    {initSpec7})"

  apply (meson symPreds0 symPreds1 symPreds2 symPreds3 symPreds4 symPreds5 symPreds6 symPreds7 
symPredsUnion)
  done

lemma symPreds':
"symPredSet' N (set (allInitSpecs N))"
  proof -
    have b1:"(set (allInitSpecs N)) =
    {(initSpec0 N)}\<union>
    {(initSpec1 N)}\<union>
    {(initSpec2 N)}\<union>
    {(initSpec3 N)}\<union>
    {(initSpec4 N)}\<union>
    {(initSpec5 N)}\<union>
    {(initSpec6 N)}\<union>
    {(initSpec7 N)}" (is "?LHS=?RHS")
      using allInitSpecs_def by auto
    have b2:"symPredSet' N ?RHS"
      using symPreds by blast
    show "symPredSet' N (set (allInitSpecs N))"
      using b1 b2 by auto
  qed

definition n_RecvGntE1::"nat \<Rightarrow> rule" where 
"n_RecvGntE1  i\<equiv>
(IVar (Para (''Chan2.Cmd'') i)) =\<^sub>f  (Const GntE) 
   \<triangleright>
(assign (Para (''Cache.State'') i, (Const E)))||
(assign (Para (''Cache.Data'') i, (IVar (Para (''Chan2.Data'') i))))||
(assign (Para (''Chan2.Cmd'') i, (Const Empty)))"

lemma symRecvGntE1:
  "symParamRule N n_RecvGntE1"
  "wellFormedStatement N (act (n_RecvGntE1 i))"
  "absTransfRule M (n_RecvGntE1 i) = (if i \<le> M then n_RecvGntE1 i else chaos
\<triangleright> skip)"
  unfolding n_RecvGntE1_def symParamRule_def by auto

definition n_RecvGntS2::"nat \<Rightarrow> rule" where 
"n_RecvGntS2  i\<equiv>
(IVar (Para (''Chan2.Cmd'') i)) =\<^sub>f  (Const GntS) 
   \<triangleright>
(assign (Para (''Cache.State'') i, (Const S)))||
(assign (Para (''Cache.Data'') i, (IVar (Para (''Chan2.Data'') i))))||
(assign (Para (''Chan2.Cmd'') i, (Const Empty)))"

lemma symRecvGntS2:
  "symParamRule N n_RecvGntS2"
  "wellFormedStatement N (act (n_RecvGntS2 i))"
  "absTransfRule M (n_RecvGntS2 i) = (if i \<le> M then n_RecvGntS2 i else chaos
\<triangleright> skip)"
  unfolding n_RecvGntS2_def symParamRule_def by auto

definition n_SendGntE3::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_SendGntE3  i N\<equiv>
(IVar (Ident ''CurCmd''))  =\<^sub>f (Const ReqE)  \<and>\<^sub>f
(IVar (Ident ''CurPtr''))  =\<^sub>f (Const (index i))  \<and>\<^sub>f
(IVar (Para (''Chan2.Cmd'') i)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
(IVar (Ident ''ExGntd''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(\<forall>\<^sub>fj. (IVar (Para (''ShrSet'') j)) =\<^sub>f  (Const false) )) M
   \<triangleright>
(assign (Para (''Chan2.Cmd'') i, (Const GntE)))||
(assign (Para (''Chan2.Data'') i, (IVar (Ident ''MemData''))))||
(assign (Para (''ShrSet'') i, (Const true)))||
(assign ((Ident ''ExGntd''), (Const true)))||
(assign ((Ident ''CurCmd''), (Const Empty)))"

lemma symSendGntE3:
  "symParamRule N n_SendGntE3"
  "wellFormedStatement N (act (n_SendGntE3 i))"
  "absTransfRule M (n_SendGntE3 i) = (if i \<le> M then n_SendGntE3 i else chaos
\<triangleright> skip)"
  unfolding n_SendGntE3_def symParamRule_def by auto

definition n_SendGntS4::"nat \<Rightarrow> rule" where 
"n_SendGntS4  i\<equiv>
(IVar (Ident ''CurCmd''))  =\<^sub>f (Const ReqS)  \<and>\<^sub>f
(IVar (Ident ''CurPtr''))  =\<^sub>f (Const (index i))  \<and>\<^sub>f
(IVar (Para (''Chan2.Cmd'') i)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
(IVar (Ident ''ExGntd''))  =\<^sub>f (Const false) 
   \<triangleright>
(assign (Para (''Chan2.Cmd'') i, (Const GntS)))||
(assign (Para (''Chan2.Data'') i, (IVar (Ident ''MemData''))))||
(assign (Para (''ShrSet'') i, (Const true)))||
(assign ((Ident ''CurCmd''), (Const Empty)))"

lemma symSendGntS4:
  "symParamRule N n_SendGntS4"
  "wellFormedStatement N (act (n_SendGntS4 i))"
  "absTransfRule M (n_SendGntS4 i) = (if i \<le> M then n_SendGntS4 i else chaos
\<triangleright> skip)"
  unfolding n_SendGntS4_def symParamRule_def by auto

definition n_RecvInvAck5::"nat \<Rightarrow> rule" where 
"n_RecvInvAck5  i\<equiv>
(IVar (Para (''Chan3.Cmd'') i)) =\<^sub>f  (Const InvAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''CurCmd'')) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
(IVar (Ident ''ExGntd''))  =\<^sub>f (Const true) 
   \<triangleright>
(assign (Para (''Chan3.Cmd'') i, (Const Empty)))||
(assign (Para (''ShrSet'') i, (Const false)))||
(assign ((Ident ''ExGntd''), (Const false)))||
(assign ((Ident ''MemData''), (IVar (Para (''Chan3.Data'') i))))"

lemma symRecvInvAck5:
  "symParamRule N n_RecvInvAck5"
  "wellFormedStatement N (act (n_RecvInvAck5 i))"
  "absTransfRule M (n_RecvInvAck5 i) = (if i \<le> M then n_RecvInvAck5 i else chaos
\<triangleright> skip)"
  unfolding n_RecvInvAck5_def symParamRule_def by auto

definition n_RecvInvAck6::"nat \<Rightarrow> rule" where 
"n_RecvInvAck6  i\<equiv>
(IVar (Para (''Chan3.Cmd'') i)) =\<^sub>f  (Const InvAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''CurCmd'')) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''ExGntd'')) =\<^sub>f  (Const true) 
   \<triangleright>
(assign (Para (''Chan3.Cmd'') i, (Const Empty)))||
(assign (Para (''ShrSet'') i, (Const false)))"

lemma symRecvInvAck6:
  "symParamRule N n_RecvInvAck6"
  "wellFormedStatement N (act (n_RecvInvAck6 i))"
  "absTransfRule M (n_RecvInvAck6 i) = (if i \<le> M then n_RecvInvAck6 i else chaos
\<triangleright> skip)"
  unfolding n_RecvInvAck6_def symParamRule_def by auto

definition n_SendInvAck7::"nat \<Rightarrow> rule" where 
"n_SendInvAck7  i\<equiv>
(IVar (Para (''Chan2.Cmd'') i)) =\<^sub>f  (Const Inv)  \<and>\<^sub>f
(IVar (Para (''Chan3.Cmd'') i)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
(IVar (Para (''Cache.State'') i)) =\<^sub>f  (Const E) 
   \<triangleright>
(assign (Para (''Chan2.Cmd'') i, (Const Empty)))||
(assign (Para (''Chan3.Cmd'') i, (Const InvAck)))||
(assign (Para (''Chan3.Data'') i, (IVar (Para (''Cache.Data'') i))))||
(assign (Para (''Cache.State'') i, (Const I)))"

lemma symSendInvAck7:
  "symParamRule N n_SendInvAck7"
  "wellFormedStatement N (act (n_SendInvAck7 i))"
  "absTransfRule M (n_SendInvAck7 i) = (if i \<le> M then n_SendInvAck7 i else chaos
\<triangleright> skip)"
  unfolding n_SendInvAck7_def symParamRule_def by auto

definition n_SendInvAck8::"nat \<Rightarrow> rule" where 
"n_SendInvAck8  i\<equiv>
(IVar (Para (''Chan2.Cmd'') i)) =\<^sub>f  (Const Inv)  \<and>\<^sub>f
(IVar (Para (''Chan3.Cmd'') i)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Cache.State'') i)) =\<^sub>f  (Const E) 
   \<triangleright>
(assign (Para (''Chan2.Cmd'') i, (Const Empty)))||
(assign (Para (''Chan3.Cmd'') i, (Const InvAck)))||
(assign (Para (''Cache.State'') i, (Const I)))"

lemma symSendInvAck8:
  "symParamRule N n_SendInvAck8"
  "wellFormedStatement N (act (n_SendInvAck8 i))"
  "absTransfRule M (n_SendInvAck8 i) = (if i \<le> M then n_SendInvAck8 i else chaos
\<triangleright> skip)"
  unfolding n_SendInvAck8_def symParamRule_def by auto

definition n_SendInv9::"nat \<Rightarrow> rule" where 
"n_SendInv9  i\<equiv>
(IVar (Para (''Chan2.Cmd'') i)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
(IVar (Para (''InvSet'') i)) =\<^sub>f  (Const true)  \<and>\<^sub>f
(IVar (Ident ''CurCmd''))  =\<^sub>f (Const ReqE) 
   \<triangleright>
(assign (Para (''Chan2.Cmd'') i, (Const Inv)))||
(assign (Para (''InvSet'') i, (Const false)))"

lemma symSendInv9:
  "symParamRule N n_SendInv9"
  "wellFormedStatement N (act (n_SendInv9 i))"
  "absTransfRule M (n_SendInv9 i) = (if i \<le> M then n_SendInv9 i else chaos
\<triangleright> skip)"
  unfolding n_SendInv9_def symParamRule_def by auto

definition n_SendInv10::"nat \<Rightarrow> rule" where 
"n_SendInv10  i\<equiv>
(IVar (Para (''Chan2.Cmd'') i)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
(IVar (Para (''InvSet'') i)) =\<^sub>f  (Const true)  \<and>\<^sub>f
(IVar (Ident ''CurCmd''))  =\<^sub>f (Const ReqS)  \<and>\<^sub>f
(IVar (Ident ''ExGntd''))  =\<^sub>f (Const true) 
   \<triangleright>
(assign (Para (''Chan2.Cmd'') i, (Const Inv)))||
(assign (Para (''InvSet'') i, (Const false)))"

lemma symSendInv10:
  "symParamRule N n_SendInv10"
  "wellFormedStatement N (act (n_SendInv10 i))"
  "absTransfRule M (n_SendInv10 i) = (if i \<le> M then n_SendInv10 i else chaos
\<triangleright> skip)"
  unfolding n_SendInv10_def symParamRule_def by auto

definition n_RecvReqE11::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_RecvReqE11  i N\<equiv>
(IVar (Ident ''CurCmd''))  =\<^sub>f (Const Empty)  \<and>\<^sub>f
(IVar (Para (''Chan1.Cmd'') i)) =\<^sub>f  (Const ReqE) 
   \<triangleright>
(assign ((Ident ''CurCmd''), (Const ReqE)))||
(assign ((Ident ''CurPtr''), (Const (index i))))||
(assign (Para (''Chan1.Cmd'') i, (Const Empty)))||
(parallelList (map (\<lambda>j. (assign (Para (''InvSet'') j, (IVar (Para (''ShrSet'') j))))) (down N)))"

lemma symRecvReqE11:
  "symParamRule N n_RecvReqE11"
  "wellFormedStatement N (act (n_RecvReqE11 i))"
  "absTransfRule M (n_RecvReqE11 i) = (if i \<le> M then n_RecvReqE11 i else chaos
\<triangleright> skip)"
  unfolding n_RecvReqE11_def symParamRule_def by auto

definition n_RecvReqS12::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_RecvReqS12  i N\<equiv>
(IVar (Ident ''CurCmd''))  =\<^sub>f (Const Empty)  \<and>\<^sub>f
(IVar (Para (''Chan1.Cmd'') i)) =\<^sub>f  (Const ReqS) 
   \<triangleright>
(assign ((Ident ''CurCmd''), (Const ReqS)))||
(assign ((Ident ''CurPtr''), (Const (index i))))||
(assign (Para (''Chan1.Cmd'') i, (Const Empty)))||
(parallelList (map (\<lambda>j. (assign (Para (''InvSet'') j, (IVar (Para (''ShrSet'') j))))) (down N)))"

lemma symRecvReqS12:
  "symParamRule N n_RecvReqS12"
  "wellFormedStatement N (act (n_RecvReqS12 i))"
  "absTransfRule M (n_RecvReqS12 i) = (if i \<le> M then n_RecvReqS12 i else chaos
\<triangleright> skip)"
  unfolding n_RecvReqS12_def symParamRule_def by auto

definition n_SendReqE13::"nat \<Rightarrow> rule" where 
"n_SendReqE13  i\<equiv>
(IVar (Para (''Chan1.Cmd'') i)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
(IVar (Para (''Cache.State'') i)) =\<^sub>f  (Const I) 
   \<triangleright>
(assign (Para (''Chan1.Cmd'') i, (Const ReqE)))"

lemma symSendReqE13:
  "symParamRule N n_SendReqE13"
  "wellFormedStatement N (act (n_SendReqE13 i))"
  "absTransfRule M (n_SendReqE13 i) = (if i \<le> M then n_SendReqE13 i else chaos
\<triangleright> skip)"
  unfolding n_SendReqE13_def symParamRule_def by auto

definition n_SendReqE14::"nat \<Rightarrow> rule" where 
"n_SendReqE14  i\<equiv>
(IVar (Para (''Chan1.Cmd'') i)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
(IVar (Para (''Cache.State'') i)) =\<^sub>f  (Const S) 
   \<triangleright>
(assign (Para (''Chan1.Cmd'') i, (Const ReqE)))"

lemma symSendReqE14:
  "symParamRule N n_SendReqE14"
  "wellFormedStatement N (act (n_SendReqE14 i))"
  "absTransfRule M (n_SendReqE14 i) = (if i \<le> M then n_SendReqE14 i else chaos
\<triangleright> skip)"
  unfolding n_SendReqE14_def symParamRule_def by auto

definition n_SendReqS15::"nat \<Rightarrow> rule" where 
"n_SendReqS15  i\<equiv>
(IVar (Para (''Chan1.Cmd'') i)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
(IVar (Para (''Cache.State'') i)) =\<^sub>f  (Const I) 
   \<triangleright>
(assign (Para (''Chan1.Cmd'') i, (Const ReqS)))"

lemma symSendReqS15:
  "symParamRule N n_SendReqS15"
  "wellFormedStatement N (act (n_SendReqS15 i))"
  "absTransfRule M (n_SendReqS15 i) = (if i \<le> M then n_SendReqS15 i else chaos
\<triangleright> skip)"
  unfolding n_SendReqS15_def symParamRule_def by auto

definition n_Store16::"nat \<Rightarrow> rule" where 
"n_Store16  i\<equiv>
(IVar (Para (''Cache.State'') i)) =\<^sub>f  (Const E) 
   \<triangleright>
(assign (Para (''Cache.Data'') i, (IVar(Ident ''d''))))||
(assign ((Ident ''AuxData''), (IVar(Ident ''d''))))"

lemma symStore16:
  "symParamRule N n_Store16"
  "wellFormedStatement N (act (n_Store16 i))"
  "absTransfRule M (n_Store16 i) = (if i \<le> M then n_Store16 i else chaos
\<triangleright> skip)"
  unfolding n_Store16_def symParamRule_def by auto

subsection \<open>Putting everything together ---definition of rules\<close>

definition n_RecvGntE1s::" nat\<Rightarrow>rule set" where 
  "n_RecvGntE1s N== oneParamCons N  n_RecvGntE1"

definition n_RecvGntS2s::" nat\<Rightarrow>rule set" where 
  "n_RecvGntS2s N== oneParamCons N  n_RecvGntS2"

definition n_SendGntE3s::" nat\<Rightarrow>rule set" where 
  "n_SendGntE3s N== oneParamCons N  n_SendGntE3"

definition n_SendGntS4s::" nat\<Rightarrow>rule set" where 
  "n_SendGntS4s N== oneParamCons N  n_SendGntS4"

definition n_RecvInvAck5s::" nat\<Rightarrow>rule set" where 
  "n_RecvInvAck5s N== oneParamCons N  n_RecvInvAck5"

definition n_RecvInvAck6s::" nat\<Rightarrow>rule set" where 
  "n_RecvInvAck6s N== oneParamCons N  n_RecvInvAck6"

definition n_SendInvAck7s::" nat\<Rightarrow>rule set" where 
  "n_SendInvAck7s N== oneParamCons N  n_SendInvAck7"

definition n_SendInvAck8s::" nat\<Rightarrow>rule set" where 
  "n_SendInvAck8s N== oneParamCons N  n_SendInvAck8"

definition n_SendInv9s::" nat\<Rightarrow>rule set" where 
  "n_SendInv9s N== oneParamCons N  n_SendInv9"

definition n_SendInv10s::" nat\<Rightarrow>rule set" where 
  "n_SendInv10s N== oneParamCons N  n_SendInv10"

definition n_RecvReqE11s::" nat\<Rightarrow>rule set" where 
  "n_RecvReqE11s N== oneParamCons N  n_RecvReqE11"

definition n_RecvReqS12s::" nat\<Rightarrow>rule set" where 
  "n_RecvReqS12s N== oneParamCons N  n_RecvReqS12"

definition n_SendReqE13s::" nat\<Rightarrow>rule set" where 
  "n_SendReqE13s N== oneParamCons N  n_SendReqE13"

definition n_SendReqE14s::" nat\<Rightarrow>rule set" where 
  "n_SendReqE14s N== oneParamCons N  n_SendReqE14"

definition n_SendReqS15s::" nat\<Rightarrow>rule set" where 
  "n_SendReqS15s N== oneParamCons N  n_SendReqS15"

definition n_Store16s::" nat\<Rightarrow>rule set" where 
  "n_Store16s N== oneParamCons N  n_Store16"

definition rules'::"nat \<Rightarrow> rule set" where [simp]:
"rules' N \<equiv>  (n_RecvGntE1s N) \<union>
 (n_RecvGntS2s N) \<union>
 (n_SendGntE3s N) \<union>
 (n_SendGntS4s N) \<union>
 (n_RecvInvAck5s N) \<union>
 (n_RecvInvAck6s N) \<union>
 (n_SendInvAck7s N) \<union>
 (n_SendInvAck8s N) \<union>
 (n_SendInv9s N) \<union>
 (n_SendInv10s N) \<union>
 (n_RecvReqE11s N) \<union>
 (n_RecvReqS12s N) \<union>
 (n_SendReqE13s N) \<union>
 (n_SendReqE14s N) \<union>
 (n_SendReqS15s N) \<union>
 (n_Store16s N) 
"

lemma n_RecvGntE1sIsSym:
  "symProtRules' N (n_RecvGntE1s N)"
  using symRecvGntE1(1) n_RecvGntE1s_def symParaRuleInfSymRuleSet by auto

lemma n_RecvGntS2sIsSym:
  "symProtRules' N (n_RecvGntS2s N)"
  using symRecvGntS2(1) n_RecvGntS2s_def symParaRuleInfSymRuleSet by auto

lemma n_SendGntE3sIsSym:
  "symProtRules' N (n_SendGntE3s N)"
  using symSendGntE3(1) n_SendGntE3s_def symParaRuleInfSymRuleSet by auto

lemma n_SendGntS4sIsSym:
  "symProtRules' N (n_SendGntS4s N)"
  using symSendGntS4(1) n_SendGntS4s_def symParaRuleInfSymRuleSet by auto

lemma n_RecvInvAck5sIsSym:
  "symProtRules' N (n_RecvInvAck5s N)"
  using symRecvInvAck5(1) n_RecvInvAck5s_def symParaRuleInfSymRuleSet by auto

lemma n_RecvInvAck6sIsSym:
  "symProtRules' N (n_RecvInvAck6s N)"
  using symRecvInvAck6(1) n_RecvInvAck6s_def symParaRuleInfSymRuleSet by auto

lemma n_SendInvAck7sIsSym:
  "symProtRules' N (n_SendInvAck7s N)"
  using symSendInvAck7(1) n_SendInvAck7s_def symParaRuleInfSymRuleSet by auto

lemma n_SendInvAck8sIsSym:
  "symProtRules' N (n_SendInvAck8s N)"
  using symSendInvAck8(1) n_SendInvAck8s_def symParaRuleInfSymRuleSet by auto

lemma n_SendInv9sIsSym:
  "symProtRules' N (n_SendInv9s N)"
  using symSendInv9(1) n_SendInv9s_def symParaRuleInfSymRuleSet by auto

lemma n_SendInv10sIsSym:
  "symProtRules' N (n_SendInv10s N)"
  using symSendInv10(1) n_SendInv10s_def symParaRuleInfSymRuleSet by auto

lemma n_RecvReqE11sIsSym:
  "symProtRules' N (n_RecvReqE11s N)"
  using symRecvReqE11(1) n_RecvReqE11s_def symParaRuleInfSymRuleSet by auto

lemma n_RecvReqS12sIsSym:
  "symProtRules' N (n_RecvReqS12s N)"
  using symRecvReqS12(1) n_RecvReqS12s_def symParaRuleInfSymRuleSet by auto

lemma n_SendReqE13sIsSym:
  "symProtRules' N (n_SendReqE13s N)"
  using symSendReqE13(1) n_SendReqE13s_def symParaRuleInfSymRuleSet by auto

lemma n_SendReqE14sIsSym:
  "symProtRules' N (n_SendReqE14s N)"
  using symSendReqE14(1) n_SendReqE14s_def symParaRuleInfSymRuleSet by auto

lemma n_SendReqS15sIsSym:
  "symProtRules' N (n_SendReqS15s N)"
  using symSendReqS15(1) n_SendReqS15s_def symParaRuleInfSymRuleSet by auto

lemma n_Store16sIsSym:
  "symProtRules' N (n_Store16s N)"
  using symStore16(1) n_Store16s_def symParaRuleInfSymRuleSet by auto

lemma rulesSym':
  shows "symProtRules' N (rules' N)"
  using n_RecvGntE1sIsSym n_RecvGntS2sIsSym n_SendGntE3sIsSym n_SendGntS4sIsSym n_RecvInvAck5sIsSym n_RecvInvAck6sIsSym n_SendInvAck7sIsSym n_SendInvAck8sIsSym n_SendInv9sIsSym n_SendInv10sIsSym n_RecvReqE11sIsSym n_RecvReqS12sIsSym n_SendReqE13sIsSym n_SendReqE14sIsSym n_SendReqS15sIsSym n_Store16sIsSym rules'_def symProtRulesUnion by presburger 



subsection{*Definitions of each abstracted rule*}

definition  NC::"nat " where [simp]: "NC==1"

definition n_SendGntE3_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_SendGntE3_abs  i M\<equiv>
(IVar (Ident ''CurCmd''))  =\<^sub>f (Const ReqE)  \<and>\<^sub>f
(IVar (Ident ''CurPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''ExGntd''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(\<forall>\<^sub>fj. (IVar (Para (''ShrSet\'') j)) =\<^sub>f  (Const false) )) M

   \<triangleright>
(assign ((Ident ''ExGntd''), (Const true )))||
(assign ((Ident ''	CurCmd''), (Const Empty)))"

definition n_SendGntS4_abs::"nat \<Rightarrow> rule" where [simp]:
"n_SendGntS4_abs  i\<equiv>
(IVar (Ident ''CurCmd''))  =\<^sub>f (Const ReqS)  \<and>\<^sub>f
(IVar (Ident ''CurPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''ExGntd''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''CurCmd''), (Const Empty)))"

definition n_RecvInvAck5_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvInvAck5_abs  i M\<equiv>
\<not>\<^sub>f (IVar (Ident ''CurCmd'')) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
(IVar (Ident ''ExGntd''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(\<forall>\<^sub>fj. (IVar (Para (''InvSet\'') j)) =\<^sub>f  (Const false) )) M \<and>\<^sub>f
(IVar (Para (''ShrSet\'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
(IVar (Para (''Chan3\.Cmd'') j)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Chan2\.Cmd'') j)) =\<^sub>f  (Const Inv)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Chan3\.Cmd'') j)) =\<^sub>f  (Const InvAck)  \<and>\<^sub>f
(IVar (Para (''Chan2\.Cmd'') j)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Cache\.State'') j)) =\<^sub>f  (Const E)  \<and>\<^sub>f
(IVar (Para (''Cache\.State'') j)) =\<^sub>f  (Const I)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Chan2\.Cmd'') j)) =\<^sub>f  (Const GntE) 

   \<triangleright>
(assign ((Ident ''ExGntd''), (Const false )))||
(assign ((Ident ''	MemData''), (IVar (Ident ''AuxData''))))"

definition n_RecvReqE11_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvReqE11_abs  i M\<equiv>
(IVar (Ident ''CurCmd''))  =\<^sub>f (Const Empty) 
   \<triangleright>
(assign ((Ident ''CurCmd''), (Const ReqE )))||
(assign ((Ident ''	CurPtr''), (IVar (Ident '' Other''))))||
(parallelList (map (\<lambda>j. (assign (Para (''		InvSet\'') j, (IVar (Para (''ShrSet\'') j))))) (down N)))"

definition n_RecvReqS12_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvReqS12_abs  i M\<equiv>
(IVar (Ident ''CurCmd''))  =\<^sub>f (Const Empty) 
   \<triangleright>
(assign ((Ident ''CurCmd''), (Const ReqS )))||
(assign ((Ident ''	CurPtr''), (IVar (Ident '' Other''))))||
(parallelList (map (\<lambda>j. (assign (Para (''		InvSet\'') j, (IVar (Para (''ShrSet\'') j))))) (down N)))"

definition n_Store16_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_Store16_abs  i M\<equiv>
(\<forall>\<^sub>fj. (IVar (Para (''InvSet\'') j)) =\<^sub>f  (Const false) )) M \<and>\<^sub>f
(IVar (Para (''ShrSet\'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
(IVar (Para (''Chan3\.Cmd'') j)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Chan2\.Cmd'') j)) =\<^sub>f  (Const Inv)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Chan2\.Cmd'') j)) =\<^sub>f  (Const GntS)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Chan3\.Cmd'') j)) =\<^sub>f  (Const InvAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Cache\.State'') j)) =\<^sub>f  (Const S)  \<and>\<^sub>f
(IVar (Para (''Chan2\.Cmd'') j)) =\<^sub>f  (Const Empty)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Cache\.State'') j)) =\<^sub>f  (Const E)  \<and>\<^sub>f
(IVar (Para (''Cache\.State'') j)) =\<^sub>f  (Const I)  \<and>\<^sub>f
(IVar (Ident ''ExGntd''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Chan2\.Cmd'') j)) =\<^sub>f  (Const GntE) 

   \<triangleright>
(assign ((Ident ''AuxData''), (IVar (Ident ''['DATA_1']''))))"



end