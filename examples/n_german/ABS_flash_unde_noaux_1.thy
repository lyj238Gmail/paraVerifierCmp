theory ABS_flash_unde_noaux_1
  imports CMP
begin

subsection \<open>Definitions\<close>

text \<open>type definitions \<close>

definition CACHE_I :: scalrValueType where [simp]: "CACHE_I\<equiv> enum ''control'' ''CACHE_I''"
definition CACHE_S :: scalrValueType where [simp]: "CACHE_S\<equiv> enum ''control'' ''CACHE_S''"
definition CACHE_E :: scalrValueType where [simp]: "CACHE_E\<equiv> enum ''control'' ''CACHE_E''"
definition NODE_None :: scalrValueType where [simp]: "NODE_None\<equiv> enum ''control'' ''NODE_None''"
definition NODE_Get :: scalrValueType where [simp]: "NODE_Get\<equiv> enum ''control'' ''NODE_Get''"
definition NODE_GetX :: scalrValueType where [simp]: "NODE_GetX\<equiv> enum ''control'' ''NODE_GetX''"
definition UNI_None :: scalrValueType where [simp]: "UNI_None\<equiv> enum ''control'' ''UNI_None''"
definition UNI_Get :: scalrValueType where [simp]: "UNI_Get\<equiv> enum ''control'' ''UNI_Get''"
definition UNI_GetX :: scalrValueType where [simp]: "UNI_GetX\<equiv> enum ''control'' ''UNI_GetX''"
definition UNI_Put :: scalrValueType where [simp]: "UNI_Put\<equiv> enum ''control'' ''UNI_Put''"
definition UNI_PutX :: scalrValueType where [simp]: "UNI_PutX\<equiv> enum ''control'' ''UNI_PutX''"
definition UNI_Nak :: scalrValueType where [simp]: "UNI_Nak\<equiv> enum ''control'' ''UNI_Nak''"
definition INV_None :: scalrValueType where [simp]: "INV_None\<equiv> enum ''control'' ''INV_None''"
definition INV_Inv :: scalrValueType where [simp]: "INV_Inv\<equiv> enum ''control'' ''INV_Inv''"
definition INV_InvAck :: scalrValueType where [simp]: "INV_InvAck\<equiv> enum ''control'' ''INV_InvAck''"
definition RP_None :: scalrValueType where [simp]: "RP_None\<equiv> enum ''control'' ''RP_None''"
definition RP_Replace :: scalrValueType where [simp]: "RP_Replace\<equiv> enum ''control'' ''RP_Replace''"
definition WB_None :: scalrValueType where [simp]: "WB_None\<equiv> enum ''control'' ''WB_None''"
definition WB_Wb :: scalrValueType where [simp]: "WB_Wb\<equiv> enum ''control'' ''WB_Wb''"
definition SHWB_None :: scalrValueType where [simp]: "SHWB_None\<equiv> enum ''control'' ''SHWB_None''"
definition SHWB_ShWb :: scalrValueType where [simp]: "SHWB_ShWb\<equiv> enum ''control'' ''SHWB_ShWb''"
definition SHWB_FAck :: scalrValueType where [simp]: "SHWB_FAck\<equiv> enum ''control'' ''SHWB_FAck''"
definition NAKC_None :: scalrValueType where [simp]: "NAKC_None\<equiv> enum ''control'' ''NAKC_None''"
definition NAKC_Nakc :: scalrValueType where [simp]: "NAKC_Nakc\<equiv> enum ''control'' ''NAKC_Nakc''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"

text \<open>initial state \<close>

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.Proc.ProcCmd'') p)) =\<^sub>f  (Const NODE_None) ) N "

definition initSpec1::"nat \<Rightarrow> formula" where [simp]:
"initSpec1 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.Proc.InvMarked'') p)) =\<^sub>f  (Const false) ) N "

definition initSpec2::"nat \<Rightarrow> formula" where [simp]:
"initSpec2 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.Proc.CacheState'') p)) =\<^sub>f  (Const CACHE_I) ) N "

definition initSpec3::"nat \<Rightarrow> formula" where [simp]:
"initSpec3 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.Proc.CacheData'') p)) =\<^sub>f  (IVar(Ident ''d'')) ) N "

definition initSpec4::"nat \<Rightarrow> formula" where [simp]:
"initSpec4 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const false) ) N "

definition initSpec5::"nat \<Rightarrow> formula" where [simp]:
"initSpec5 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.Dir.InvSet'') p)) =\<^sub>f  (Const false) ) N "

definition initSpec6::"nat \<Rightarrow> formula" where [simp]:
"initSpec6 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.UniMsg.Cmd'') p)) =\<^sub>f  (Const UNI_None) ) N "

definition initSpec7::"nat \<Rightarrow> formula" where [simp]:
"initSpec7 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.UniMsg.Proc'') p)) =\<^sub>f  (Const (index h)) ) N "

definition initSpec8::"nat \<Rightarrow> formula" where [simp]:
"initSpec8 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.UniMsg.HomeProc'') p)) =\<^sub>f  (Const true) ) N "

definition initSpec9::"nat \<Rightarrow> formula" where [simp]:
"initSpec9 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.UniMsg.Data'') p)) =\<^sub>f  (IVar(Ident ''d'')) ) N "

definition initSpec10::"nat \<Rightarrow> formula" where [simp]:
"initSpec10 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.InvMsg.Cmd'') p)) =\<^sub>f  (Const INV_None) ) N "

definition initSpec11::"nat \<Rightarrow> formula" where [simp]:
"initSpec11 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.RpMsg.Cmd'') p)) =\<^sub>f  (Const RP_None) ) N "

definition initSpec12::"formula" where [simp]:
"initSpec12 \<equiv> (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_None) "

definition initSpec13::"formula" where [simp]:
"initSpec13 \<equiv> (IVar (Ident ''Sta.HomeProc.InvMarked'')) =\<^sub>f  (Const false) "

definition initSpec14::"formula" where [simp]:
"initSpec14 \<equiv> (IVar (Ident ''Sta.HomeProc.CacheState'')) =\<^sub>f  (Const CACHE_I) "

definition initSpec15::"formula" where [simp]:
"initSpec15 \<equiv> (IVar (Ident ''Sta.Dir.HomeShrSet'')) =\<^sub>f  (Const false) "

definition initSpec16::"formula" where [simp]:
"initSpec16 \<equiv> (IVar (Ident ''Sta.Dir.HomeInvSet'')) =\<^sub>f  (Const false) "

definition initSpec17::"formula" where [simp]:
"initSpec17 \<equiv> (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =\<^sub>f  (Const UNI_None) "

definition initSpec18::"formula" where [simp]:
"initSpec18 \<equiv> (IVar (Ident ''Sta.HomeUniMsg.HomeProc'')) =\<^sub>f  (Const true) "

definition initSpec19::"formula" where [simp]:
"initSpec19 \<equiv> (IVar (Ident ''Sta.HomeInvMsg.Cmd'')) =\<^sub>f  (Const INV_None) "

definition initSpec20::"formula" where [simp]:
"initSpec20 \<equiv> (IVar (Ident ''Sta.HomeRpMsg.Cmd'')) =\<^sub>f  (Const RP_None) "

lemma absInitSpec:
assumes "M \<le> N"
shows "absTransfForm M (initSpec0 N) = initSpec0 M"
"absTransfForm M (initSpec1 N) = initSpec1 M"
"absTransfForm M (initSpec2 N) = initSpec2 M"
"absTransfForm M (initSpec3 N) = initSpec3 M"
"absTransfForm M (initSpec4 N) = initSpec4 M"
"absTransfForm M (initSpec5 N) = initSpec5 M"
"absTransfForm M (initSpec6 N) = initSpec6 M"
"absTransfForm M (initSpec7 N) = initSpec7 M"
"absTransfForm M (initSpec8 N) = initSpec8 M"
"absTransfForm M (initSpec9 N) = initSpec9 M"
"absTransfForm M (initSpec10 N) = initSpec10 M"
"absTransfForm M (initSpec11 N) = initSpec11 M"
"absTransfForm M initSpec12 = initSpec12"
"absTransfForm M initSpec13 = initSpec13"
"absTransfForm M initSpec14 = initSpec14"
"absTransfForm M initSpec15 = initSpec15"
"absTransfForm M initSpec16 = initSpec16"
"absTransfForm M initSpec17 = initSpec17"
"absTransfForm M initSpec18 = initSpec18"
"absTransfForm M initSpec19 = initSpec19"
"absTransfForm M initSpec20 = initSpec20"
unfolding initSpec0_def initSpec1_def initSpec2_def initSpec3_def initSpec4_def initSpec5_def initSpec6_def initSpec7_def initSpec8_def initSpec9_def initSpec10_def initSpec11_def initSpec12_def initSpec13_def initSpec14_def initSpec15_def initSpec16_def initSpec17_def initSpec18_def initSpec19_def initSpec20_def 
using assms by auto


definition allInitSpecs::"nat \<Rightarrow> formula list" where
"allInitSpecs N \<equiv> [
(initSpec0 N),
(initSpec1 N),
(initSpec2 N),
(initSpec3 N),
(initSpec4 N),
(initSpec5 N),
(initSpec6 N),
(initSpec7 N),
(initSpec8 N),
(initSpec9 N),
(initSpec10 N),
(initSpec11 N),
(initSpec12),
(initSpec13),
(initSpec14),
(initSpec15),
(initSpec16),
(initSpec17),
(initSpec18),
(initSpec19),
(initSpec20)
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
  "symPredSet' N ({(initSpec6 N)} )"
unfolding initSpec6_def
    apply (rule symPredSetForall)
  unfolding symParamForm_def by auto

lemma symPreds7[intro]:
  "symPredSet' N ({(initSpec7 N)} )"
unfolding initSpec7_def
    apply (rule symPredSetForall)
  unfolding symParamForm_def by auto

lemma symPreds8[intro]:
  "symPredSet' N ({(initSpec8 N)} )"
unfolding initSpec8_def
    apply (rule symPredSetForall)
  unfolding symParamForm_def by auto

lemma symPreds9[intro]:
  "symPredSet' N ({(initSpec9 N)} )"
unfolding initSpec9_def
    apply (rule symPredSetForall)
  unfolding symParamForm_def by auto

lemma symPreds10[intro]:
  "symPredSet' N ({(initSpec10 N)} )"
unfolding initSpec10_def
    apply (rule symPredSetForall)
  unfolding symParamForm_def by auto

lemma symPreds11[intro]:
  "symPredSet' N ({(initSpec11 N)} )"
unfolding initSpec11_def
    apply (rule symPredSetForall)
  unfolding symParamForm_def by auto

lemma symPreds12[intro]:
  "symPredSet' N ({(initSpec12 )} )"
  unfolding symPredSet'_def initSpec12_def by auto

lemma symPreds13[intro]:
  "symPredSet' N ({(initSpec13 )} )"
  unfolding symPredSet'_def initSpec13_def by auto

lemma symPreds14[intro]:
  "symPredSet' N ({(initSpec14 )} )"
  unfolding symPredSet'_def initSpec14_def by auto

lemma symPreds15[intro]:
  "symPredSet' N ({(initSpec15 )} )"
  unfolding symPredSet'_def initSpec15_def by auto

lemma symPreds16[intro]:
  "symPredSet' N ({(initSpec16 )} )"
  unfolding symPredSet'_def initSpec16_def by auto

lemma symPreds17[intro]:
  "symPredSet' N ({(initSpec17 )} )"
  unfolding symPredSet'_def initSpec17_def by auto

lemma symPreds18[intro]:
  "symPredSet' N ({(initSpec18 )} )"
  unfolding symPredSet'_def initSpec18_def by auto

lemma symPreds19[intro]:
  "symPredSet' N ({(initSpec19 )} )"
  unfolding symPredSet'_def initSpec19_def by auto

lemma symPreds20[intro]:
  "symPredSet' N ({(initSpec20 )} )"
  unfolding symPredSet'_def initSpec20_def by auto

lemma symPreds:
  "symPredSet' N (    {(initSpec0 N)} \<union>
    {(initSpec1 N)} \<union>
    {(initSpec2 N)} \<union>
    {(initSpec3 N)} \<union>
    {(initSpec4 N)} \<union>
    {(initSpec5 N)} \<union>
    {(initSpec6 N)} \<union>
    {(initSpec7 N)} \<union>
    {(initSpec8 N)} \<union>
    {(initSpec9 N)} \<union>
    {(initSpec10 N)} \<union>
    {(initSpec11 N)} \<union>
    {initSpec12} \<union>
    {initSpec13} \<union>
    {initSpec14} \<union>
    {initSpec15} \<union>
    {initSpec16} \<union>
    {initSpec17} \<union>
    {initSpec18} \<union>
    {initSpec19} \<union>
    {initSpec20})"

  apply (meson symPreds0 symPreds1 symPreds2 symPreds3 symPreds4 symPreds5 symPreds6 symPreds7 symPreds8 symPreds9 symPreds10 symPreds11 symPreds12 symPreds13 symPreds14 symPreds15 symPreds16 symPreds17 symPreds18 symPreds19 symPreds20 
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
    {(initSpec7 N)}\<union>
    {(initSpec8 N)}\<union>
    {(initSpec9 N)}\<union>
    {(initSpec10 N)}\<union>
    {(initSpec11 N)}\<union>
    {(initSpec12 )}\<union>
    {(initSpec13 )}\<union>
    {(initSpec14 )}\<union>
    {(initSpec15 )}\<union>
    {(initSpec16 )}\<union>
    {(initSpec17 )}\<union>
    {(initSpec18 )}\<union>
    {(initSpec19 )}\<union>
    {(initSpec20 )}" (is "?LHS=?RHS")
      using allInitSpecs_def by auto
    have b2:"symPredSet' N ?RHS"
      using symPreds by blast
    show "symPredSet' N (set (allInitSpecs N))"
      using b1 b2 by auto
  qed

definition n_NI_Replace3::"nat \<Rightarrow> rule" where 
"n_NI_Replace3  src \<equiv>
(IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true)
   \<triangleright>
(assign (Para (''Sta.RpMsg.Cmd'') src, (Const RP_None)))||
(assign (Para (''Sta.Dir.ShrSet'') src, (Const false)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))"

definition n_NI_Replace4::"nat \<Rightarrow> rule" where 
"n_NI_Replace4  src \<equiv>
(IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)
   \<triangleright>
(assign (Para (''Sta.RpMsg.Cmd'') src, (Const RP_None)))"

definition n_NI_InvAck_311::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_InvAck_311  src N\<equiv>
(IVar (Para (''Sta.InvMsg.Cmd'') src)) =\<^sub>f  (Const INV_InvAck) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =\<^sub>f (Const false) \<and>\<^sub>f
(\<forall>\<^sub>fp. (IVar (Para (''p = src | Sta.Dir.InvSet'') p)) =\<^sub>f  (Const false) ) N
   \<triangleright>
(assign (Para (''Sta.InvMsg.Cmd'') src, (Const INV_None)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))||
(assign ((Ident ''Sta.Dir.Pending''), (Const false)))"

definition n_NI_InvAck_212::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_InvAck_212  src N\<equiv>
(IVar (Para (''Sta.InvMsg.Cmd'') src)) =\<^sub>f  (Const INV_InvAck) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =\<^sub>f (Const false) \<and>\<^sub>f
(\<forall>\<^sub>fp. (IVar (Para (''Sta.Dir.InvSet'') p)) =\<^sub>f  (Const false) ) N
   \<triangleright>
(assign (Para (''Sta.InvMsg.Cmd'') src, (Const INV_None)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))||
(assign ((Ident ''Sta.Dir.Pending''), (Const false)))"

definition n_NI_InvAck_113::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_InvAck_113  src N\<equiv>
(IVar (Para (''Sta.InvMsg.Cmd'') src)) =\<^sub>f  (Const INV_InvAck) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =\<^sub>f (Const false) \<and>\<^sub>f
(\<forall>\<^sub>fp. (IVar (Para (''Sta.Dir.InvSet'') p)) =\<^sub>f  (Const false) ) N
   \<triangleright>
(assign (Para (''Sta.InvMsg.Cmd'') src, (Const INV_None)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))||
(assign ((Ident ''Sta.Dir.Pending''), (Const false)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))"

definition n_NI_InvAck_exists14::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_InvAck_exists14  dst src \<equiv>
(IVar (Para (''Sta.InvMsg.Cmd'') src)) =\<^sub>f  (Const INV_InvAck) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''dst'')) =\<^sub>f  (Const (index src)) \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') dst)) =\<^sub>f  (Const true)
   \<triangleright>
(assign (Para (''Sta.InvMsg.Cmd'') src, (Const INV_None)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))"

definition n_NI_InvAck_exists_Home15::"nat \<Rightarrow> rule" where 
"n_NI_InvAck_exists_Home15  src \<equiv>
(IVar (Para (''Sta.InvMsg.Cmd'') src)) =\<^sub>f  (Const INV_InvAck) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =\<^sub>f (Const true)
   \<triangleright>
(assign (Para (''Sta.InvMsg.Cmd'') src, (Const INV_None)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))"

definition n_NI_Inv16::"nat \<Rightarrow> rule" where 
"n_NI_Inv16  dst \<equiv>
(IVar (Para (''Sta.InvMsg.Cmd'') dst)) =\<^sub>f  (Const INV_Inv) \<and>\<^sub>f
(IVar (Para (''Sta.Proc.ProcCmd'') dst)) =\<^sub>f  (Const NODE_Get)
   \<triangleright>
(assign (Para (''Sta.InvMsg.Cmd'') dst, (Const INV_InvAck)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign (Para (''Sta.Proc.InvMarked'') dst, (Const true)))"

definition n_NI_Inv17::"nat \<Rightarrow> rule" where 
"n_NI_Inv17  dst \<equiv>
(IVar (Para (''Sta.InvMsg.Cmd'') dst)) =\<^sub>f  (Const INV_Inv) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.ProcCmd'') dst)) =\<^sub>f  (Const NODE_Get)
   \<triangleright>
(assign (Para (''Sta.InvMsg.Cmd'') dst, (Const INV_InvAck)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))"

definition n_NI_Remote_PutX18::"nat \<Rightarrow> rule" where 
"n_NI_Remote_PutX18  dst \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =\<^sub>f  (Const UNI_PutX) \<and>\<^sub>f
(IVar (Para (''Sta.Proc.ProcCmd'') dst)) =\<^sub>f  (Const NODE_GetX)
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''Sta.UniMsg.HomeProc'') dst, (Const false)))||
(assign (Para (''Sta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''Sta.Proc.InvMarked'') dst, (Const false)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_E)))"

definition n_NI_Remote_Put20::"nat \<Rightarrow> rule" where 
"n_NI_Remote_Put20  dst \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =\<^sub>f  (Const UNI_Put) \<and>\<^sub>f
(IVar (Para (''Sta.Proc.InvMarked'') dst)) =\<^sub>f  (Const true)
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''Sta.UniMsg.HomeProc'') dst, (Const false)))||
(assign (Para (''Sta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''Sta.Proc.InvMarked'') dst, (Const false)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))"

definition n_NI_Remote_Put21::"nat \<Rightarrow> rule" where 
"n_NI_Remote_Put21  dst \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =\<^sub>f  (Const UNI_Put) \<and>\<^sub>f
(IVar (Para (''Sta.Proc.InvMarked'') dst)) =\<^sub>f  (Const false)
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''Sta.UniMsg.HomeProc'') dst, (Const false)))||
(assign (Para (''Sta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_S)))"

definition n_NI_Remote_GetX_PutX_Home24::"nat \<Rightarrow> rule" where 
"n_NI_Remote_GetX_PutX_Home24  dst \<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index dst)) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)
   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_PutX)))"

definition n_NI_Remote_GetX_PutX25::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_GetX_PutX25  dst src \<equiv>
\<not>\<^sub>f (IVar (Ident ''src'')) =\<^sub>f  (Const (index dst)) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst)) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)
   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_FAck)))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index src))))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_GetX_Nak_Home26::"nat \<Rightarrow> rule" where 
"n_NI_Remote_GetX_Nak_Home26  dst \<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index dst)) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =\<^sub>f (Const false) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)
   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Nak)))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_GetX_Nak27::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_GetX_Nak27  dst src \<equiv>
\<not>\<^sub>f (IVar (Ident ''src'')) =\<^sub>f  (Const (index dst)) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst)) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const false) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (Const (index dst))))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const false)))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Local_GetX_PutX_1128::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_1128  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_E)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))N"

definition n_NI_Local_GetX_PutX_1029::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_1029  dst src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') dst)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const true)
 (Const false))))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const INV_Inv)
 (Const INV_None)))))N)"

definition n_NI_Local_GetX_PutX_10_Home30::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_10_Home30  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const true)
 (Const false))))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const INV_Inv)
 (Const INV_None)))))N)"

definition n_NI_Local_GetX_PutX_931::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_931  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const true)
 (Const false))))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const INV_Inv)
 (Const INV_None)))))N)"

definition n_NI_Local_GetX_PutX_932::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_932  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const true)
 (Const false))))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const INV_Inv)
 (Const INV_None)))))N)"

definition n_NI_Local_GetX_PutX_8_NODE_Get33::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_8_NODE_Get33  dst src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') dst)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const true)
 (Const false))))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const INV_Inv)
 (Const INV_None)))))N)"

definition n_NI_Local_GetX_PutX_834::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_834  dst src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') dst)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const true)
 (Const false))))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const INV_Inv)
 (Const INV_None)))))N)"

definition n_NI_Local_GetX_PutX_8_Home_NODE_Get35::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_8_Home_NODE_Get35  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const true)
 (Const false))))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const INV_Inv)
 (Const INV_None)))))N)"

definition n_NI_Local_GetX_PutX_8_Home36::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_8_Home36  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const true)
 (Const false))))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const INV_Inv)
 (Const INV_None)))))N)"

definition n_NI_Local_GetX_PutX_7_NODE_Get37::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_7_NODE_Get37  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const true)
 (Const false))))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const INV_Inv)
 (Const INV_None)))))N)"

definition n_NI_Local_GetX_PutX_7_NODE_Get38::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_7_NODE_Get38  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const true)
 (Const false))))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const INV_Inv)
 (Const INV_None)))))N)"

definition n_NI_Local_GetX_PutX_739::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_739  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const true)
 (Const false))))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const INV_Inv)
 (Const INV_None)))))N)"

definition n_NI_Local_GetX_PutX_740::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_740  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const true)
 (Const false))))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (iteForm
((\<not>\<^sub>f (Const (index p)) =\<^sub>f  (Const (index src)) \<and>\<^sub>f(((IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const true) )\<or>\<^sub>f(((IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) \<and>\<^sub>f(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index p)) )\<and>\<^sub>f(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) ))))
 (Const INV_Inv)
 (Const INV_None)))))N)"

definition n_NI_Local_GetX_PutX_641::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_641  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =\<^sub>f (Const false) \<and>\<^sub>f
(\<forall>\<^sub>fp. (IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const false) ) N \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))N"

definition n_NI_Local_GetX_PutX_542::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_542  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =\<^sub>f (Const false) \<and>\<^sub>f
(\<forall>\<^sub>fp. (IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const false) ) N \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))N"

definition n_NI_Local_GetX_PutX_443::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_443  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =\<^sub>f (Const false) \<and>\<^sub>f
(\<forall>\<^sub>fp. (IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const false) ) N \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))N"

definition n_NI_Local_GetX_PutX_344::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_344  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))N"

definition n_NI_Local_GetX_PutX_245::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_245  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))N"

definition n_NI_Local_GetX_PutX_146::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX_146  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
forallStm (\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))N"

definition n_NI_Local_GetX_GetX47::"nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_GetX47  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index src))
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_GetX)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident ''StaDirHeadPtr''))))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (IVar (Ident ''StaDirHomeHeadPtr''))))"

definition n_NI_Local_GetX_GetX48::"nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_GetX48  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const true)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_GetX)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident ''StaDirHeadPtr''))))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (IVar (Ident ''StaDirHomeHeadPtr''))))"

definition n_NI_Local_GetX_Nak49::"nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_Nak49  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true)
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_NI_Local_GetX_Nak50::"nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_Nak50  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.CacheState'')) =\<^sub>f  (Const CACHE_E)
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_NI_Local_GetX_Nak51::"nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_Nak51  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_NI_Remote_Get_Put_Home52::"nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Put_Home52  dst \<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index dst)) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)
   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_S)))||
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Put)))"

definition n_NI_Remote_Get_Put53::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Put53  dst src \<equiv>
\<not>\<^sub>f (IVar (Ident ''src'')) =\<^sub>f  (Const (index dst)) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst)) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)
   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_S)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Put)))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_ShWb)))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index src))))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_Get_Nak_Home54::"nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Nak_Home54  dst \<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index dst)) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =\<^sub>f (Const false) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)
   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Nak)))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_Get_Nak55::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Nak55  dst src \<equiv>
\<not>\<^sub>f (IVar (Ident ''src'')) =\<^sub>f  (Const (index dst)) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst)) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const false) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (Const (index dst))))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const false)))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Local_Get_Put_Dirty56::"nat \<Rightarrow> rule" where 
"n_NI_Local_Get_Put_Dirty56  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_E)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_S)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Put)))"

definition n_NI_Local_Get_Put57::"nat \<Rightarrow> rule" where 
"n_NI_Local_Get_Put57  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const false)
   \<triangleright>
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Put)))"

definition n_NI_Local_Get_Put_Head58::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_Get_Put_Head58  src N\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)
   \<triangleright>
(assign ((Ident ''Sta.Dir.ShrVld''), (Const true)))||
(assign (Para (''Sta.Dir.ShrSet'') src, (Const true)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (IVar (Ident (''Sta.Dir.HomeShrSet'')))))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Put)))||
(forallStm(\<lambda>p. 
(assign (Para (''Sta.Dir.InvSet'') p, (iteForm
((Const (index p))  =\<^sub>f (Const (index src)) )
 (Const true)
(IVar (Para (''Sta.Dir.ShrSet'') p))))))N)"

definition n_NI_Local_Get_Get59::"nat \<Rightarrow> rule" where 
"n_NI_Local_Get_Get59  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index src))
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Get)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident ''StaDirHeadPtr''))))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (IVar (Ident ''StaDirHomeHeadPtr''))))"

definition n_NI_Local_Get_Get60::"nat \<Rightarrow> rule" where 
"n_NI_Local_Get_Get60  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const true)
   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Get)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident ''StaDirHeadPtr''))))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (IVar (Ident ''StaDirHomeHeadPtr''))))"

definition n_NI_Local_Get_Nak61::"nat \<Rightarrow> rule" where 
"n_NI_Local_Get_Nak61  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true)
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_NI_Local_Get_Nak62::"nat \<Rightarrow> rule" where 
"n_NI_Local_Get_Nak62  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.CacheState'')) =\<^sub>f  (Const CACHE_E)
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_NI_Local_Get_Nak63::"nat \<Rightarrow> rule" where 
"n_NI_Local_Get_Nak63  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get) \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index src)) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_NI_Nak66::"nat \<Rightarrow> rule" where 
"n_NI_Nak66  dst \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =\<^sub>f  (Const UNI_Nak)
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''Sta.UniMsg.HomeProc'') dst, (Const false)))||
(assign (Para (''Sta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''Sta.Proc.InvMarked'') dst, (Const false)))"

definition n_PI_Remote_Replace68::"nat \<Rightarrow> rule" where 
"n_PI_Remote_Replace68  src \<equiv>
(IVar (Para (''Sta.Proc.ProcCmd'') src)) =\<^sub>f  (Const NODE_None) \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') src)) =\<^sub>f  (Const CACHE_S)
   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') src, (Const CACHE_I)))||
(assign (Para (''Sta.RpMsg.Cmd'') src, (Const RP_Replace)))"

definition n_PI_Remote_PutX71::"nat \<Rightarrow> rule" where 
"n_PI_Remote_PutX71  dst \<equiv>
(IVar (Para (''Sta.Proc.ProcCmd'') dst)) =\<^sub>f  (Const NODE_None) \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)
   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign ((Ident ''Sta.WbMsg.Cmd''), (Const WB_Wb)))||
(assign ((Ident ''Sta.WbMsg.Proc''), (Const (index dst))))||
(assign ((Ident ''Sta.WbMsg.HomeProc''), (Const false)))"

definition n_PI_Remote_GetX80::"nat \<Rightarrow> rule" where 
"n_PI_Remote_GetX80  src \<equiv>
(IVar (Para (''Sta.Proc.ProcCmd'') src)) =\<^sub>f  (Const NODE_None) \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') src)) =\<^sub>f  (Const CACHE_I)
   \<triangleright>
(assign (Para (''Sta.Proc.ProcCmd'') src, (Const NODE_GetX)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_GetX)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_PI_Remote_Get84::"nat \<Rightarrow> rule" where 
"n_PI_Remote_Get84  src \<equiv>
(IVar (Para (''Sta.Proc.ProcCmd'') src)) =\<^sub>f  (Const NODE_None) \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') src)) =\<^sub>f  (Const CACHE_I)
   \<triangleright>
(assign (Para (''Sta.Proc.ProcCmd'') src, (Const NODE_Get)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Get)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

"n_Store_Home85  \<equiv>
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_E)
   \<triangleright>
"

definition n_Store86::"nat \<Rightarrow> rule" where 
"n_Store86  src \<equiv>
(IVar (Para (''Sta.Proc.CacheState'') src)) =\<^sub>f  (Const CACHE_E)
   \<triangleright>
"

subsection \<open>Putting everything together ---definition of rules\<close>

definition n_NI_Replace3s::" nat\<Rightarrow>rule set" where 
  "n_NI_Replace3s N== oneParamCons N  n_NI_Replace3"

definition n_NI_Replace4s::" nat\<Rightarrow>rule set" where 
  "n_NI_Replace4s N== oneParamCons N  n_NI_Replace4"

definition n_NI_InvAck_311s::" nat\<Rightarrow>rule set" where 
  "n_NI_InvAck_311s N== oneParamCons N  (n_NI_InvAck_311 N)"

definition n_NI_InvAck_212s::" nat\<Rightarrow>rule set" where 
  "n_NI_InvAck_212s N== oneParamCons N  (n_NI_InvAck_212 N)"

definition n_NI_InvAck_113s::" nat\<Rightarrow>rule set" where 
  "n_NI_InvAck_113s N== oneParamCons N  (n_NI_InvAck_113 N)"

definition n_NI_InvAck_exists14s::" nat\<Rightarrow>rule set" where 
  "n_NI_InvAck_exists14s N== oneParamCons N  n_NI_InvAck_exists14"

definition n_NI_InvAck_exists_Home15s::" nat\<Rightarrow>rule set" where 
  "n_NI_InvAck_exists_Home15s N== oneParamCons N  n_NI_InvAck_exists_Home15"

definition n_NI_Inv16s::" nat\<Rightarrow>rule set" where 
  "n_NI_Inv16s N== oneParamCons N  n_NI_Inv16"

definition n_NI_Inv17s::" nat\<Rightarrow>rule set" where 
  "n_NI_Inv17s N== oneParamCons N  n_NI_Inv17"

definition n_NI_Remote_PutX18s::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_PutX18s N== oneParamCons N  n_NI_Remote_PutX18"

definition n_NI_Remote_Put20s::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Put20s N== oneParamCons N  n_NI_Remote_Put20"

definition n_NI_Remote_Put21s::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Put21s N== oneParamCons N  n_NI_Remote_Put21"

definition n_NI_Remote_GetX_PutX_Home24s::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_GetX_PutX_Home24s N== oneParamCons N  n_NI_Remote_GetX_PutX_Home24"

definition n_NI_Remote_GetX_PutX25s::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_GetX_PutX25s N== oneParamCons N  n_NI_Remote_GetX_PutX25"

definition n_NI_Remote_GetX_Nak_Home26s::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_GetX_Nak_Home26s N== oneParamCons N  n_NI_Remote_GetX_Nak_Home26"

definition n_NI_Remote_GetX_Nak27s::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_GetX_Nak27s N== oneParamCons N  n_NI_Remote_GetX_Nak27"

definition n_NI_Local_GetX_PutX_1128s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_1128s N== oneParamCons N  (n_NI_Local_GetX_PutX_1128 N)"

definition n_NI_Local_GetX_PutX_1029s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_1029s N== oneParamCons N  (n_NI_Local_GetX_PutX_1029 N)"

definition n_NI_Local_GetX_PutX_10_Home30s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_10_Home30s N== oneParamCons N  (n_NI_Local_GetX_PutX_10_Home30 N)"

definition n_NI_Local_GetX_PutX_931s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_931s N== oneParamCons N  (n_NI_Local_GetX_PutX_931 N)"

definition n_NI_Local_GetX_PutX_932s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_932s N== oneParamCons N  (n_NI_Local_GetX_PutX_932 N)"

definition n_NI_Local_GetX_PutX_8_NODE_Get33s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_8_NODE_Get33s N== oneParamCons N  (n_NI_Local_GetX_PutX_8_NODE_Get33 N)"

definition n_NI_Local_GetX_PutX_834s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_834s N== oneParamCons N  (n_NI_Local_GetX_PutX_834 N)"

definition n_NI_Local_GetX_PutX_8_Home_NODE_Get35s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_8_Home_NODE_Get35s N== oneParamCons N  (n_NI_Local_GetX_PutX_8_Home_NODE_Get35 N)"

definition n_NI_Local_GetX_PutX_8_Home36s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_8_Home36s N== oneParamCons N  (n_NI_Local_GetX_PutX_8_Home36 N)"

definition n_NI_Local_GetX_PutX_7_NODE_Get37s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_7_NODE_Get37s N== oneParamCons N  (n_NI_Local_GetX_PutX_7_NODE_Get37 N)"

definition n_NI_Local_GetX_PutX_7_NODE_Get38s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_7_NODE_Get38s N== oneParamCons N  (n_NI_Local_GetX_PutX_7_NODE_Get38 N)"

definition n_NI_Local_GetX_PutX_739s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_739s N== oneParamCons N  (n_NI_Local_GetX_PutX_739 N)"

definition n_NI_Local_GetX_PutX_740s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_740s N== oneParamCons N  (n_NI_Local_GetX_PutX_740 N)"

definition n_NI_Local_GetX_PutX_641s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_641s N== oneParamCons N  (n_NI_Local_GetX_PutX_641 N)"

definition n_NI_Local_GetX_PutX_542s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_542s N== oneParamCons N  (n_NI_Local_GetX_PutX_542 N)"

definition n_NI_Local_GetX_PutX_443s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_443s N== oneParamCons N  (n_NI_Local_GetX_PutX_443 N)"

definition n_NI_Local_GetX_PutX_344s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_344s N== oneParamCons N  (n_NI_Local_GetX_PutX_344 N)"

definition n_NI_Local_GetX_PutX_245s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_245s N== oneParamCons N  (n_NI_Local_GetX_PutX_245 N)"

definition n_NI_Local_GetX_PutX_146s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutX_146s N== oneParamCons N  (n_NI_Local_GetX_PutX_146 N)"

definition n_NI_Local_GetX_GetX47s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_GetX47s N== oneParamCons N  n_NI_Local_GetX_GetX47"

definition n_NI_Local_GetX_GetX48s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_GetX48s N== oneParamCons N  n_NI_Local_GetX_GetX48"

definition n_NI_Local_GetX_Nak49s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_Nak49s N== oneParamCons N  n_NI_Local_GetX_Nak49"

definition n_NI_Local_GetX_Nak50s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_Nak50s N== oneParamCons N  n_NI_Local_GetX_Nak50"

definition n_NI_Local_GetX_Nak51s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_Nak51s N== oneParamCons N  n_NI_Local_GetX_Nak51"

definition n_NI_Remote_Get_Put_Home52s::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Get_Put_Home52s N== oneParamCons N  n_NI_Remote_Get_Put_Home52"

definition n_NI_Remote_Get_Put53s::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Get_Put53s N== oneParamCons N  n_NI_Remote_Get_Put53"

definition n_NI_Remote_Get_Nak_Home54s::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Get_Nak_Home54s N== oneParamCons N  n_NI_Remote_Get_Nak_Home54"

definition n_NI_Remote_Get_Nak55s::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Get_Nak55s N== oneParamCons N  n_NI_Remote_Get_Nak55"

definition n_NI_Local_Get_Put_Dirty56s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_Get_Put_Dirty56s N== oneParamCons N  n_NI_Local_Get_Put_Dirty56"

definition n_NI_Local_Get_Put57s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_Get_Put57s N== oneParamCons N  n_NI_Local_Get_Put57"

definition n_NI_Local_Get_Put_Head58s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_Get_Put_Head58s N== oneParamCons N  (n_NI_Local_Get_Put_Head58 N)"

definition n_NI_Local_Get_Get59s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_Get_Get59s N== oneParamCons N  n_NI_Local_Get_Get59"

definition n_NI_Local_Get_Get60s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_Get_Get60s N== oneParamCons N  n_NI_Local_Get_Get60"

definition n_NI_Local_Get_Nak61s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_Get_Nak61s N== oneParamCons N  n_NI_Local_Get_Nak61"

definition n_NI_Local_Get_Nak62s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_Get_Nak62s N== oneParamCons N  n_NI_Local_Get_Nak62"

definition n_NI_Local_Get_Nak63s::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_Get_Nak63s N== oneParamCons N  n_NI_Local_Get_Nak63"

definition n_NI_Nak66s::" nat\<Rightarrow>rule set" where 
  "n_NI_Nak66s N== oneParamCons N  n_NI_Nak66"

definition n_PI_Remote_Replace68s::" nat\<Rightarrow>rule set" where 
  "n_PI_Remote_Replace68s N== oneParamCons N  n_PI_Remote_Replace68"

definition n_PI_Remote_PutX71s::" nat\<Rightarrow>rule set" where 
  "n_PI_Remote_PutX71s N== oneParamCons N  n_PI_Remote_PutX71"

definition n_PI_Remote_GetX80s::" nat\<Rightarrow>rule set" where 
  "n_PI_Remote_GetX80s N== oneParamCons N  n_PI_Remote_GetX80"

definition n_PI_Remote_Get84s::" nat\<Rightarrow>rule set" where 
  "n_PI_Remote_Get84s N== oneParamCons N  n_PI_Remote_Get84"

definition n_Store_Home85s::" nat\<Rightarrow>rule set" where 
  "n_Store_Home85s N== oneParamCons N  n_Store_Home85"

definition n_Store86s::" nat\<Rightarrow>rule set" where 
  "n_Store86s N== oneParamCons N  n_Store86"

definition rules'::"nat \<Rightarrow> rule set" where [simp]:
"rules' N \<equiv>  (n_NI_Replace3s N) \<union>
 (n_NI_Replace4s N) \<union>
 (n_NI_InvAck_311s N) \<union>
 (n_NI_InvAck_212s N) \<union>
 (n_NI_InvAck_113s N) \<union>
 (n_NI_InvAck_exists14s N) \<union>
 (n_NI_InvAck_exists_Home15s N) \<union>
 (n_NI_Inv16s N) \<union>
 (n_NI_Inv17s N) \<union>
 (n_NI_Remote_PutX18s N) \<union>
 (n_NI_Remote_Put20s N) \<union>
 (n_NI_Remote_Put21s N) \<union>
 (n_NI_Remote_GetX_PutX_Home24s N) \<union>
 (n_NI_Remote_GetX_PutX25s N) \<union>
 (n_NI_Remote_GetX_Nak_Home26s N) \<union>
 (n_NI_Remote_GetX_Nak27s N) \<union>
 (n_NI_Local_GetX_PutX_1128s N) \<union>
 (n_NI_Local_GetX_PutX_1029s N) \<union>
 (n_NI_Local_GetX_PutX_10_Home30s N) \<union>
 (n_NI_Local_GetX_PutX_931s N) \<union>
 (n_NI_Local_GetX_PutX_932s N) \<union>
 (n_NI_Local_GetX_PutX_8_NODE_Get33s N) \<union>
 (n_NI_Local_GetX_PutX_834s N) \<union>
 (n_NI_Local_GetX_PutX_8_Home_NODE_Get35s N) \<union>
 (n_NI_Local_GetX_PutX_8_Home36s N) \<union>
 (n_NI_Local_GetX_PutX_7_NODE_Get37s N) \<union>
 (n_NI_Local_GetX_PutX_7_NODE_Get38s N) \<union>
 (n_NI_Local_GetX_PutX_739s N) \<union>
 (n_NI_Local_GetX_PutX_740s N) \<union>
 (n_NI_Local_GetX_PutX_641s N) \<union>
 (n_NI_Local_GetX_PutX_542s N) \<union>
 (n_NI_Local_GetX_PutX_443s N) \<union>
 (n_NI_Local_GetX_PutX_344s N) \<union>
 (n_NI_Local_GetX_PutX_245s N) \<union>
 (n_NI_Local_GetX_PutX_146s N) \<union>
 (n_NI_Local_GetX_GetX47s N) \<union>
 (n_NI_Local_GetX_GetX48s N) \<union>
 (n_NI_Local_GetX_Nak49s N) \<union>
 (n_NI_Local_GetX_Nak50s N) \<union>
 (n_NI_Local_GetX_Nak51s N) \<union>
 (n_NI_Remote_Get_Put_Home52s N) \<union>
 (n_NI_Remote_Get_Put53s N) \<union>
 (n_NI_Remote_Get_Nak_Home54s N) \<union>
 (n_NI_Remote_Get_Nak55s N) \<union>
 (n_NI_Local_Get_Put_Dirty56s N) \<union>
 (n_NI_Local_Get_Put57s N) \<union>
 (n_NI_Local_Get_Put_Head58s N) \<union>
 (n_NI_Local_Get_Get59s N) \<union>
 (n_NI_Local_Get_Get60s N) \<union>
 (n_NI_Local_Get_Nak61s N) \<union>
 (n_NI_Local_Get_Nak62s N) \<union>
 (n_NI_Local_Get_Nak63s N) \<union>
 (n_NI_Nak66s N) \<union>
 (n_PI_Remote_Replace68s N) \<union>
 (n_PI_Remote_PutX71s N) \<union>
 (n_PI_Remote_GetX80s N) \<union>
 (n_PI_Remote_Get84s N) \<union>
 (n_Store_Home85s N) \<union>
 (n_Store86s N) 
"

lemma n_NI_Replace3sIsSym:
  "symProtRules' N (n_NI_Replace3s N)"
  using symNI_Replace3(1) n_NI_Replace3s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Replace4sIsSym:
  "symProtRules' N (n_NI_Replace4s N)"
  using symNI_Replace4(1) n_NI_Replace4s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_InvAck_311sIsSym:
  "symProtRules' N (n_NI_InvAck_311s N)"
  using symNI_InvAck_311(1) n_NI_InvAck_311s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_InvAck_212sIsSym:
  "symProtRules' N (n_NI_InvAck_212s N)"
  using symNI_InvAck_212(1) n_NI_InvAck_212s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_InvAck_113sIsSym:
  "symProtRules' N (n_NI_InvAck_113s N)"
  using symNI_InvAck_113(1) n_NI_InvAck_113s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_InvAck_exists14sIsSym:
  "symProtRules' N (n_NI_InvAck_exists14s N)"
  using symNI_InvAck_exists14(1) n_NI_InvAck_exists14s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_InvAck_exists_Home15sIsSym:
  "symProtRules' N (n_NI_InvAck_exists_Home15s N)"
  using symNI_InvAck_exists_Home15(1) n_NI_InvAck_exists_Home15s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Inv16sIsSym:
  "symProtRules' N (n_NI_Inv16s N)"
  using symNI_Inv16(1) n_NI_Inv16s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Inv17sIsSym:
  "symProtRules' N (n_NI_Inv17s N)"
  using symNI_Inv17(1) n_NI_Inv17s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_PutX18sIsSym:
  "symProtRules' N (n_NI_Remote_PutX18s N)"
  using symNI_Remote_PutX18(1) n_NI_Remote_PutX18s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_Put20sIsSym:
  "symProtRules' N (n_NI_Remote_Put20s N)"
  using symNI_Remote_Put20(1) n_NI_Remote_Put20s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_Put21sIsSym:
  "symProtRules' N (n_NI_Remote_Put21s N)"
  using symNI_Remote_Put21(1) n_NI_Remote_Put21s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_GetX_PutX_Home24sIsSym:
  "symProtRules' N (n_NI_Remote_GetX_PutX_Home24s N)"
  using symNI_Remote_GetX_PutX_Home24(1) n_NI_Remote_GetX_PutX_Home24s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_GetX_PutX25sIsSym:
  "symProtRules' N (n_NI_Remote_GetX_PutX25s N)"
  using symNI_Remote_GetX_PutX25(1) n_NI_Remote_GetX_PutX25s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_GetX_Nak_Home26sIsSym:
  "symProtRules' N (n_NI_Remote_GetX_Nak_Home26s N)"
  using symNI_Remote_GetX_Nak_Home26(1) n_NI_Remote_GetX_Nak_Home26s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_GetX_Nak27sIsSym:
  "symProtRules' N (n_NI_Remote_GetX_Nak27s N)"
  using symNI_Remote_GetX_Nak27(1) n_NI_Remote_GetX_Nak27s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_1128sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_1128s N)"
  using symNI_Local_GetX_PutX_1128(1) n_NI_Local_GetX_PutX_1128s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_1029sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_1029s N)"
  using symNI_Local_GetX_PutX_1029(1) n_NI_Local_GetX_PutX_1029s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_10_Home30sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_10_Home30s N)"
  using symNI_Local_GetX_PutX_10_Home30(1) n_NI_Local_GetX_PutX_10_Home30s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_931sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_931s N)"
  using symNI_Local_GetX_PutX_931(1) n_NI_Local_GetX_PutX_931s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_932sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_932s N)"
  using symNI_Local_GetX_PutX_932(1) n_NI_Local_GetX_PutX_932s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_8_NODE_Get33sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_8_NODE_Get33s N)"
  using symNI_Local_GetX_PutX_8_NODE_Get33(1) n_NI_Local_GetX_PutX_8_NODE_Get33s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_834sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_834s N)"
  using symNI_Local_GetX_PutX_834(1) n_NI_Local_GetX_PutX_834s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_8_Home_NODE_Get35sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_8_Home_NODE_Get35s N)"
  using symNI_Local_GetX_PutX_8_Home_NODE_Get35(1) n_NI_Local_GetX_PutX_8_Home_NODE_Get35s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_8_Home36sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_8_Home36s N)"
  using symNI_Local_GetX_PutX_8_Home36(1) n_NI_Local_GetX_PutX_8_Home36s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_7_NODE_Get37sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_7_NODE_Get37s N)"
  using symNI_Local_GetX_PutX_7_NODE_Get37(1) n_NI_Local_GetX_PutX_7_NODE_Get37s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_7_NODE_Get38sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_7_NODE_Get38s N)"
  using symNI_Local_GetX_PutX_7_NODE_Get38(1) n_NI_Local_GetX_PutX_7_NODE_Get38s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_739sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_739s N)"
  using symNI_Local_GetX_PutX_739(1) n_NI_Local_GetX_PutX_739s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_740sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_740s N)"
  using symNI_Local_GetX_PutX_740(1) n_NI_Local_GetX_PutX_740s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_641sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_641s N)"
  using symNI_Local_GetX_PutX_641(1) n_NI_Local_GetX_PutX_641s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_542sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_542s N)"
  using symNI_Local_GetX_PutX_542(1) n_NI_Local_GetX_PutX_542s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_443sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_443s N)"
  using symNI_Local_GetX_PutX_443(1) n_NI_Local_GetX_PutX_443s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_344sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_344s N)"
  using symNI_Local_GetX_PutX_344(1) n_NI_Local_GetX_PutX_344s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_245sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_245s N)"
  using symNI_Local_GetX_PutX_245(1) n_NI_Local_GetX_PutX_245s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutX_146sIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutX_146s N)"
  using symNI_Local_GetX_PutX_146(1) n_NI_Local_GetX_PutX_146s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_GetX47sIsSym:
  "symProtRules' N (n_NI_Local_GetX_GetX47s N)"
  using symNI_Local_GetX_GetX47(1) n_NI_Local_GetX_GetX47s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_GetX48sIsSym:
  "symProtRules' N (n_NI_Local_GetX_GetX48s N)"
  using symNI_Local_GetX_GetX48(1) n_NI_Local_GetX_GetX48s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_Nak49sIsSym:
  "symProtRules' N (n_NI_Local_GetX_Nak49s N)"
  using symNI_Local_GetX_Nak49(1) n_NI_Local_GetX_Nak49s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_Nak50sIsSym:
  "symProtRules' N (n_NI_Local_GetX_Nak50s N)"
  using symNI_Local_GetX_Nak50(1) n_NI_Local_GetX_Nak50s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_Nak51sIsSym:
  "symProtRules' N (n_NI_Local_GetX_Nak51s N)"
  using symNI_Local_GetX_Nak51(1) n_NI_Local_GetX_Nak51s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_Get_Put_Home52sIsSym:
  "symProtRules' N (n_NI_Remote_Get_Put_Home52s N)"
  using symNI_Remote_Get_Put_Home52(1) n_NI_Remote_Get_Put_Home52s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_Get_Put53sIsSym:
  "symProtRules' N (n_NI_Remote_Get_Put53s N)"
  using symNI_Remote_Get_Put53(1) n_NI_Remote_Get_Put53s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_Get_Nak_Home54sIsSym:
  "symProtRules' N (n_NI_Remote_Get_Nak_Home54s N)"
  using symNI_Remote_Get_Nak_Home54(1) n_NI_Remote_Get_Nak_Home54s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_Get_Nak55sIsSym:
  "symProtRules' N (n_NI_Remote_Get_Nak55s N)"
  using symNI_Remote_Get_Nak55(1) n_NI_Remote_Get_Nak55s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Get_Put_Dirty56sIsSym:
  "symProtRules' N (n_NI_Local_Get_Put_Dirty56s N)"
  using symNI_Local_Get_Put_Dirty56(1) n_NI_Local_Get_Put_Dirty56s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Get_Put57sIsSym:
  "symProtRules' N (n_NI_Local_Get_Put57s N)"
  using symNI_Local_Get_Put57(1) n_NI_Local_Get_Put57s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Get_Put_Head58sIsSym:
  "symProtRules' N (n_NI_Local_Get_Put_Head58s N)"
  using symNI_Local_Get_Put_Head58(1) n_NI_Local_Get_Put_Head58s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Get_Get59sIsSym:
  "symProtRules' N (n_NI_Local_Get_Get59s N)"
  using symNI_Local_Get_Get59(1) n_NI_Local_Get_Get59s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Get_Get60sIsSym:
  "symProtRules' N (n_NI_Local_Get_Get60s N)"
  using symNI_Local_Get_Get60(1) n_NI_Local_Get_Get60s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Get_Nak61sIsSym:
  "symProtRules' N (n_NI_Local_Get_Nak61s N)"
  using symNI_Local_Get_Nak61(1) n_NI_Local_Get_Nak61s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Get_Nak62sIsSym:
  "symProtRules' N (n_NI_Local_Get_Nak62s N)"
  using symNI_Local_Get_Nak62(1) n_NI_Local_Get_Nak62s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Get_Nak63sIsSym:
  "symProtRules' N (n_NI_Local_Get_Nak63s N)"
  using symNI_Local_Get_Nak63(1) n_NI_Local_Get_Nak63s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Nak66sIsSym:
  "symProtRules' N (n_NI_Nak66s N)"
  using symNI_Nak66(1) n_NI_Nak66s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_Replace68sIsSym:
  "symProtRules' N (n_PI_Remote_Replace68s N)"
  using symPI_Remote_Replace68(1) n_PI_Remote_Replace68s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_PutX71sIsSym:
  "symProtRules' N (n_PI_Remote_PutX71s N)"
  using symPI_Remote_PutX71(1) n_PI_Remote_PutX71s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_GetX80sIsSym:
  "symProtRules' N (n_PI_Remote_GetX80s N)"
  using symPI_Remote_GetX80(1) n_PI_Remote_GetX80s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_Get84sIsSym:
  "symProtRules' N (n_PI_Remote_Get84s N)"
  using symPI_Remote_Get84(1) n_PI_Remote_Get84s_def symParaRuleInfSymRuleSet by auto

lemma n_Store_Home85sIsSym:
  "symProtRules' N (n_Store_Home85s N)"
  using symStore_Home85(1) n_Store_Home85s_def symParaRuleInfSymRuleSet by auto

lemma n_Store86sIsSym:
  "symProtRules' N (n_Store86s N)"
  using symStore86(1) n_Store86s_def symParaRuleInfSymRuleSet by auto

lemma rulesSym':
  shows "symProtRules' N (rules' N)"
  using n_NI_Replace3sIsSym n_NI_Replace4sIsSym n_NI_InvAck_311sIsSym n_NI_InvAck_212sIsSym n_NI_InvAck_113sIsSym n_NI_InvAck_exists14sIsSym n_NI_InvAck_exists_Home15sIsSym n_NI_Inv16sIsSym n_NI_Inv17sIsSym n_NI_Remote_PutX18sIsSym n_NI_Remote_Put20sIsSym n_NI_Remote_Put21sIsSym n_NI_Remote_GetX_PutX_Home24sIsSym n_NI_Remote_GetX_PutX25sIsSym n_NI_Remote_GetX_Nak_Home26sIsSym n_NI_Remote_GetX_Nak27sIsSym n_NI_Local_GetX_PutX_1128sIsSym n_NI_Local_GetX_PutX_1029sIsSym n_NI_Local_GetX_PutX_10_Home30sIsSym n_NI_Local_GetX_PutX_931sIsSym n_NI_Local_GetX_PutX_932sIsSym n_NI_Local_GetX_PutX_8_NODE_Get33sIsSym n_NI_Local_GetX_PutX_834sIsSym n_NI_Local_GetX_PutX_8_Home_NODE_Get35sIsSym n_NI_Local_GetX_PutX_8_Home36sIsSym n_NI_Local_GetX_PutX_7_NODE_Get37sIsSym n_NI_Local_GetX_PutX_7_NODE_Get38sIsSym n_NI_Local_GetX_PutX_739sIsSym n_NI_Local_GetX_PutX_740sIsSym n_NI_Local_GetX_PutX_641sIsSym n_NI_Local_GetX_PutX_542sIsSym n_NI_Local_GetX_PutX_443sIsSym n_NI_Local_GetX_PutX_344sIsSym n_NI_Local_GetX_PutX_245sIsSym n_NI_Local_GetX_PutX_146sIsSym n_NI_Local_GetX_GetX47sIsSym n_NI_Local_GetX_GetX48sIsSym n_NI_Local_GetX_Nak49sIsSym n_NI_Local_GetX_Nak50sIsSym n_NI_Local_GetX_Nak51sIsSym n_NI_Remote_Get_Put_Home52sIsSym n_NI_Remote_Get_Put53sIsSym n_NI_Remote_Get_Nak_Home54sIsSym n_NI_Remote_Get_Nak55sIsSym n_NI_Local_Get_Put_Dirty56sIsSym n_NI_Local_Get_Put57sIsSym n_NI_Local_Get_Put_Head58sIsSym n_NI_Local_Get_Get59sIsSym n_NI_Local_Get_Get60sIsSym n_NI_Local_Get_Nak61sIsSym n_NI_Local_Get_Nak62sIsSym n_NI_Local_Get_Nak63sIsSym n_NI_Nak66sIsSym n_PI_Remote_Replace68sIsSym n_PI_Remote_PutX71sIsSym n_PI_Remote_GetX80sIsSym n_PI_Remote_Get84sIsSym n_Store_Home85sIsSym n_Store86sIsSym rules'_def symProtRulesUnion by presburger 



subsection{*Definitions of each abstracted rule*}

definition  NC::"nat " where [simp]: "NC==1"

definition n_NI_InvAck_311_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_InvAck_311_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(\<forall>\<^sub>fj. (IVar (Para (''false | Sta.Dir.InvSet'') j)) =\<^sub>f  (Const false) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const false) 
 \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index k)) )M
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_InvAck) )M \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_Inv) )M

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const false)))"

definition n_NI_InvAck_212_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_InvAck_212_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(\<forall>\<^sub>fj. (IVar (Para (''Sta.Dir.InvSet'') j)) =\<^sub>f  (Const false) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false) 
 \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index k)) )M
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_InvAck) )M \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_Inv) )M

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const false)))"

definition n_NI_InvAck_113_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_InvAck_113_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(\<forall>\<^sub>fj. (IVar (Para (''Sta.Dir.InvSet'') j)) =\<^sub>f  (Const false) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const false) 
 \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index k)) )M
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_InvAck) )M \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_Inv) )M

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const false )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))"

definition n_NI_InvAck_exists14_NODE_1_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_InvAck_exists14_NODE_1_abs  j M\<equiv>
(IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_InvAck)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') j)) =\<^sub>f  (Const true)  \<and>\<^sub>f
(IVar (Ident ''''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const false) 
 \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index k)) )M


   \<triangleright>
(assign (Para (''Sta.InvMsg.Cmd'') j, (Const INV_None )))||
(assign (Para (''Sta.Dir.InvSet'') j, (Const false)))"

definition n_NI_Remote_GetX_PutX_Home24_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX_Home24_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) 
 \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.InvSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_PutX) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_Inv) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_InvAck) )M


   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_PutX)))"

definition n_NI_Remote_GetX_PutX25_NODE_1_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX25_NODE_1_abs  j M\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_InvAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index j))  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_PutX)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_Inv) 

   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_PutX )))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_FAck )))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index j) )))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_GetX_PutX25_NODE_2_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX25_NODE_2_abs  k M\<equiv>
(IVar (Para (''Sta.Proc.CacheState'') k)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.InvMarked'') k)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_Inv)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') k)) =\<^sub>f  (Const UNI_Put)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') k)) =\<^sub>f  (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') k)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') k)) =\<^sub>f  (Const CACHE_S)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_InvAck) 
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index j)) )M


   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') k, (Const CACHE_I )))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_FAck )))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index (M+1)) )))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_GetX_PutX25_NODE_1_NODE_2_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX25_NODE_1_NODE_2_abs  M\<equiv>
\<not>\<^sub>f (IVar (Ident ''Other'')) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) 
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index j)) )M \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_PutX) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_Inv) )M \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.InvSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_InvAck) )M
 \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') k)) =\<^sub>f  (Const UNI_Put) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_InvAck) )M \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Para (''Sta.Proc.InvMarked'') k)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_Inv) )M \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Para (''Sta.Dir.InvSet'') k)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Para (''Sta.Dir.ShrSet'') k)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') k)) =\<^sub>f  (Const CACHE_S) )M

   \<triangleright>
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_FAck )))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index (M+1)) )))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_GetX_Nak_Home26_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_Home26_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Nak )))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_GetX_Nak27_NODE_1_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak27_NODE_1_abs  j M\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index j))  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) 

   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_Nak )))||
(assign (Para (''Sta.UniMsg.Proc'') j, (Const (index (M+1)) )))||
(assign (Para (''Sta.UniMsg.HomeProc'') j, (Const false )))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_GetX_Nak27_NODE_2_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak27_NODE_2_abs  k M\<equiv>
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') k)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.InvMarked'') k)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_Inv)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') k)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') k)) =\<^sub>f  (Const UNI_Put)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') k)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') k)) =\<^sub>f  (Const CACHE_S)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_InvAck) 
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index j)) )M


   \<triangleright>
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_GetX_Nak27_NODE_1_NODE_2_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak27_NODE_1_NODE_2_abs  k M\<equiv>
\<not>\<^sub>f (IVar (Ident ''Other'')) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) 
 \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Para (''Sta.Proc.InvMarked'') k)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_Inv) )M \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Para (''Sta.Dir.InvSet'') k)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') k)) =\<^sub>f  (Const UNI_Put) )M \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Para (''Sta.Dir.ShrSet'') k)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') k)) =\<^sub>f  (Const CACHE_S) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_InvAck) )M
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index j)) )M

   \<triangleright>
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Local_GetX_PutX_1128_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_1128_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_E) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))M||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))M"

definition n_NI_Local_GetX_PutX_1029_NODE_1_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_1029_NODE_1_abs  j M\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') j)) =\<^sub>f  (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index j))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) 
 \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index k)) )M


   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index j))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_PutX)))"

definition n_NI_Local_GetX_PutX_1029_NODE_2_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_1029_NODE_2_abs  k M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') k)) =\<^sub>f  (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))"

definition n_NI_Local_GetX_PutX_1029_NODE_1_NODE_2_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_1029_NODE_1_NODE_2_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) 
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index (M+1))) )M


   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))"

definition n_NI_Local_GetX_PutX_10_Home30_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_10_Home30_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))"

definition n_NI_Local_GetX_PutX_931_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_931_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))"

definition n_NI_Local_GetX_PutX_932_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_932_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))"

definition n_NI_Local_GetX_PutX_8_NODE_Get33_NODE_1_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_8_NODE_Get33_NODE_1_abs  j M\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') j)) =\<^sub>f  (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index j))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get) 
 \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index k)) )M


   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index j))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_8_NODE_Get33_NODE_2_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_8_NODE_Get33_NODE_2_abs  k M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') k)) =\<^sub>f  (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_8_NODE_Get33_NODE_1_NODE_2_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_8_NODE_Get33_NODE_1_NODE_2_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get) 
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index (M+1))) )M


   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_834_NODE_1_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_834_NODE_1_abs  j M\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') j)) =\<^sub>f  (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index j))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get) 
 \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index k)) )M


   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index j))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_834_NODE_2_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_834_NODE_2_abs  k M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') k)) =\<^sub>f  (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_834_NODE_1_NODE_2_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_834_NODE_1_NODE_2_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get) 
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index (M+1))) )M


   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_8_Home_NODE_Get35_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_8_Home_NODE_Get35_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_8_Home36_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_8_Home36_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_7_NODE_Get37_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_7_NODE_Get37_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_7_NODE_Get38_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_7_NODE_Get38_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_739_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_739_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_740_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_740_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_641_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_641_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) 
 \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) )M


   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))M||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))M"

definition n_NI_Local_GetX_PutX_542_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_542_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get) 
 \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) )M


   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))M||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))M"

definition n_NI_Local_GetX_PutX_443_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_443_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get) 
 \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) )M


   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))M||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))M"

definition n_NI_Local_GetX_PutX_344_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_344_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))M||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))M"

definition n_NI_Local_GetX_PutX_245_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_245_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_Get) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))M||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))M"

definition n_NI_Local_GetX_PutX_146_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_146_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_Get) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))M||
forallStm(\<lambda>p. (assign (Para (''Sta.Dir.InvSet'') p, (Const false))))M"

definition n_NI_Local_GetX_GetX47_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_GetX47_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index (M+1))) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))"

definition n_NI_Local_GetX_GetX48_NODE_1_abs:: rule where
"n_NI_Local_GetX_GetX48_NODE_1_abs  \<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const true) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))"

definition n_NI_Remote_Get_Put_Home52_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put_Home52_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) 
 \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.InvSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_PutX) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_Inv) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_InvAck) )M


   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Put)))"

definition n_NI_Remote_Get_Put53_NODE_1_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put53_NODE_1_abs  j M\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_InvAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index j))  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_PutX)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_Inv)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) 

   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_Put )))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_ShWb )))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index j) )))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_Get_Put53_NODE_2_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put53_NODE_2_abs  k M\<equiv>
(IVar (Para (''Sta.Proc.CacheState'') k)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.InvMarked'') k)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') k)) =\<^sub>f  (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') k)) =\<^sub>f  (Const UNI_Put)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') k)) =\<^sub>f  (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_InvAck)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_Inv)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') k)) =\<^sub>f  (Const CACHE_S)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) 
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index j)) )M


   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') k, (Const CACHE_S )))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_ShWb )))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index (M+1)) )))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false )))"

definition n_NI_Remote_Get_Put53_NODE_1_NODE_2_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put53_NODE_1_NODE_2_abs  M\<equiv>
\<not>\<^sub>f (IVar (Ident ''Other'')) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) 
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index j)) )M \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_PutX) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_Inv) )M \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.InvSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_InvAck) )M
 \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') k)) =\<^sub>f  (Const UNI_Put) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_InvAck) )M \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Para (''Sta.Proc.InvMarked'') k)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_Inv) )M \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Para (''Sta.Dir.InvSet'') k)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Para (''Sta.Dir.ShrSet'') k)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') k)) =\<^sub>f  (Const CACHE_S) )M

   \<triangleright>
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_ShWb )))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index (M+1)) )))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_Get_Nak_Home54_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak_Home54_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Nak )))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_Get_Nak55_NODE_1_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak55_NODE_1_abs  j M\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index j))  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) 

   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_Nak )))||
(assign (Para (''Sta.UniMsg.Proc'') j, (Const (index (M+1)) )))||
(assign (Para (''Sta.UniMsg.HomeProc'') j, (Const false )))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_Get_Nak55_NODE_2_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak55_NODE_2_abs  k M\<equiv>
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') k)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.InvMarked'') k)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_Inv)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') k)) =\<^sub>f  (Const false)  \<and>\<^sub>f
(IVar (Para (''Sta.Dir.InvSet'') k)) =\<^sub>f  (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') k)) =\<^sub>f  (Const UNI_Put)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_InvAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') k)) =\<^sub>f  (Const CACHE_S)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) 
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index j)) )M


   \<triangleright>
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_Get_Nak55_NODE_1_NODE_2_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak55_NODE_1_NODE_2_abs  M\<equiv>
\<not>\<^sub>f (IVar (Ident ''Other'')) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_FAck)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =\<^sub>f  (Const NAKC_Nakc)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const true) 
 \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Para (''Sta.Proc.InvMarked'') k)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_Inv) )M \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Para (''Sta.Dir.ShrSet'') k)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>k. (IVar (Para (''Sta.Dir.InvSet'') k)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') k)) =\<^sub>f  (Const UNI_Put) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') k)) =\<^sub>f  (Const INV_InvAck) )M \<and>\<^sub>f
forallForm(\<lambda>k. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') k)) =\<^sub>f  (Const CACHE_S) )M
 \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index j)) )M

   \<triangleright>
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Local_Get_Put_Dirty56_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Put_Dirty56_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_E) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Dirty''), (Const false )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)) )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_S)))"

definition n_NI_Local_Get_Put57_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Put57_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index (M+1)) )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))"

definition n_NI_Local_Get_Put_Head58_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Put_Head58_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.ShrVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (IVar (Ident (''Sta.Dir.HomeShrSet'')))))"

definition n_NI_Local_Get_Get59_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Get59_NODE_1_abs  M\<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index (M+1))) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))"

definition n_NI_Local_Get_Get60_NODE_1_abs:: rule where
"n_NI_Local_Get_Get60_NODE_1_abs  \<equiv>
(IVar (Ident ''Sta.Dir.Pending''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =\<^sub>f (Const true) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))"

definition n_PI_Remote_PutX71_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_PI_Remote_PutX71_NODE_1_abs  M\<equiv>
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) 
 \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.InvSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_PutX) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_Inv) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_InvAck) )M


   \<triangleright>
(assign ((Ident ''Sta.WbMsg.Cmd''), (Const WB_Wb )))||
(assign ((Ident ''Sta.WbMsg.Proc''), (Const (index (M+1)) )))||
(assign ((Ident ''Sta.WbMsg.HomeProc''), (Const false)))"

definition n_Store86_NODE_1_abs::"nat \<Rightarrow> rule" where [simp]:
"n_Store86_NODE_1_abs  M\<equiv>
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true) 
 \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.InvSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_PutX) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_Inv) )M \<and>\<^sub>f
forallForm(\<lambda>j. \<not>\<^sub>f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =\<^sub>f  (Const INV_InvAck) )M


   \<triangleright>
"

