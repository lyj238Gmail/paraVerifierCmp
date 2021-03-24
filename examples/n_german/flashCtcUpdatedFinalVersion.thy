theory flashCtcUpdatedFinalVersion
  imports ECMP
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
"initSpec3 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.Dir.ShrSet'') p)) =\<^sub>f  (Const false) ) N "

definition initSpec4::"nat \<Rightarrow> formula" where [simp]:
"initSpec4 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.Dir.InvSet'') p)) =\<^sub>f  (Const false) ) N "

definition initSpec5::"nat \<Rightarrow> formula" where [simp]:
"initSpec5 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.UniMsg.Cmd'') p)) =\<^sub>f  (Const UNI_None) ) N "

definition initSpec6::"nat \<Rightarrow> formula" where [simp]:
"initSpec6 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.InvMsg.Cmd'') p)) =\<^sub>f  (Const INV_None) ) N "

definition initSpec7::"nat \<Rightarrow> formula" where [simp]:
"initSpec7 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.RpMsg.Cmd'') p)) =\<^sub>f  (Const RP_None) ) N "

definition initSpec8::"nat \<Rightarrow> formula" where [simp]:
"initSpec8 N\<equiv> (\<forall>\<^sub>fp. (IVar (Para (''Sta.UniMsg.HomeProc'') p)) =\<^sub>f  (Const false) ) N "

definition initSpec9::"formula" where [simp]:
"initSpec9 \<equiv> (IVar (Ident ''Sta.HomeUniMsg.HomeProc'')) =\<^sub>f  (Const false) "

definition initSpec10::"formula" where [simp]:
"initSpec10 \<equiv> (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =\<^sub>f  (Const UNI_None) "

definition initSpec11::"formula" where [simp]:
"initSpec11 \<equiv> (IVar (Ident ''Sta.HomeInvMsg.Cmd'')) =\<^sub>f  (Const INV_None) "

definition initSpec12::"formula" where [simp]:
"initSpec12 \<equiv> (IVar (Ident ''Sta.HomeRpMsg.Cmd'')) =\<^sub>f  (Const RP_None) "

definition initSpec13::"formula" where [simp]:
"initSpec13 \<equiv> (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =\<^sub>f  (Const NODE_None) "

definition initSpec14::"formula" where [simp]:
"initSpec14 \<equiv> (IVar (Ident ''Sta.HomeProc.InvMarked'')) =\<^sub>f  (Const false) "

definition initSpec15::"formula" where [simp]:
"initSpec15 \<equiv> (IVar (Ident ''Sta.HomeProc.CacheState'')) =\<^sub>f  (Const CACHE_I) "

definition initSpec16::"formula" where [simp]:
"initSpec16 \<equiv> (IVar (Ident ''Sta.Dir.HomeShrSet'')) =\<^sub>f  (Const false) "

definition initSpec17::"formula" where [simp]:
"initSpec17 \<equiv> (IVar (Ident ''Sta.Dir.HomeInvSet'')) =\<^sub>f  (Const false) "

definition initSpec18::"formula" where [simp]:
"initSpec18 \<equiv> (IVar (Ident ''Sta.LastWrVld'')) =\<^sub>f  (Const false) "

definition initSpec19::"formula" where [simp]:
"initSpec19 \<equiv> (IVar (Ident ''Sta.Collecting'')) =\<^sub>f  (Const false) "

definition initSpec20::"formula" where [simp]:
"initSpec20 \<equiv> (IVar (Ident ''Sta.FwdCmd'')) =\<^sub>f  (Const UNI_None) "

definition env::"envType" where [simp]:
"env == (%v. case v of
   Ident ''Sta.FwdCmd'' \<Rightarrow> enumType
  |Ident ''Sta.Collecting'' \<Rightarrow> boolType
  |Ident ''Sta.LastWrVld'' \<Rightarrow>   boolType
  |Ident ''Sta.Dir.HomeShrSet'' \<Rightarrow>  boolType 
  |Ident ''Sta.HomeProc.CacheState'' \<Rightarrow>  enumType
  |Ident ''Sta.Dir.HomeInvSet''\<Rightarrow>  boolType 
  |Ident ''Sta.HomeProc.InvMarked'' => boolType
  |Ident ''Sta.HomeProc.ProcCmd'' => enumType
  |Ident ''Sta.HomeRpMsg.Cmd'' => enumType
  |Ident ''Sta.HomeInvMsg.Cmd'' => enumType

  |Ident ''Sta.HomeUniMsg.Cmd'' => enumType
  |Ident ''Sta.HomeUniMsg.HomeProc'' => boolType

  |Para ''Sta.UniMsg.HomeProc'' i => boolType
 
  |Para (''Sta.RpMsg.Cmd'') i => enumType

  |Para (''Sta.InvMsg.Cmd'') i => enumType

  |Para (''Sta.UniMsg.Cmd'') i => enumType

  |Para (''Sta.Dir.InvSet'') i => boolType
  |Para (''Sta.Dir.ShrSet'') i => boolType

  |Para (''Sta.Proc.CacheState'') i => enumType
  |Para (''Sta.Proc.ProcCmd'') i => enumType
  |Para (''Sta.Proc.InvMarked'') i => boolType
  |_ \<Rightarrow>  anyType)" 

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
"absTransfForm M initSpec9 = initSpec9"
"absTransfForm M initSpec10 = initSpec10"
"absTransfForm M initSpec11 = initSpec11"
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
(initSpec9),
(initSpec10),
(initSpec11),
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
  "symPredSet' N ({(initSpec9 )} )"
  unfolding symPredSet'_def initSpec9_def by auto

lemma symPreds10[intro]:
  "symPredSet' N ({(initSpec10 )} )"
  unfolding symPredSet'_def initSpec10_def by auto

lemma symPreds11[intro]:
  "symPredSet' N ({(initSpec11 )} )"
  unfolding symPredSet'_def initSpec11_def by auto

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
    {initSpec9} \<union>
    {initSpec10} \<union>
    {initSpec11} \<union>
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
    {(initSpec9 )}\<union>
    {(initSpec10 )}\<union>
    {(initSpec11 )}\<union>
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

definition n_Store::"nat \<Rightarrow> rule" where 
"n_Store  src \<equiv>
(IVar (Para (''Sta.Proc.CacheState'') src)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign (Para (''Sta.Proc.CacheData'') src, (IVar(Ident ''data''))))||
(assign ((Ident ''Sta.CurrData''), (IVar(Ident ''data''))))||
(assign ((Ident ''Sta.LastWrVld''), (Const true)))||
(assign ((Ident ''Sta.LastWrPtr''), (Const (index src))))"

lemma symStore:
  "symParamRule N n_Store"
  "wellFormedStatement N (act (n_Store i))"
  "absTransfRule M (n_Store i) = (if i \<le> M then n_Store i else chaos
\<triangleright> skip)"
  unfolding n_Store_def symParamRule_def by auto

definition n_Store_Home::"nat \<Rightarrow> rule" where 
"n_Store_Home  src \<equiv>
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_E) 
   \<triangleright>
(assign ((Ident ''Sta.HomeProc.CacheData''), (IVar(Ident ''data''))))||
(assign ((Ident ''Sta.CurrData''), (IVar(Ident ''data''))))||
(assign ((Ident ''Sta.LastWrVld''), (Const true)))||
(assign ((Ident ''Sta.LastWrPtr''), (Const (index src))))"

lemma symStore_Home:
  "symParamRule N n_Store_Home"
  "wellFormedStatement N (act (n_Store_Home i))"
  "absTransfRule M (n_Store_Home i) = (if i \<le> M then n_Store_Home i else chaos
\<triangleright> skip)"
  unfolding n_Store_Home_def symParamRule_def by auto

definition n_PI_Remote_Get::"nat \<Rightarrow> rule" where 
"n_PI_Remote_Get  src \<equiv>
(IVar (Para (''Sta.Proc.ProcCmd'') src)) =\<^sub>f  (Const NODE_None)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') src)) =\<^sub>f  (Const CACHE_I) 
   \<triangleright>
(assign (Para (''Sta.Proc.ProcCmd'') src, (Const NODE_Get)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Get)))||
(assign ((Ident ''Sta.HomeUniMsg.HomeProc''), (Const true)))"

lemma symPI_Remote_Get:
  "symParamRule N n_PI_Remote_Get"
  "wellFormedStatement N (act (n_PI_Remote_Get i))"
  "absTransfRule M (n_PI_Remote_Get i) = (if i \<le> M then n_PI_Remote_Get i else chaos
\<triangleright> skip)"
  unfolding n_PI_Remote_Get_def symParamRule_def by auto

definition n_PI_Remote_Get_Home::"nat \<Rightarrow> rule" where 
"n_PI_Remote_Get_Home  src \<equiv>
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_None)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_I) 
   \<triangleright>
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_Get)))||
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Get)))||
(assign ((Ident ''Sta.HomeUniMsg.HomeProc''), (Const true)))"

lemma symPI_Remote_Get_Home:
  "symParamRule N n_PI_Remote_Get_Home"
  "wellFormedStatement N (act (n_PI_Remote_Get_Home i))"
  "absTransfRule M (n_PI_Remote_Get_Home i) = (if i \<le> M then n_PI_Remote_Get_Home i else chaos
\<triangleright> skip)"
  unfolding n_PI_Remote_Get_Home_def symParamRule_def by auto

definition n_PI_Remote_GetX::"nat \<Rightarrow> rule" where 
"n_PI_Remote_GetX  src \<equiv>
(IVar (Para (''Sta.Proc.ProcCmd'') src)) =\<^sub>f  (Const NODE_None)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') src)) =\<^sub>f  (Const CACHE_I) 
   \<triangleright>
(assign (Para (''Sta.Proc.ProcCmd'') src, (Const NODE_GetX)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_GetX)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

lemma symPI_Remote_GetX:
  "symParamRule N n_PI_Remote_GetX"
  "wellFormedStatement N (act (n_PI_Remote_GetX i))"
  "absTransfRule M (n_PI_Remote_GetX i) = (if i \<le> M then n_PI_Remote_GetX i else chaos
\<triangleright> skip)"
  unfolding n_PI_Remote_GetX_def symParamRule_def by auto

definition n_PI_Remote_GetX_Home::"nat \<Rightarrow> rule" where 
"n_PI_Remote_GetX_Home  src \<equiv>
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_None)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_I) 
   \<triangleright>
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_GetX)))||
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_GetX)))||
(assign ((Ident ''Sta.HomeUniMsg.HomeProc''), (Const true)))"

lemma symPI_Remote_GetX_Home:
  "symParamRule N n_PI_Remote_GetX_Home"
  "wellFormedStatement N (act (n_PI_Remote_GetX_Home i))"
  "absTransfRule M (n_PI_Remote_GetX_Home i) = (if i \<le> M then n_PI_Remote_GetX_Home i else chaos
\<triangleright> skip)"
  unfolding n_PI_Remote_GetX_Home_def symParamRule_def by auto

definition n_PI_Remote_PutX::"nat \<Rightarrow> rule" where 
"n_PI_Remote_PutX  dst \<equiv>
(IVar (Para (''Sta.Proc.ProcCmd'') dst)) =\<^sub>f  (Const NODE_None)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign ((Ident ''Sta.WbMsg.Cmd''), (Const WB_Wb)))||
(assign ((Ident ''Sta.WbMsg.Proc''), (Const (index dst))))||
(assign ((Ident ''Sta.WbMsg.Data''), (IVar (Para (''Sta.Proc.CacheData'') dst))))"

lemma symPI_Remote_PutX:
  "symParamRule N n_PI_Remote_PutX"
  "wellFormedStatement N (act (n_PI_Remote_PutX i))"
  "absTransfRule M (n_PI_Remote_PutX i) = (if i \<le> M then n_PI_Remote_PutX i else chaos
\<triangleright> skip)"
  unfolding n_PI_Remote_PutX_def symParamRule_def by auto

definition n_PI_Remote_Replace::"nat \<Rightarrow> rule" where 
"n_PI_Remote_Replace  src \<equiv>
(IVar (Para (''Sta.Proc.ProcCmd'') src)) =\<^sub>f  (Const NODE_None)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') src)) =\<^sub>f  (Const CACHE_S) 
   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') src, (Const CACHE_I)))||
(assign (Para (''Sta.RpMsg.Cmd'') src, (Const RP_Replace)))"

lemma symPI_Remote_Replace:
  "symParamRule N n_PI_Remote_Replace"
  "wellFormedStatement N (act (n_PI_Remote_Replace i))"
  "absTransfRule M (n_PI_Remote_Replace i) = (if i \<le> M then n_PI_Remote_Replace i else chaos
\<triangleright> skip)"
  unfolding n_PI_Remote_Replace_def symParamRule_def by auto

definition n_NI_Nak::"nat \<Rightarrow> rule" where 
"n_NI_Nak  dst \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =\<^sub>f  (Const UNI_Nak) 
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''Sta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''Sta.Proc.InvMarked'') dst, (Const false)))"

lemma symNI_Nak:
  "symParamRule N n_NI_Nak"
  "wellFormedStatement N (act (n_NI_Nak i))"
  "absTransfRule M (n_NI_Nak i) = (if i \<le> M then n_NI_Nak i else chaos
\<triangleright> skip)"
  unfolding n_NI_Nak_def symParamRule_def by auto

definition n_NI_Nak_Home::"nat \<Rightarrow> rule" where 
"n_NI_Nak_Home  dst \<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Nak) 
   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const false)))"

lemma symNI_Nak_Home:
  "symParamRule N n_NI_Nak_Home"
  "wellFormedStatement N (act (n_NI_Nak_Home i))"
  "absTransfRule M (n_NI_Nak_Home i) = (if i \<le> M then n_NI_Nak_Home i else chaos
\<triangleright> skip)"
  unfolding n_NI_Nak_Home_def symParamRule_def by auto

definition n_NI_Local_Get_Nak::"nat \<Rightarrow> rule" where 
"n_NI_Local_Get_Nak  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace)  \<and>\<^sub>f
IVar (Ident ''
  ( Sta.Dir.Pending |
    Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident '' Sta.Dir.Local '') =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.CacheState'')) =\<^sub>f  (Const CACHE_E |)  \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const src )) 
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

lemma symNI_Local_Get_Nak:
  "symParamRule N n_NI_Local_Get_Nak"
  "wellFormedStatement N (act (n_NI_Local_Get_Nak i))"
  "absTransfRule M (n_NI_Local_Get_Nak i) = (if i \<le> M then n_NI_Local_Get_Nak i else chaos
\<triangleright> skip)"
  unfolding n_NI_Local_Get_Nak_def symParamRule_def by auto

definition n_NI_Local_Get_Get::"nat \<Rightarrow> rule" where 
"n_NI_Local_Get_Get  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace)  \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Pending '') =\<^sub>f  (Const false) \<and>\<^sub>f
IVar (Ident '' Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index src)) 
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Get)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident ''StaDirHeadPtr''))))||
(assign ((Ident ''Sta.Collecting''), (Const false)))"

lemma symNI_Local_Get_Get:
  "symParamRule N n_NI_Local_Get_Get"
  "wellFormedStatement N (act (n_NI_Local_Get_Get i))"
  "absTransfRule M (n_NI_Local_Get_Get i) = (if i \<le> M then n_NI_Local_Get_Get i else chaos
\<triangleright> skip)"
  unfolding n_NI_Local_Get_Get_def symParamRule_def by auto

definition n_NI_Local_Get_Put::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_Get_Put  src  \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace)  \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Pending '') =\<^sub>f  (Const false) \<and>\<^sub>f
IVar (Ident ''
  (Sta.Dir.Dirty -> Sta.Dir.Local '') =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_E)) 
   \<triangleright>
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.MemData''), (Const Sta.HomeProc.CacheData)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_S)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Put)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))||
(assign (Para (''Sta.UniMsg.Data'') src, (IVar (Ident ''StaHomeProcCacheData''))))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const true)))||
(assign (Para (''Sta.Dir.ShrSet'') src, (Const true)))||
forallStm(\<lambda>j. (assign (Para (''Sta.Dir.InvSet'') p, (IVar (Para (''(p = src) | Sta.Dir.ShrSet'') p)))))N||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const (p = src) | Sta.Dir.HomeShrSet)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Put)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))||
(assign (Para (''Sta.UniMsg.Data'') src, (Const Sta.MemData)))"

lemma symNI_Local_Get_Put:
  "symParamRule N n_NI_Local_Get_Put"
  "wellFormedStatement N (act (n_NI_Local_Get_Put i))"
  "absTransfRule M (n_NI_Local_Get_Put i) = (if i \<le> M then n_NI_Local_Get_Put i else chaos
\<triangleright> skip)"
  unfolding n_NI_Local_Get_Put_def symParamRule_def by auto

definition n_NI_Remote_Get_Nak::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Nak  src dst  \<equiv>
(\<not>\<^sub>f (Const (index src)) =\<^sub>f  (Const (index dst)))  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)) 
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (Const (index dst))))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

(*invariant "Lemma_21"
  forall src : NODE do forall dst : NODE do
      src != dst &
    Sta.UniMsg[src].Cmd = UNI_Get & Sta.UniMsg[src].Proc = dst ->
    Sta.Dir.Pending & !Sta.Dir.Local &
    !Sta.HomePendReqSrc & Sta.PendReqSrc = src & Sta.FwdCmd = UNI_Get
  end end;*)

definition invAux21 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where  
  "invAux21  src dst \<equiv>
     ((\<not>\<^sub>f(Const (index src) =\<^sub>f Const (index dst)))\<and>\<^sub>f
     IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const (UNI_Get) \<and>\<^sub>f
     IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) )  
      \<longrightarrow>\<^sub>f
    ( 
    ( IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true)  \<and>\<^sub>f
    (IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false)  \<and>\<^sub>f
    (IVar (Ident ''HomePendReqSrc'') =\<^sub>f Const false)  \<and>\<^sub>f
    (IVar (Ident ''Sta.PendReqSrc'' ) =\<^sub>f Const (index src))  \<and>\<^sub>f
     (IVar (Ident ''Sta.FwdCmd'' ) =\<^sub>f Const (UNI_Get))
    ) "


definition n_NI_Remote_Get_Nak_ref::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Nak_ref  src dst  \<equiv>
(\<not>\<^sub>f (Const (index src)) =\<^sub>f  (Const (index dst)))  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E))\<and>\<^sub>f
( IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true)  \<and>\<^sub>f
    (IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false)  \<and>\<^sub>f
    (IVar (Ident ''HomePendReqSrc'') =\<^sub>f Const false)  \<and>\<^sub>f
    (IVar (Ident ''Sta.PendReqSrc'' ) =\<^sub>f Const (index src))  \<and>\<^sub>f
     (IVar (Ident ''Sta.FwdCmd'' ) =\<^sub>f Const (UNI_Get)) 
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (Const (index dst))))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"


definition n_NI_Remote_Get_Nak_src_abs::" nat \<Rightarrow> nat\<Rightarrow>rule" where [simp]:
"n_NI_Remote_Get_Nak_src_abs  dst other\<equiv>
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local'') =\<^sub>f  (Const false) \<and>\<^sub>f
IVar (Ident ''HomePendReqSrc'') =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.PendReqSrc''))  =\<^sub>f (Const (index (Suc other)))  \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_Get) 

   \<triangleright>
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index (other +1)))))"

definition n_NI_Remote_Get_Nak_dst_abs::"nat  \<Rightarrow> nat\<Rightarrow>rule" where [simp]:
"n_NI_Remote_Get_Nak_dst_abs  src other \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f 
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index (Suc other)))\<and>\<^sub>f
IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local'') =\<^sub>f  (Const false) \<and>\<^sub>f
IVar (Ident ''HomePendReqSrc'') =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.PendReqSrc''))  =\<^sub>f (Const (index src))  \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_Get) 

   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (Const (index (Suc other)))))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"



definition n_NI_Remote_Get_Nak_src_dst_abs::"nat\<Rightarrow>rule" where [simp]:
"n_NI_Remote_Get_Nak_src_dst_abs  other\<equiv>
IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local'') =\<^sub>f  (Const false) \<and>\<^sub>f 
IVar (Ident ''HomePendReqSrc'') =\<^sub>f (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.PendReqSrc''))  =\<^sub>f (Const (index (Suc other)))  \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_Get) 

   \<triangleright>
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index (Suc other)))))"


 (*lemma "n_NI_Remote_Get_Nak_ref  i j=b"
  apply (auto  simp add:n_NI_Remote_Get_Nak_ref_def)*)
lemma n_RecvInvAck12Eq:
  "equivRule (strengthenRule2 (invAux21  i j) (n_NI_Remote_Get_Nak i j)) 
  ( n_NI_Remote_Get_Nak_ref  i j)"
   apply (auto  simp add: strengthenRule2.simps invAux21_def 
       n_NI_Remote_Get_Nak_ref_def n_NI_Remote_Get_Nak_def equivForm_def)
  done

definition symParamRule2' :: "nat \<Rightarrow> (nat \<Rightarrow>nat\<Rightarrow>rule) \<Rightarrow> bool" where
  "symParamRule2' N r =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j\<le>N 
      \<longrightarrow>   equivRule (applySym2Rule p (r i  j)) (r (p i) (p j)))" 

lemma symParamRule2I:
  "symParamForm2 N f \<Longrightarrow> symParamStatement2 N ps \<Longrightarrow> symParamRule2' N (\<lambda>i j. guard (f i j) (ps i j))"
  unfolding symParamRule2'_def symParamForm2_def symParamStatement2_def by auto


lemma symRecvInvAck12_ref1:
  "symParamRule2' N (n_NI_Remote_Get_Nak_ref )"
   
  unfolding n_NI_Remote_Get_Nak_ref_def  symParamRule2'_def
  apply (auto intro!: symParamRule2I symParamFormAnd symParamFormForallExcl)
  done

lemma symRecvInvAck12_ref2:
  
  "wellFormedStatement env N (act (n_NI_Remote_Get_Nak_ref  i j))"
    
  unfolding n_NI_Remote_Get_Nak_ref_def  
  by (auto intro!:   symParamFormAnd symParamFormForallExcl)

lemma symRecvInvAck12_ref31:
   
   "  i \<le> M & j\<le>M \<Longrightarrow> absTransfRule env M  (n_NI_Remote_Get_Nak_ref  i j) =
       (n_NI_Remote_Get_Nak_ref  i j) "
  unfolding n_NI_Remote_Get_Nak_ref_def n_NI_Remote_Get_Nak_def
  apply auto
  done

lemma symRecvInvAck12_ref32:
   
   "  i \<le> M & M<j \<Longrightarrow>absTransfRule env M  (n_NI_Remote_Get_Nak_ref  i j) =
        n_NI_Remote_Get_Nak_dst_abs i M "
  unfolding n_NI_Remote_Get_Nak_ref_def n_NI_Remote_Get_Nak_dst_abs_def
  apply auto
  done

lemma symRecvInvAck12_ref33:
   
   "  j \<le> M & M<i \<Longrightarrow>absTransfRule env M  (n_NI_Remote_Get_Nak_ref  i j) =
        n_NI_Remote_Get_Nak_src_abs j M "
  unfolding n_NI_Remote_Get_Nak_ref_def n_NI_Remote_Get_Nak_src_abs_def
  apply auto
  done

lemma symRecvInvAck12_ref34:
   
   "  M<i & M<j \<Longrightarrow>absTransfRule env M  (n_NI_Remote_Get_Nak_ref  i j) =
        n_NI_Remote_Get_Nak_src_dst_abs  M "
  unfolding n_NI_Remote_Get_Nak_ref_def n_NI_Remote_Get_Nak_src_dst_abs_def
  apply auto
  done

lemma symRecvInvAck12_ref3:
   
   " absTransfRule M (n_NI_Remote_Get_Nak_ref  i j) =
    (if i \<le> M & j\<le>M then  (n_NI_Remote_Get_Nak_ref  i j)
     else if (i\<le>M \<and> j>M) then (n_NI_Remote_Get_Nak_dst_abs i M)
     else if (i>M \<and> j\<le>M) then (n_NI_Remote_Get_Nak_src_abs j)
     else n_NI_Remote_Get_Nak_src_dst_abs)"
   
  unfolding n_NI_Remote_Get_Nak_ref_def n_NI_Remote_Get_Nak_def
    n_NI_Remote_Get_Nak_dst_abs_def n_NI_Remote_Get_Nak_src_abs_def
    n_NI_Remote_Get_Nak_src_dst_abs_def apply auto

lemma symRecvInvAck12_ref:
  "symParamRule N (n_RecvInvAck12_ref N)"
  "wellFormedStatement N (act (n_RecvInvAck12_ref N i))"
   "M \<le> N \<Longrightarrow> absTransfRule M (n_RecvInvAck12_ref N i) =
    (if i \<le> M then n_RecvInvAck1 i else n_RecvInvAck12_abs M)"
  unfolding n_RecvInvAck12_ref_def n_NI_Remote_Get_Nak_ref  i j
  apply (auto intro!: symParamRuleI symParamFormAnd symParamFormForallExcl)
  unfolding symParamForm_def symParamForm2_def symParamStatement_def apply auto[1]
  unfolding n_RecvInvAck1_def n_RecvInvAck12_ref_def n_RecvInvAck12_abs_def by auto
absTransfRule env M  (n_NI_Remote_Get_Nak_ref  i j)


(IVar (Para ''Sta.UniMsg.Cmd'' i) =\<^sub>f Const (enum ''control'' ''UNI_Get'') \<and>\<^sub>f
     IVar (Para ''Sta.UniMsg.Proc'' i) =\<^sub>f Const (index (Suc M)) \<and>\<^sub>f
     IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const (boolV True) \<and>\<^sub>f
     IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const (boolV False) \<and>\<^sub>f
     IVar (Ident ''HomePendReqSrc'') =\<^sub>f Const (boolV False) \<and>\<^sub>f
     IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index i) \<and>\<^sub>f
     IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const (enum ''control'' ''UNI_Get'') \<triangleright>
     assign (Para ''Sta.UniMsg.Cmd'' i, Const (enum ''control'' ''UNI_Nak'')) ||
     assign (Para ''Sta.UniMsg.Proc'' i, Const (index (Suc M))) ||
     assign (Ident ''Sta.NakcMsg.Cmd'', Const (enum ''control'' ''NAKC_Nakc'')) ||
     assign (Ident ''Sta.FwdCmd'', Const (enum ''control'' ''UNI_None'')) ||
     assign (Ident ''Sta.FwdSrc'', Const (index i))) =

(IVar (Para ''Sta.UniMsg.Cmd'' i) =\<^sub>f Const (enum ''control'' ''UNI_Get'') \<and>\<^sub>f
     IVar (Para ''Sta.UniMsg.Proc'' i) =\<^sub>f Const (index (Suc M)) \<and>\<^sub>f
     IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const (boolV True) \<and>\<^sub>f
     IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const (boolV False) \<and>\<^sub>f
     IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index i) \<and>\<^sub>f
     IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const (enum ''control'' ''UNI_Get'') \<triangleright>
     assign (Para ''Sta.UniMsg.Cmd'' i, Const (enum ''control'' ''UNI_Nak'')) ||
     assign (Para ''Sta.UniMsg.Proc'' i, Const (index (Suc M))) ||
     assign (Ident ''Sta.NakcMsg.Cmd'', Const (enum ''control'' ''NAKC_Nakc'')) ||
     assign (Ident ''Sta.FwdCmd'', Const (enum ''control'' ''UNI_None'')) ||
     assign (Ident ''Sta.FwdSrc'', Const (index i)))


definition symParamRule2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat\<Rightarrow> rule) \<Rightarrow> bool" where
  "symParamRule2 N r =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> 
  i \<le> N \<longrightarrow>j \<le> N\<longrightarrow>i\<noteq>j\<longrightarrow> equivRule (applySym2Rule p (r i j)) (r (p i) (p j)))"

lemma symNI_Remote_Get_Nak1:
  "symParamRule2 N n_NI_Remote_Get_Nak"
  unfolding n_NI_Remote_Get_Nak_def symParamRule2_def apply auto done

lemma symNI_Remote_Get_Nak2: 
  "wellFormedStatement N (act (n_NI_Remote_Get_Nak i j))"
  unfolding n_NI_Remote_Get_Nak_def   apply auto done

lemma symNI_Remote_Get_Nak3: 
  "absTransfRule M (n_NI_Remote_Get_Nak i j) = 
 (if i \<le> M then n_NI_Remote_Get_Nak i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_Get_Nak_def symParamRule_def by auto

lemma symNI_Remote_Get_Nak:
  "symParamRule N n_NI_Remote_Get_Nak"
  "wellFormedStatement N (act (n_NI_Remote_Get_Nak i))"
  "absTransfRule M (n_NI_Remote_Get_Nak i) = (if i \<le> M then n_NI_Remote_Get_Nak i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_Get_Nak_def symParamRule_def by auto

definition n_NI_Remote_Get_Nak_Home::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Nak_Home  src dst  \<equiv>
\<not>\<^sub>f (IVar (Ident ''src'')) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index dst))  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Nak)))||
(assign ((Ident ''Sta.HomeUniMsg.Proc''), (Const (index dst))))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

lemma symNI_Remote_Get_Nak_Home:
  "symParamRule N n_NI_Remote_Get_Nak_Home"
  "wellFormedStatement N (act (n_NI_Remote_Get_Nak_Home i))"
  "absTransfRule M (n_NI_Remote_Get_Nak_Home i) = (if i \<le> M then n_NI_Remote_Get_Nak_Home i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_Get_Nak_Home_def symParamRule_def by auto

definition n_NI_Remote_Get_Put::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Put  src dst  \<equiv>
\<not>\<^sub>f (IVar (Ident ''src'')) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_S)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Put)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (Const (index dst))))||
(assign (Para (''Sta.UniMsg.Data'') src, (IVar (Para (''Sta.Proc.CacheData'') dst))))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

lemma symNI_Remote_Get_Put:
  "symParamRule N n_NI_Remote_Get_Put"
  "wellFormedStatement N (act (n_NI_Remote_Get_Put i))"
  "absTransfRule M (n_NI_Remote_Get_Put i) = (if i \<le> M then n_NI_Remote_Get_Put i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_Get_Put_def symParamRule_def by auto

definition n_NI_Remote_Get_Put_Home::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Put_Home  src dst  \<equiv>
\<not>\<^sub>f (IVar (Ident ''src'')) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index dst))  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_S)))||
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Put)))||
(assign ((Ident ''Sta.HomeUniMsg.Proc''), (Const (index dst))))||
(assign ((Ident ''Sta.HomeUniMsg.Data''), (IVar (Para (''Sta.Proc.CacheData'') dst))))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

lemma symNI_Remote_Get_Put_Home:
  "symParamRule N n_NI_Remote_Get_Put_Home"
  "wellFormedStatement N (act (n_NI_Remote_Get_Put_Home i))"
  "absTransfRule M (n_NI_Remote_Get_Put_Home i) = (if i \<le> M then n_NI_Remote_Get_Put_Home i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_Get_Put_Home_def symParamRule_def by auto

definition n_NI_Local_GetX_Nak::"nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_Nak  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true)  \<and>\<^sub>f
IVar (Ident ''
  ( Sta.Dir.Pending |
    Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident '' Sta.Dir.Local '') =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.CacheState'')) =\<^sub>f  (Const CACHE_E |)  \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =\<^sub>f (Const src )) 
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

lemma symNI_Local_GetX_Nak:
  "symParamRule N n_NI_Local_GetX_Nak"
  "wellFormedStatement N (act (n_NI_Local_GetX_Nak i))"
  "absTransfRule M (n_NI_Local_GetX_Nak i) = (if i \<le> M then n_NI_Local_GetX_Nak i else chaos
\<triangleright> skip)"
  unfolding n_NI_Local_GetX_Nak_def symParamRule_def by auto

definition n_NI_Local_GetX_GetX::"nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_GetX  src \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true)  \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Pending '') =\<^sub>f  (Const false) \<and>\<^sub>f
IVar (Ident '' Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.Dir.HeadPtr'')) =\<^sub>f  (Const (index src)) 
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_GetX)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident ''StaDirHeadPtr''))))||
(assign ((Ident ''Sta.Collecting''), (Const false)))"

lemma symNI_Local_GetX_GetX:
  "symParamRule N n_NI_Local_GetX_GetX"
  "wellFormedStatement N (act (n_NI_Local_GetX_GetX i))"
  "absTransfRule M (n_NI_Local_GetX_GetX i) = (if i \<le> M then n_NI_Local_GetX_GetX i else chaos
\<triangleright> skip)"
  unfolding n_NI_Local_GetX_GetX_def symParamRule_def by auto

definition n_NI_Local_GetX_PutX::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_PutX  src  \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true)  \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Pending '') =\<^sub>f  (Const false) \<and>\<^sub>f
IVar (Ident ''
  (Sta.Dir.Dirty -> Sta.Dir.Local '') =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_E)) 
   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(\<lambda>j. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))||
(assign (Para (''Sta.UniMsg.Data'') src, (IVar (Ident ''StaHomeProcCacheData''))))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(\<lambda>j. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))||
(assign (Para (''Sta.UniMsg.Data'') src, (Const Sta.MemData)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''if (Sta.HomeProc.ProcCmd''), (Const NODE_Get) then)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(\<lambda>j. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))||
(assign (Para (''Sta.UniMsg.Data'') src, (Const Sta.MemData)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''if (Sta.HomeProc.ProcCmd''), (Const NODE_Get) then)))||
(assign ((Ident ''Sta.Collecting''), (Const true)))||
(assign ((Ident ''Sta.PrevData''), (Const Sta.CurrData)))||
(assign ((Ident ''if (Sta.Dir.HeadPtr !''), (Const src) then)))"

lemma symNI_Local_GetX_PutX:
  "symParamRule N n_NI_Local_GetX_PutX"
  "wellFormedStatement N (act (n_NI_Local_GetX_PutX i))"
  "absTransfRule M (n_NI_Local_GetX_PutX i) = (if i \<le> M then n_NI_Local_GetX_PutX i else chaos
\<triangleright> skip)"
  unfolding n_NI_Local_GetX_PutX_def symParamRule_def by auto

definition n_NI_Remote_GetX_Nak::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_GetX_Nak  src dst  \<equiv>
\<not>\<^sub>f (IVar (Ident ''src'')) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (Const (index dst))))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

lemma symNI_Remote_GetX_Nak:
  "symParamRule N n_NI_Remote_GetX_Nak"
  "wellFormedStatement N (act (n_NI_Remote_GetX_Nak i))"
  "absTransfRule M (n_NI_Remote_GetX_Nak i) = (if i \<le> M then n_NI_Remote_GetX_Nak i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_GetX_Nak_def symParamRule_def by auto

definition n_NI_Remote_GetX_Nak_Home::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_GetX_Nak_Home  src dst  \<equiv>
\<not>\<^sub>f (IVar (Ident ''src'')) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index dst))  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Nak)))||
(assign ((Ident ''Sta.HomeUniMsg.Proc''), (Const (index dst))))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

lemma symNI_Remote_GetX_Nak_Home:
  "symParamRule N n_NI_Remote_GetX_Nak_Home"
  "wellFormedStatement N (act (n_NI_Remote_GetX_Nak_Home i))"
  "absTransfRule M (n_NI_Remote_GetX_Nak_Home i) = (if i \<le> M then n_NI_Remote_GetX_Nak_Home i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_GetX_Nak_Home_def symParamRule_def by auto

definition n_NI_Remote_GetX_PutX::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_GetX_PutX  src dst  \<equiv>
\<not>\<^sub>f (IVar (Ident ''src'')) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (Const (index dst))))||
(assign (Para (''Sta.UniMsg.Data'') src, (IVar (Para (''Sta.Proc.CacheData'') dst))))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_FAck)))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index src))))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

lemma symNI_Remote_GetX_PutX:
  "symParamRule N n_NI_Remote_GetX_PutX"
  "wellFormedStatement N (act (n_NI_Remote_GetX_PutX i))"
  "absTransfRule M (n_NI_Remote_GetX_PutX i) = (if i \<le> M then n_NI_Remote_GetX_PutX i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_GetX_PutX_def symParamRule_def by auto

definition n_NI_Remote_GetX_PutX_Home::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_Remote_GetX_PutX_Home  src dst  \<equiv>
\<not>\<^sub>f (IVar (Ident ''src'')) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index dst))  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeUniMsg.Proc''), (Const (index dst))))||
(assign ((Ident ''Sta.HomeUniMsg.Data''), (IVar (Para (''Sta.Proc.CacheData'') dst))))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

lemma symNI_Remote_GetX_PutX_Home:
  "symParamRule N n_NI_Remote_GetX_PutX_Home"
  "wellFormedStatement N (act (n_NI_Remote_GetX_PutX_Home i))"
  "absTransfRule M (n_NI_Remote_GetX_PutX_Home i) = (if i \<le> M then n_NI_Remote_GetX_PutX_Home i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_GetX_PutX_Home_def symParamRule_def by auto

definition n_NI_Remote_Put::"nat \<Rightarrow> rule" where 
"n_NI_Remote_Put  dst \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =\<^sub>f  (Const UNI_Put) 
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''Sta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''Sta.Proc.InvMarked'') dst, (Const false)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_S)))||
(assign (Para (''Sta.Proc.CacheData'') dst, (IVar (Para (''Sta.UniMsg.Data'') dst))))"

lemma symNI_Remote_Put:
  "symParamRule N n_NI_Remote_Put"
  "wellFormedStatement N (act (n_NI_Remote_Put i))"
  "absTransfRule M (n_NI_Remote_Put i) = (if i \<le> M then n_NI_Remote_Put i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_Put_def symParamRule_def by auto

definition n_NI_Remote_PutX::"nat \<Rightarrow> rule" where 
"n_NI_Remote_PutX  dst \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =\<^sub>f  (Const UNI_PutX)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.ProcCmd'') dst)) =\<^sub>f  (Const NODE_GetX) 
   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''Sta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''Sta.Proc.InvMarked'') dst, (Const false)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_E)))||
(assign (Para (''Sta.Proc.CacheData'') dst, (IVar (Para (''Sta.UniMsg.Data'') dst))))"

lemma symNI_Remote_PutX:
  "symParamRule N n_NI_Remote_PutX"
  "wellFormedStatement N (act (n_NI_Remote_PutX i))"
  "absTransfRule M (n_NI_Remote_PutX i) = (if i \<le> M then n_NI_Remote_PutX i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_PutX_def symParamRule_def by auto

definition n_NI_Inv::"nat \<Rightarrow> rule" where 
"n_NI_Inv  dst \<equiv>
(IVar (Para (''Sta.InvMsg.Cmd'') dst)) =\<^sub>f  (Const INV_Inv) 
   \<triangleright>
(assign (Para (''Sta.InvMsg.Cmd'') dst, (Const INV_InvAck)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign (Para (''if (Sta.Proc.ProcCmd'') dst, (Const NODE_Get) then)))"

lemma symNI_Inv:
  "symParamRule N n_NI_Inv"
  "wellFormedStatement N (act (n_NI_Inv i))"
  "absTransfRule M (n_NI_Inv i) = (if i \<le> M then n_NI_Inv i else chaos
\<triangleright> skip)"
  unfolding n_NI_Inv_def symParamRule_def by auto

definition n_NI_InvAck::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_InvAck  src  \<equiv>
(IVar (Para (''Sta.InvMsg.Cmd'') src)) =\<^sub>f  (Const INV_InvAck)  \<and>\<^sub>f
IVar (Ident ''
  Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident '' Sta.Dir.InvSet[src]  
'') =\<^sub>f  (Const true)
   \<triangleright>
(assign (Para (''Sta.InvMsg.Cmd'') src, (Const INV_None)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))||
forallStm(\<lambda>j. (assign ((Ident ''if (p !''), (IVar (Para (''src & Sta.Dir.InvSet'') p)))))N||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Collecting''), (Const false)))||
(assign ((Ident ''Sta.LastInvAck''), (Const (index src))))"

lemma symNI_InvAck:
  "symParamRule N n_NI_InvAck"
  "wellFormedStatement N (act (n_NI_InvAck i))"
  "absTransfRule M (n_NI_InvAck i) = (if i \<le> M then n_NI_InvAck i else chaos
\<triangleright> skip)"
  unfolding n_NI_InvAck_def symParamRule_def by auto

definition n_NI_Replace::"nat \<Rightarrow> rule" where 
"n_NI_Replace  src \<equiv>
(IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace) 
   \<triangleright>
(assign (Para (''Sta.RpMsg.Cmd'') src, (Const RP_None)))||
(assign (Para (''Sta.Dir.ShrSet'') src, (Const false)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))"

lemma symNI_Replace:
  "symParamRule N n_NI_Replace"
  "wellFormedStatement N (act (n_NI_Replace i))"
  "absTransfRule M (n_NI_Replace i) = (if i \<le> M then n_NI_Replace i else chaos
\<triangleright> skip)"
  unfolding n_NI_Replace_def symParamRule_def by auto

definition n_NI_Replace_Home::"nat \<Rightarrow> rule" where 
"n_NI_Replace_Home  src \<equiv>
(IVar (Ident ''Sta.HomeRpMsg.Cmd''))  =\<^sub>f (Const RP_Replace) 
   \<triangleright>
(assign ((Ident ''Sta.HomeRpMsg.Cmd''), (Const RP_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))"

lemma symNI_Replace_Home:
  "symParamRule N n_NI_Replace_Home"
  "wellFormedStatement N (act (n_NI_Replace_Home i))"
  "absTransfRule M (n_NI_Replace_Home i) = (if i \<le> M then n_NI_Replace_Home i else chaos
\<triangleright> skip)"
  unfolding n_NI_Replace_Home_def symParamRule_def by auto

subsection \<open>Putting everything together ---definition of rules\<close>

definition n_Stores::" nat\<Rightarrow>rule set" where 
  "n_Stores N== oneParamCons N  n_Store"

definition n_Store_Homes::" nat\<Rightarrow>rule set" where 
  "n_Store_Homes N== oneParamCons N  n_Store_Home"

definition n_PI_Remote_Gets::" nat\<Rightarrow>rule set" where 
  "n_PI_Remote_Gets N== oneParamCons N  n_PI_Remote_Get"

definition n_PI_Remote_Get_Homes::" nat\<Rightarrow>rule set" where 
  "n_PI_Remote_Get_Homes N== oneParamCons N  n_PI_Remote_Get_Home"

definition n_PI_Remote_GetXs::" nat\<Rightarrow>rule set" where 
  "n_PI_Remote_GetXs N== oneParamCons N  n_PI_Remote_GetX"

definition n_PI_Remote_GetX_Homes::" nat\<Rightarrow>rule set" where 
  "n_PI_Remote_GetX_Homes N== oneParamCons N  n_PI_Remote_GetX_Home"

definition n_PI_Remote_PutXs::" nat\<Rightarrow>rule set" where 
  "n_PI_Remote_PutXs N== oneParamCons N  n_PI_Remote_PutX"

definition n_PI_Remote_Replaces::" nat\<Rightarrow>rule set" where 
  "n_PI_Remote_Replaces N== oneParamCons N  n_PI_Remote_Replace"

definition n_NI_Naks::" nat\<Rightarrow>rule set" where 
  "n_NI_Naks N== oneParamCons N  n_NI_Nak"

definition n_NI_Nak_Homes::" nat\<Rightarrow>rule set" where 
  "n_NI_Nak_Homes N== oneParamCons N  n_NI_Nak_Home"

definition n_NI_Local_Get_Naks::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_Get_Naks N== oneParamCons N  n_NI_Local_Get_Nak"

definition n_NI_Local_Get_Gets::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_Get_Gets N== oneParamCons N  n_NI_Local_Get_Get"

definition n_NI_Local_Get_Puts::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_Get_Puts N== oneParamCons N  (n_NI_Local_Get_Put N)"

definition n_NI_Remote_Get_Naks::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Get_Naks N== oneParamCons N  n_NI_Remote_Get_Nak"

definition n_NI_Remote_Get_Nak_Homes::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Get_Nak_Homes N== oneParamCons N  n_NI_Remote_Get_Nak_Home"

definition n_NI_Remote_Get_Puts::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Get_Puts N== oneParamCons N  n_NI_Remote_Get_Put"

definition n_NI_Remote_Get_Put_Homes::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Get_Put_Homes N== oneParamCons N  n_NI_Remote_Get_Put_Home"

definition n_NI_Local_GetX_Naks::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_Naks N== oneParamCons N  n_NI_Local_GetX_Nak"

definition n_NI_Local_GetX_GetXs::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_GetXs N== oneParamCons N  n_NI_Local_GetX_GetX"

definition n_NI_Local_GetX_PutXs::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_PutXs N== oneParamCons N  (n_NI_Local_GetX_PutX N)"

definition n_NI_Remote_GetX_Naks::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_GetX_Naks N== oneParamCons N  n_NI_Remote_GetX_Nak"

definition n_NI_Remote_GetX_Nak_Homes::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_GetX_Nak_Homes N== oneParamCons N  n_NI_Remote_GetX_Nak_Home"

definition n_NI_Remote_GetX_PutXs::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_GetX_PutXs N== oneParamCons N  n_NI_Remote_GetX_PutX"

definition n_NI_Remote_GetX_PutX_Homes::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_GetX_PutX_Homes N== oneParamCons N  n_NI_Remote_GetX_PutX_Home"

definition n_NI_Remote_Puts::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Puts N== oneParamCons N  n_NI_Remote_Put"

definition n_NI_Remote_PutXs::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_PutXs N== oneParamCons N  n_NI_Remote_PutX"

definition n_NI_Invs::" nat\<Rightarrow>rule set" where 
  "n_NI_Invs N== oneParamCons N  n_NI_Inv"

definition n_NI_InvAcks::" nat\<Rightarrow>rule set" where 
  "n_NI_InvAcks N== oneParamCons N  (n_NI_InvAck N)"

definition n_NI_Replaces::" nat\<Rightarrow>rule set" where 
  "n_NI_Replaces N== oneParamCons N  n_NI_Replace"

definition n_NI_Replace_Homes::" nat\<Rightarrow>rule set" where 
  "n_NI_Replace_Homes N== oneParamCons N  n_NI_Replace_Home"

definition rules'::"nat \<Rightarrow> rule set" where [simp]:
"rules' N \<equiv>  (n_Stores N) \<union>
 (n_Store_Homes N) \<union>
 (n_PI_Remote_Gets N) \<union>
 (n_PI_Remote_Get_Homes N) \<union>
 (n_PI_Remote_GetXs N) \<union>
 (n_PI_Remote_GetX_Homes N) \<union>
 (n_PI_Remote_PutXs N) \<union>
 (n_PI_Remote_Replaces N) \<union>
 (n_NI_Naks N) \<union>
 (n_NI_Nak_Homes N) \<union>
 (n_NI_Local_Get_Naks N) \<union>
 (n_NI_Local_Get_Gets N) \<union>
 (n_NI_Local_Get_Puts N) \<union>
 (n_NI_Remote_Get_Naks N) \<union>
 (n_NI_Remote_Get_Nak_Homes N) \<union>
 (n_NI_Remote_Get_Puts N) \<union>
 (n_NI_Remote_Get_Put_Homes N) \<union>
 (n_NI_Local_GetX_Naks N) \<union>
 (n_NI_Local_GetX_GetXs N) \<union>
 (n_NI_Local_GetX_PutXs N) \<union>
 (n_NI_Remote_GetX_Naks N) \<union>
 (n_NI_Remote_GetX_Nak_Homes N) \<union>
 (n_NI_Remote_GetX_PutXs N) \<union>
 (n_NI_Remote_GetX_PutX_Homes N) \<union>
 (n_NI_Remote_Puts N) \<union>
 (n_NI_Remote_PutXs N) \<union>
 (n_NI_Invs N) \<union>
 (n_NI_InvAcks N) \<union>
 (n_NI_Replaces N) \<union>
 (n_NI_Replace_Homes N) 
"

lemma n_StoresIsSym:
  "symProtRules' N (n_Stores N)"
  using symStore(1) n_Stores_def symParaRuleInfSymRuleSet by auto

lemma n_Store_HomesIsSym:
  "symProtRules' N (n_Store_Homes N)"
  using symStore_Home(1) n_Store_Homes_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_GetsIsSym:
  "symProtRules' N (n_PI_Remote_Gets N)"
  using symPI_Remote_Get(1) n_PI_Remote_Gets_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_Get_HomesIsSym:
  "symProtRules' N (n_PI_Remote_Get_Homes N)"
  using symPI_Remote_Get_Home(1) n_PI_Remote_Get_Homes_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_GetXsIsSym:
  "symProtRules' N (n_PI_Remote_GetXs N)"
  using symPI_Remote_GetX(1) n_PI_Remote_GetXs_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_GetX_HomesIsSym:
  "symProtRules' N (n_PI_Remote_GetX_Homes N)"
  using symPI_Remote_GetX_Home(1) n_PI_Remote_GetX_Homes_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_PutXsIsSym:
  "symProtRules' N (n_PI_Remote_PutXs N)"
  using symPI_Remote_PutX(1) n_PI_Remote_PutXs_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_ReplacesIsSym:
  "symProtRules' N (n_PI_Remote_Replaces N)"
  using symPI_Remote_Replace(1) n_PI_Remote_Replaces_def symParaRuleInfSymRuleSet by auto

lemma n_NI_NaksIsSym:
  "symProtRules' N (n_NI_Naks N)"
  using symNI_Nak(1) n_NI_Naks_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Nak_HomesIsSym:
  "symProtRules' N (n_NI_Nak_Homes N)"
  using symNI_Nak_Home(1) n_NI_Nak_Homes_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Get_NaksIsSym:
  "symProtRules' N (n_NI_Local_Get_Naks N)"
  using symNI_Local_Get_Nak(1) n_NI_Local_Get_Naks_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Get_GetsIsSym:
  "symProtRules' N (n_NI_Local_Get_Gets N)"
  using symNI_Local_Get_Get(1) n_NI_Local_Get_Gets_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Get_PutsIsSym:
  "symProtRules' N (n_NI_Local_Get_Puts N)"
  using symNI_Local_Get_Put(1) n_NI_Local_Get_Puts_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_Get_NaksIsSym:
  "symProtRules' N (n_NI_Remote_Get_Naks N)"
  using symNI_Remote_Get_Nak(1) n_NI_Remote_Get_Naks_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_Get_Nak_HomesIsSym:
  "symProtRules' N (n_NI_Remote_Get_Nak_Homes N)"
  using symNI_Remote_Get_Nak_Home(1) n_NI_Remote_Get_Nak_Homes_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_Get_PutsIsSym:
  "symProtRules' N (n_NI_Remote_Get_Puts N)"
  using symNI_Remote_Get_Put(1) n_NI_Remote_Get_Puts_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_Get_Put_HomesIsSym:
  "symProtRules' N (n_NI_Remote_Get_Put_Homes N)"
  using symNI_Remote_Get_Put_Home(1) n_NI_Remote_Get_Put_Homes_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_NaksIsSym:
  "symProtRules' N (n_NI_Local_GetX_Naks N)"
  using symNI_Local_GetX_Nak(1) n_NI_Local_GetX_Naks_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_GetXsIsSym:
  "symProtRules' N (n_NI_Local_GetX_GetXs N)"
  using symNI_Local_GetX_GetX(1) n_NI_Local_GetX_GetXs_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_GetX_PutXsIsSym:
  "symProtRules' N (n_NI_Local_GetX_PutXs N)"
  using symNI_Local_GetX_PutX(1) n_NI_Local_GetX_PutXs_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_GetX_NaksIsSym:
  "symProtRules' N (n_NI_Remote_GetX_Naks N)"
  using symNI_Remote_GetX_Nak(1) n_NI_Remote_GetX_Naks_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_GetX_Nak_HomesIsSym:
  "symProtRules' N (n_NI_Remote_GetX_Nak_Homes N)"
  using symNI_Remote_GetX_Nak_Home(1) n_NI_Remote_GetX_Nak_Homes_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_GetX_PutXsIsSym:
  "symProtRules' N (n_NI_Remote_GetX_PutXs N)"
  using symNI_Remote_GetX_PutX(1) n_NI_Remote_GetX_PutXs_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_GetX_PutX_HomesIsSym:
  "symProtRules' N (n_NI_Remote_GetX_PutX_Homes N)"
  using symNI_Remote_GetX_PutX_Home(1) n_NI_Remote_GetX_PutX_Homes_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_PutsIsSym:
  "symProtRules' N (n_NI_Remote_Puts N)"
  using symNI_Remote_Put(1) n_NI_Remote_Puts_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_PutXsIsSym:
  "symProtRules' N (n_NI_Remote_PutXs N)"
  using symNI_Remote_PutX(1) n_NI_Remote_PutXs_def symParaRuleInfSymRuleSet by auto

lemma n_NI_InvsIsSym:
  "symProtRules' N (n_NI_Invs N)"
  using symNI_Inv(1) n_NI_Invs_def symParaRuleInfSymRuleSet by auto

lemma n_NI_InvAcksIsSym:
  "symProtRules' N (n_NI_InvAcks N)"
  using symNI_InvAck(1) n_NI_InvAcks_def symParaRuleInfSymRuleSet by auto

lemma n_NI_ReplacesIsSym:
  "symProtRules' N (n_NI_Replaces N)"
  using symNI_Replace(1) n_NI_Replaces_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Replace_HomesIsSym:
  "symProtRules' N (n_NI_Replace_Homes N)"
  using symNI_Replace_Home(1) n_NI_Replace_Homes_def symParaRuleInfSymRuleSet by auto

lemma rulesSym':
  shows "symProtRules' N (rules' N)"
  using n_StoresIsSym n_Store_HomesIsSym n_PI_Remote_GetsIsSym n_PI_Remote_Get_HomesIsSym n_PI_Remote_GetXsIsSym n_PI_Remote_GetX_HomesIsSym n_PI_Remote_PutXsIsSym n_PI_Remote_ReplacesIsSym n_NI_NaksIsSym n_NI_Nak_HomesIsSym n_NI_Local_Get_NaksIsSym n_NI_Local_Get_GetsIsSym n_NI_Local_Get_PutsIsSym n_NI_Remote_Get_NaksIsSym n_NI_Remote_Get_Nak_HomesIsSym n_NI_Remote_Get_PutsIsSym n_NI_Remote_Get_Put_HomesIsSym n_NI_Local_GetX_NaksIsSym n_NI_Local_GetX_GetXsIsSym n_NI_Local_GetX_PutXsIsSym n_NI_Remote_GetX_NaksIsSym n_NI_Remote_GetX_Nak_HomesIsSym n_NI_Remote_GetX_PutXsIsSym n_NI_Remote_GetX_PutX_HomesIsSym n_NI_Remote_PutsIsSym n_NI_Remote_PutXsIsSym n_NI_InvsIsSym n_NI_InvAcksIsSym n_NI_ReplacesIsSym n_NI_Replace_HomesIsSym rules'_def symProtRulesUnion by presburger 



subsection{*Definitions of each abstracted rule*}

definition  NC::"nat " where [simp]: "NC==1"

definition n_Store_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_Store_abs  src dst\<equiv>
IVar (Ident ''
  Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall p : NODE do Sta.Proc.CacheState'') p)) =\<^sub>f  (Const CACHE_E end) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.CacheState'')) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =\<^sub>f  (Const UNI_Put)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall q : NODE do Sta.UniMsg.Cmd'') q)) =\<^sub>f  (Const UNI_PutX end) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =\<^sub>f  (Const UNI_PutX) 

   \<triangleright>
(assign ((Ident ''Sta.CurrData''), (Const data)))||
(assign ((Ident ''Sta.LastWrVld''), (Const true)))||
(assign ((Ident ''Sta.LastWrPtr''), (IVar (Ident '' Other''))))"

definition n_PI_Remote_PutX_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_PI_Remote_PutX_abs  src dst\<equiv>
IVar (Ident ''
  Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall p : NODE do Sta.Proc.CacheState'') p)) =\<^sub>f  (Const CACHE_E end) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.CacheState'')) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =\<^sub>f  (Const UNI_Put)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall q : NODE do Sta.UniMsg.Cmd'') q)) =\<^sub>f  (Const UNI_PutX end) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =\<^sub>f  (Const UNI_PutX) 

   \<triangleright>
(assign ((Ident ''Sta.WbMsg.Cmd''), (Const WB_Wb)))||
(assign ((Ident ''Sta.WbMsg.Proc''), (IVar (Ident '' Other''))))"

definition n_NI_Local_Get_Get_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Get_abs  src dst\<equiv>
IVar (Ident ''Sta.Dir.Pending '') =\<^sub>f  (Const false) \<and>\<^sub>f
IVar (Ident '' Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false)

   \<triangleright>
(assign ((Ident ''Sta.Collecting''), (Const false)))"

definition n_NI_Local_Get_Put_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Put_abs  src dst\<equiv>
IVar (Ident ''Sta.Dir.Pending '') =\<^sub>f  (Const false) \<and>\<^sub>f
IVar (Ident ''
  (Sta.Dir.Dirty -> Sta.Dir.Local '') =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_E)) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.MemData''), (Const Sta.HomeProc.CacheData)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_S)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const true)))||
forallStm(\<lambda>j. (assign (Para (''Sta.Dir.InvSet'') p, (IVar (Para (''Sta.Dir.ShrSet'') p)))))M||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other''))))"

definition n_NI_Remote_Get_Nak_dst_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak_dst_Home_abs  src dst \<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
IVar (Ident ''
    Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.PendReqSrc''))  =\<^sub>f (Const (index src))  \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_Get) 

   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Nak)))||
(assign ((Ident ''Sta.HomeUniMsg.Proc''), (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

definition n_NI_Remote_Get_Put_src_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put_src_abs  dst src \<equiv>
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
IVar (Ident ''
  Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_Get) 

   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_S)))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_ShWb)))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.ShWbMsg.Data''), (IVar (Para (''Sta.Proc.CacheData'') dst))))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (IVar (Ident '' Other''))))"

definition n_NI_Remote_Get_Put_dst_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put_dst_abs  src dst \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
IVar (Ident ''
    Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall p : NODE do Sta.Proc.CacheState'') p)) =\<^sub>f  (Const CACHE_E end) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =\<^sub>f  (Const UNI_Put)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall q : NODE do Sta.UniMsg.Cmd'') q)) =\<^sub>f  (Const UNI_PutX end) ) M \<and>\<^sub>f
IVar (Ident ''    Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.PendReqSrc''))  =\<^sub>f (Const (index src))  \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_Get) 

   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Put)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident '' Other''))))||
(assign (Para (''Sta.UniMsg.Data'') src, (IVar (Ident ''StaCurrDataStaFwdCmd := UNI_None''))))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

definition n_NI_Remote_Get_Put_dst_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put_dst_Home_abs  src dst \<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
IVar (Ident ''
    Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall p : NODE do Sta.Proc.CacheState'') p)) =\<^sub>f  (Const CACHE_E end) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =\<^sub>f  (Const UNI_Put)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall q : NODE do Sta.UniMsg.Cmd'') q)) =\<^sub>f  (Const UNI_PutX end) ) M \<and>\<^sub>f
IVar (Ident ''    Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.PendReqSrc''))  =\<^sub>f (Const (index src))  \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_Get) 

   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Put)))||
(assign ((Ident ''Sta.HomeUniMsg.Proc''), (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.HomeUniMsg.Data''), (Const Sta.CurrDataSta.FwdCmd := UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

definition n_NI_Remote_Get_Put_src_dst_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put_src_dst_abs  src dst\<equiv>
IVar (Ident ''
  Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall p : NODE do Sta.Proc.CacheState'') p)) =\<^sub>f  (Const CACHE_E end) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =\<^sub>f  (Const UNI_Put)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall q : NODE do Sta.UniMsg.Cmd'') q)) =\<^sub>f  (Const UNI_PutX end) ) M \<and>\<^sub>f
IVar (Ident ''    Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_Get) 

   \<triangleright>
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_ShWb)))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.ShWbMsg.Data''), (Const Sta.CurrDataSta.FwdCmd := UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (IVar (Ident '' Other''))))"

definition n_NI_Local_GetX_GetX_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_GetX_abs  src dst\<equiv>
IVar (Ident ''Sta.Dir.Pending '') =\<^sub>f  (Const false) \<and>\<^sub>f
IVar (Ident '' Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false)

   \<triangleright>
(assign ((Ident ''Sta.Collecting''), (Const false)))"

definition n_NI_Local_GetX_PutX_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_abs  src dst\<equiv>
IVar (Ident ''Sta.Dir.Pending '') =\<^sub>f  (Const false) \<and>\<^sub>f
IVar (Ident ''
  (Sta.Dir.Dirty -> Sta.Dir.Local '') =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_E)) 

   \<triangleright>
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(\<lambda>j. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(\<lambda>j. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''if (Sta.HomeProc.ProcCmd''), (Const NODE_Get) then)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(\<lambda>j. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''if (Sta.HomeProc.ProcCmd''), (Const NODE_Get) then)))||
(assign ((Ident ''Sta.Collecting''), (Const true)))||
(assign ((Ident ''Sta.PrevData''), (Const Sta.CurrData)))||
(assign ((Ident ''if (Sta.Dir.HeadPtr !''), (IVar (Ident '' Other'')) then)))"

definition n_NI_Remote_GetX_Nak_src_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_src_abs  dst src \<equiv>
\<not>\<^sub>f (IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
IVar (Ident ''
  Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_GetX) 

   \<triangleright>
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (IVar (Ident '' Other''))))"

definition n_NI_Remote_GetX_Nak_src_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_src_Home_abs  dst src \<equiv>
\<not>\<^sub>f (IVar (Ident ''Sta.HomeProc.CacheState'')) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
IVar (Ident ''
  Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_GetX) 

   \<triangleright>
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (IVar (Ident '' Other''))))"

definition n_NI_Remote_GetX_Nak_dst_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_dst_abs  src dst \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
IVar (Ident ''
   Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.PendReqSrc''))  =\<^sub>f (Const (index src))  \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_GetX) 

   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

definition n_NI_Remote_GetX_Nak_dst_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_dst_Home_abs  src dst \<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
IVar (Ident ''
   Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.PendReqSrc''))  =\<^sub>f (Const (index src))  \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_GetX) 

   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Nak)))||
(assign ((Ident ''Sta.HomeUniMsg.Proc''), (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

definition n_NI_Remote_GetX_Nak_src_dst_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_src_dst_abs  src dst\<equiv>
IVar (Ident ''
  Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_GetX) 

   \<triangleright>
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (IVar (Ident '' Other''))))"

definition n_NI_Remote_GetX_PutX_src_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX_src_abs  dst src \<equiv>
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
IVar (Ident ''
  Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_GetX) 

   \<triangleright>
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_FAck)))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (IVar (Ident '' Other''))))"

definition n_NI_Remote_GetX_PutX_dst_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX_dst_abs  src dst \<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
IVar (Ident ''
    Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall p : NODE do Sta.Proc.CacheState'') p)) =\<^sub>f  (Const CACHE_E end) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =\<^sub>f  (Const UNI_Put)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall q : NODE do Sta.UniMsg.Cmd'') q)) =\<^sub>f  (Const UNI_PutX end) ) M \<and>\<^sub>f
IVar (Ident ''    Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.PendReqSrc''))  =\<^sub>f (Const (index src))  \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_GetX) 

   \<triangleright>
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident '' Other''))))||
(assign (Para (''Sta.UniMsg.Data'') src, (IVar (Ident ''StaCurrDataStaFwdCmd := UNI_None''))))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

definition n_NI_Remote_GetX_PutX_dst_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX_dst_Home_abs  src dst \<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
IVar (Ident ''
    Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall p : NODE do Sta.Proc.CacheState'') p)) =\<^sub>f  (Const CACHE_E end) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =\<^sub>f  (Const UNI_Put)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall q : NODE do Sta.UniMsg.Cmd'') q)) =\<^sub>f  (Const UNI_PutX end) ) M \<and>\<^sub>f
IVar (Ident ''    Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.PendReqSrc''))  =\<^sub>f (Const (index src))  \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_GetX) 

   \<triangleright>
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeUniMsg.Proc''), (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.HomeUniMsg.Data''), (Const Sta.CurrDataSta.FwdCmd := UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (Const (index src))))"

definition n_NI_Remote_GetX_PutX_src_dst_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX_src_dst_abs  src dst\<equiv>
IVar (Ident ''
  Sta.Dir.Dirty '') =\<^sub>f  (Const true) \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.WbMsg.Cmd'')) =\<^sub>f  (Const WB_Wb)  \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =\<^sub>f  (Const SHWB_ShWb)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall p : NODE do Sta.Proc.CacheState'') p)) =\<^sub>f  (Const CACHE_E end) ) M \<and>\<^sub>f
\<not>\<^sub>f (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =\<^sub>f  (Const UNI_Put)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<not>\<^sub>f (IVar (Para (''forall q : NODE do Sta.UniMsg.Cmd'') q)) =\<^sub>f  (Const UNI_PutX end) ) M \<and>\<^sub>f
IVar (Ident ''    Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident ''Sta.Dir.Local '') =\<^sub>f  (Const false) \<and>\<^sub>f
(IVar (Ident ''Sta.FwdCmd''))  =\<^sub>f (Const UNI_GetX) 

   \<triangleright>
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_FAck)))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (IVar (Ident '' Other''))))||
(assign ((Ident ''Sta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.FwdSrc''), (IVar (Ident '' Other''))))"

definition n_NI_InvAck_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_InvAck_abs  src dst\<equiv>
IVar (Ident ''
  Sta.Dir.Pending '') =\<^sub>f  (Const true) \<and>\<^sub>f
IVar (Ident '' Sta.Collecting '') =\<^sub>f  (Const true) \<and>\<^sub>f
(IVar (Ident ''Sta.NakcMsg.Cmd''))  =\<^sub>f (Const NAKC_None)  \<and>\<^sub>f
(IVar (Ident ''Sta.ShWbMsg.Cmd''))  =\<^sub>f (Const SHWB_None)  \<and>\<^sub>f
(\<forall>\<^sub>fj. (IVar (Para (''( Sta.UniMsg.Cmd'') q)) =\<^sub>f  (IVar (Para (''UNI_Get | Sta.UniMsg.Cmd = UNI_GetX ->'') q)) ) M \<and>\<^sub>f
(IVar (Para (''( Sta.UniMsg.Cmd'') q)) =\<^sub>f  (Const UNI_PutX ->)  \<and>\<^sub>f
(IVar (Ident ''Sta.PendReqSrc''))  =\<^sub>f (Const q )) 

   \<triangleright>
forallStm(\<lambda>j. TODOTODOTODOTODOTODOTODO




)M||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Collecting''), (Const false)))||
(assign ((Ident ''Sta.LastInvAck''), (IVar (Ident '' Other''))))"

definition n_NI_ShWb_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_ShWb_abs  src dst\<equiv>
(IVar (Ident ''Sta.ShWbMsg.Cmd''))  =\<^sub>f (Const SHWB_ShWb) 
   \<triangleright>
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_None)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const true)))||
forallStm(\<lambda>j. (assign (Para (''Sta.Dir.ShrSet'') p, (IVar (Para (''Sta.Dir.ShrSet'') p)))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (IVar (Para (''Sta.Dir.ShrSet'') p))))||
(assign ((Ident ''Sta.MemData''), (Const Sta.ShWbMsg.Data)))"


end

definition F::"((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula)) set" where  
"F \<equiv> {}"

definition rules2' :: "nat \<Rightarrow> rule set" where [simp]:
  "rules2' N \<equiv> (n_Stores N) \<union>
(n_Store_Homes N) \<union>
(n_PI_Remote_Gets N) \<union>
(n_PI_Remote_Get_Homes N) \<union>
(n_PI_Remote_GetXs N) \<union>
(n_PI_Remote_GetX_Homes N) \<union>
(n_PI_Remote_PutXs N) \<union>
(n_PI_Remote_Replaces N) \<union>
(n_NI_Naks N) \<union>
(n_NI_Nak_Homes N) \<union>
(n_NI_Local_Get_Naks N) \<union>
(n_NI_Local_Get_Gets N) \<union>
(n_NI_Local_Get_Puts N) \<union>
(n_NI_Remote_Get_Naks N) \<union>
(n_NI_Remote_Get_Nak_Homes N) \<union>
(n_NI_Remote_Get_Puts N) \<union>
(n_NI_Remote_Get_Put_Homes N) \<union>
(n_NI_Local_GetX_Naks N) \<union>
(n_NI_Local_GetX_GetXs N) \<union>
(n_NI_Local_GetX_PutXs N) \<union>
(n_NI_Remote_GetX_Naks N) \<union>
(n_NI_Remote_GetX_Nak_Homes N) \<union>
(n_NI_Remote_GetX_PutXs N) \<union>
(n_NI_Remote_GetX_PutX_Homes N) \<union>
(n_NI_Remote_Puts N) \<union>
(n_NI_Remote_PutXs N) \<union>
(n_NI_Invs N) \<union>
(n_NI_InvAcks N) \<union>
(n_NI_Replaces N) \<union>
(n_NI_Replace_Homes N)"

definition absRules' :: " nat\<Rightarrow>rule set" where [simp]:
  "absRules' M \<equiv>  (n_Stores M)  \<union>
 (n_Store_Homes M)  \<union>
 (n_PI_Remote_Gets M)  \<union>
 (n_PI_Remote_Get_Homes M)  \<union>
 (n_PI_Remote_GetXs M)  \<union>
 (n_PI_Remote_GetX_Homes M)  \<union>
 (n_PI_Remote_PutXs M)  \<union>
 (n_PI_Remote_Replaces M)  \<union>
 (n_NI_Naks M)  \<union>
 (n_NI_Nak_Homes M)  \<union>
 (n_NI_Local_Get_Naks M)  \<union>
 (n_NI_Local_Get_Gets M)  \<union>
 (n_NI_Local_Get_Puts M)  \<union>
 (n_NI_Remote_Get_Naks M)  \<union>
 (n_NI_Remote_Get_Nak_Homes M)  \<union>
 (n_NI_Remote_Get_Puts M)  \<union>
 (n_NI_Remote_Get_Put_Homes M)  \<union>
 (n_NI_Local_GetX_Naks M)  \<union>
 (n_NI_Local_GetX_GetXs M)  \<union>
 (n_NI_Local_GetX_PutXs M)  \<union>
 (n_NI_Remote_GetX_Naks M)  \<union>
 (n_NI_Remote_GetX_Nak_Homes M)  \<union>
 (n_NI_Remote_GetX_PutXs M)  \<union>
 (n_NI_Remote_GetX_PutX_Homes M)  \<union>
 (n_NI_Remote_Puts M)  \<union>
 (n_NI_Remote_PutXs M)  \<union>
 (n_NI_Invs M)  \<union>
 (n_NI_InvAcks M)  \<union>
 (n_NI_Replaces M)  \<union>
 (n_NI_Replace_Homes M)  \<union>
 (n_Stores M)  \<union>
 (n_PI_Remote_PutXs M)  \<union>
 (n_NI_Local_Get_Gets M)  \<union>
 (n_NI_Local_Get_Puts M)  \<union>
 (n_NI_Remote_Get_Nak_srcs M)  \<union>
 (n_NI_Remote_Get_Nak_dsts M)  \<union>
 (n_NI_Remote_Get_Nak_dst_Homes M)  \<union>
 (n_NI_Remote_Get_Nak_src_dsts M)  \<union>
 (n_NI_Remote_Get_Put_srcs M)  \<union>
 (n_NI_Remote_Get_Put_dsts M)  \<union>
 (n_NI_Remote_Get_Put_dst_Homes M)  \<union>
 (n_NI_Remote_Get_Put_src_dsts M)  \<union>
 (n_NI_Local_GetX_GetXs M)  \<union>
 (n_NI_Local_GetX_PutXs M)  \<union>
 (n_NI_Remote_GetX_Nak_srcs M)  \<union>
 (n_NI_Remote_GetX_Nak_src_Homes M)  \<union>
 (n_NI_Remote_GetX_Nak_dsts M)  \<union>
 (n_NI_Remote_GetX_Nak_dst_Homes M)  \<union>
 (n_NI_Remote_GetX_Nak_src_dsts M)  \<union>
 (n_NI_Remote_GetX_PutX_srcs M)  \<union>
 (n_NI_Remote_GetX_PutX_dsts M)  \<union>
 (n_NI_Remote_GetX_PutX_dst_Homes M)  \<union>
 (n_NI_Remote_GetX_PutX_src_dsts M)  \<union>
 (n_NI_InvAcks M)  \<union>
 (n_NI_ShWbs M)  \<union>
    {chaos \<triangleright> skip}"

text\<open>abstract rules\<close> 

lemma absStores:
  "M < N \<Longrightarrow> absTransfRule M ` (n_Stores N) = (n_Stores M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_Stores_def apply (rule absGen) 
  using symStore(3) apply blast
  by simp 

lemma absStore_Homes:
  "M < N \<Longrightarrow> absTransfRule M ` (n_Store_Homes N) = (n_Store_Homes M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_Store_Homes_def apply (rule absGen) 
  using symStore_Home(3) apply blast
  by simp 

lemma absPI_Remote_Gets:
  "M < N \<Longrightarrow> absTransfRule M ` (n_PI_Remote_Gets N) = (n_PI_Remote_Gets M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_PI_Remote_Gets_def apply (rule absGen) 
  using symPI_Remote_Get(3) apply blast
  by simp 

lemma absPI_Remote_Get_Homes:
  "M < N \<Longrightarrow> absTransfRule M ` (n_PI_Remote_Get_Homes N) = (n_PI_Remote_Get_Homes M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_PI_Remote_Get_Homes_def apply (rule absGen) 
  using symPI_Remote_Get_Home(3) apply blast
  by simp 

lemma absPI_Remote_GetXs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_PI_Remote_GetXs N) = (n_PI_Remote_GetXs M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_PI_Remote_GetXs_def apply (rule absGen) 
  using symPI_Remote_GetX(3) apply blast
  by simp 

lemma absPI_Remote_GetX_Homes:
  "M < N \<Longrightarrow> absTransfRule M ` (n_PI_Remote_GetX_Homes N) = (n_PI_Remote_GetX_Homes M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_PI_Remote_GetX_Homes_def apply (rule absGen) 
  using symPI_Remote_GetX_Home(3) apply blast
  by simp 

lemma absPI_Remote_PutXs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_PI_Remote_PutXs N) = (n_PI_Remote_PutXs M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_PI_Remote_PutXs_def apply (rule absGen) 
  using symPI_Remote_PutX(3) apply blast
  by simp 

lemma absPI_Remote_Replaces:
  "M < N \<Longrightarrow> absTransfRule M ` (n_PI_Remote_Replaces N) = (n_PI_Remote_Replaces M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_PI_Remote_Replaces_def apply (rule absGen) 
  using symPI_Remote_Replace(3) apply blast
  by simp 

lemma absNI_Naks:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Naks N) = (n_NI_Naks M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Naks_def apply (rule absGen) 
  using symNI_Nak(3) apply blast
  by simp 

lemma absNI_Nak_Homes:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Nak_Homes N) = (n_NI_Nak_Homes M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Nak_Homes_def apply (rule absGen) 
  using symNI_Nak_Home(3) apply blast
  by simp 

lemma absNI_Local_Get_Naks:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Local_Get_Naks N) = (n_NI_Local_Get_Naks M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Local_Get_Naks_def apply (rule absGen) 
  using symNI_Local_Get_Nak(3) apply blast
  by simp 

lemma absNI_Local_Get_Gets:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Local_Get_Gets N) = (n_NI_Local_Get_Gets M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Local_Get_Gets_def apply (rule absGen) 
  using symNI_Local_Get_Get(3) apply blast
  by simp 

lemma absNI_Local_Get_Puts:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Local_Get_Puts N) = (n_NI_Local_Get_Puts M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Local_Get_Puts_def apply (rule absGen) 
  using symNI_Local_Get_Put(3) apply blast
  by simp 

lemma absNI_Remote_Get_Naks:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Remote_Get_Naks N) = (n_NI_Remote_Get_Naks M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Remote_Get_Naks_def apply (rule absGen) 
  using symNI_Remote_Get_Nak(3) apply blast
  by simp 

lemma absNI_Remote_Get_Nak_Homes:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Remote_Get_Nak_Homes N) = (n_NI_Remote_Get_Nak_Homes M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Remote_Get_Nak_Homes_def apply (rule absGen) 
  using symNI_Remote_Get_Nak_Home(3) apply blast
  by simp 

lemma absNI_Remote_Get_Puts:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Remote_Get_Puts N) = (n_NI_Remote_Get_Puts M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Remote_Get_Puts_def apply (rule absGen) 
  using symNI_Remote_Get_Put(3) apply blast
  by simp 

lemma absNI_Remote_Get_Put_Homes:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Remote_Get_Put_Homes N) = (n_NI_Remote_Get_Put_Homes M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Remote_Get_Put_Homes_def apply (rule absGen) 
  using symNI_Remote_Get_Put_Home(3) apply blast
  by simp 

lemma absNI_Local_GetX_Naks:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Local_GetX_Naks N) = (n_NI_Local_GetX_Naks M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Local_GetX_Naks_def apply (rule absGen) 
  using symNI_Local_GetX_Nak(3) apply blast
  by simp 

lemma absNI_Local_GetX_GetXs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Local_GetX_GetXs N) = (n_NI_Local_GetX_GetXs M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Local_GetX_GetXs_def apply (rule absGen) 
  using symNI_Local_GetX_GetX(3) apply blast
  by simp 

lemma absNI_Local_GetX_PutXs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Local_GetX_PutXs N) = (n_NI_Local_GetX_PutXs M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Local_GetX_PutXs_def apply (rule absGen) 
  using symNI_Local_GetX_PutX(3) apply blast
  by simp 

lemma absNI_Remote_GetX_Naks:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Remote_GetX_Naks N) = (n_NI_Remote_GetX_Naks M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Remote_GetX_Naks_def apply (rule absGen) 
  using symNI_Remote_GetX_Nak(3) apply blast
  by simp 

lemma absNI_Remote_GetX_Nak_Homes:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Remote_GetX_Nak_Homes N) = (n_NI_Remote_GetX_Nak_Homes M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Remote_GetX_Nak_Homes_def apply (rule absGen) 
  using symNI_Remote_GetX_Nak_Home(3) apply blast
  by simp 

lemma absNI_Remote_GetX_PutXs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Remote_GetX_PutXs N) = (n_NI_Remote_GetX_PutXs M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Remote_GetX_PutXs_def apply (rule absGen) 
  using symNI_Remote_GetX_PutX(3) apply blast
  by simp 

lemma absNI_Remote_GetX_PutX_Homes:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Remote_GetX_PutX_Homes N) = (n_NI_Remote_GetX_PutX_Homes M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Remote_GetX_PutX_Homes_def apply (rule absGen) 
  using symNI_Remote_GetX_PutX_Home(3) apply blast
  by simp 

lemma absNI_Remote_Puts:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Remote_Puts N) = (n_NI_Remote_Puts M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Remote_Puts_def apply (rule absGen) 
  using symNI_Remote_Put(3) apply blast
  by simp 

lemma absNI_Remote_PutXs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Remote_PutXs N) = (n_NI_Remote_PutXs M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Remote_PutXs_def apply (rule absGen) 
  using symNI_Remote_PutX(3) apply blast
  by simp 

lemma absNI_Invs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Invs N) = (n_NI_Invs M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Invs_def apply (rule absGen) 
  using symNI_Inv(3) apply blast
  by simp 

lemma absNI_InvAcks:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_InvAcks N) = (n_NI_InvAcks M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_InvAcks_def apply (rule absGen) 
  using symNI_InvAck(3) apply blast
  by simp 

lemma absNI_Replaces:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Replaces N) = (n_NI_Replaces M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Replaces_def apply (rule absGen) 
  using symNI_Replace(3) apply blast
  by simp 

lemma absNI_Replace_Homes:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Replace_Homes N) = (n_NI_Replace_Homes M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Replace_Homes_def apply (rule absGen) 
  using symNI_Replace_Home(3) apply blast
  by simp 

definition absRules' :: " nat\<Rightarrow>rule set" where [simp]:
  "absRules' M \<equiv>  (n_Stores M)  \<union>
 (n_Store_Homes M)  \<union>
 (n_PI_Remote_Gets M)  \<union>
 (n_PI_Remote_Get_Homes M)  \<union>
 (n_PI_Remote_GetXs M)  \<union>
 (n_PI_Remote_GetX_Homes M)  \<union>
 (n_PI_Remote_PutXs M)  \<union>
 (n_PI_Remote_Replaces M)  \<union>
 (n_NI_Naks M)  \<union>
 (n_NI_Nak_Homes M)  \<union>
 (n_NI_Local_Get_Naks M)  \<union>
 (n_NI_Local_Get_Gets M)  \<union>
 (n_NI_Local_Get_Puts M)  \<union>
 (n_NI_Remote_Get_Naks M)  \<union>
 (n_NI_Remote_Get_Nak_Homes M)  \<union>
 (n_NI_Remote_Get_Puts M)  \<union>
 (n_NI_Remote_Get_Put_Homes M)  \<union>
 (n_NI_Local_GetX_Naks M)  \<union>
 (n_NI_Local_GetX_GetXs M)  \<union>
 (n_NI_Local_GetX_PutXs M)  \<union>
 (n_NI_Remote_GetX_Naks M)  \<union>
 (n_NI_Remote_GetX_Nak_Homes M)  \<union>
 (n_NI_Remote_GetX_PutXs M)  \<union>
 (n_NI_Remote_GetX_PutX_Homes M)  \<union>
 (n_NI_Remote_Puts M)  \<union>
 (n_NI_Remote_PutXs M)  \<union>
 (n_NI_Invs M)  \<union>
 (n_NI_InvAcks M)  \<union>
 (n_NI_Replaces M)  \<union>
 (n_NI_Replace_Homes M)  \<union>
 (n_Stores M)  \<union>
 (n_PI_Remote_PutXs M)  \<union>
 (n_NI_Local_Get_Gets M)  \<union>
 (n_NI_Local_Get_Puts M)  \<union>
 (n_NI_Remote_Get_Nak_srcs M)  \<union>
 (n_NI_Remote_Get_Nak_dsts M)  \<union>
 (n_NI_Remote_Get_Nak_dst_Homes M)  \<union>
 (n_NI_Remote_Get_Nak_src_dsts M)  \<union>
 (n_NI_Remote_Get_Put_srcs M)  \<union>
 (n_NI_Remote_Get_Put_dsts M)  \<union>
 (n_NI_Remote_Get_Put_dst_Homes M)  \<union>
 (n_NI_Remote_Get_Put_src_dsts M)  \<union>
 (n_NI_Local_GetX_GetXs M)  \<union>
 (n_NI_Local_GetX_PutXs M)  \<union>
 (n_NI_Remote_GetX_Nak_srcs M)  \<union>
 (n_NI_Remote_GetX_Nak_src_Homes M)  \<union>
 (n_NI_Remote_GetX_Nak_dsts M)  \<union>
 (n_NI_Remote_GetX_Nak_dst_Homes M)  \<union>
 (n_NI_Remote_GetX_Nak_src_dsts M)  \<union>
 (n_NI_Remote_GetX_PutX_srcs M)  \<union>
 (n_NI_Remote_GetX_PutX_dsts M)  \<union>
 (n_NI_Remote_GetX_PutX_dst_Homes M)  \<union>
 (n_NI_Remote_GetX_PutX_src_dsts M)  \<union>
 (n_NI_InvAcks M)  \<union>
 (n_NI_ShWbs M)  \<union>
    {chaos \<triangleright> skip}"

lemma absAll:
  "M < N \<Longrightarrow> absTransfRule M ` rules2' N = absRules M"
  unfolding rules2'_def absRules_def absRules_def image_Un 
    absStores
    absStore_Homes
    absPI_Remote_Gets
    absPI_Remote_Get_Homes
    absPI_Remote_GetXs
    absPI_Remote_GetX_Homes
    absPI_Remote_PutXs
    absPI_Remote_Replaces
    absNI_Naks
    absNI_Nak_Homes
    absNI_Local_Get_Naks
    absNI_Local_Get_Gets
    absNI_Local_Get_Puts
    absNI_Remote_Get_Naks
    absNI_Remote_Get_Nak_Homes
    absNI_Remote_Get_Puts
    absNI_Remote_Get_Put_Homes
    absNI_Local_GetX_Naks
    absNI_Local_GetX_GetXs
    absNI_Local_GetX_PutXs
    absNI_Remote_GetX_Naks
    absNI_Remote_GetX_Nak_Homes
    absNI_Remote_GetX_PutXs
    absNI_Remote_GetX_PutX_Homes
    absNI_Remote_Puts
    absNI_Remote_PutXs
    absNI_Invs
    absNI_InvAcks
    absNI_Replaces
    absNI_Replace_Homes
by auto

text \<open>type value information on variables occurring in aux(0,1)\<close> 
