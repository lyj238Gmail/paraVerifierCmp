theory ABS_flashWithoutABS_1
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

  apply ( intro symPreds0 symPreds1 symPreds2 symPreds3 symPreds4 symPreds5 symPreds6
 symPreds7 symPreds8 symPreds9 symPreds10 symPreds11 symPreds12 symPreds13 symPreds14 
symPreds15 symPreds16 symPreds17 symPreds18 symPreds19 symPreds20 
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
"n_Store  i\<equiv>
(IVar (Para (''Sta.Proc.CacheState'') src)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.Proc.CacheData'') src, (IVar(Ident ''data''))))||
(assign ((Ident ''NxtSta.CurrData''), (IVar(Ident ''data''))))||
(assign ((Ident ''NxtSta.LastWrVld''), (Const true)))||
(assign ((Ident ''NxtSta.LastWrPtr''), (Const (index src))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

(*lemma symStore:
  "symParamRule N n_Store"
  "wellFormedStatement N (act (n_Store i))"
  "absTransfRule M (n_Store i) = (if i \<le> M then n_Store i else chaos
\<triangleright> skip)"
  unfolding n_Store_def symParamRule_def by auto

definition n_Store_Home::"nat \<Rightarrow> rule" where 
"n_Store_Home  i\<equiv>
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_E) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign ((Ident ''NxtSta.HomeProc.CacheData''), (IVar(Ident ''data''))))||
(assign ((Ident ''NxtSta.CurrData''), (IVar(Ident ''data''))))||
(assign ((Ident ''NxtSta.LastWrVld''), (Const true)))||
(assign ((Ident ''NxtSta.LastWrPtr''), (Const (index src))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symStore_Home:
  "symParamRule N n_Store_Home"
  "wellFormedStatement N (act (n_Store_Home i))"
  "absTransfRule M (n_Store_Home i) = (if i \<le> M then n_Store_Home i else chaos
\<triangleright> skip)"
  unfolding n_Store_Home_def symParamRule_def by auto
*)
definition n_PI_Remote_Get::"nat \<Rightarrow> rule" where 
"n_PI_Remote_Get  src\<equiv>
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
"n_PI_Remote_Get_Home  i\<equiv>
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_None)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_I) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign ((Ident ''NxtSta.HomeProc.ProcCmd''), (Const NODE_Get)))||
(assign ((Ident ''NxtSta.HomeUniMsg.Cmd''), (Const UNI_Get)))||
(assign ((Ident ''NxtSta.HomeUniMsg.HomeProc''), (Const true)))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symPI_Remote_Get_Home:
  "symParamRule N n_PI_Remote_Get_Home"
  "wellFormedStatement N (act (n_PI_Remote_Get_Home i))"
  "absTransfRule M (n_PI_Remote_Get_Home i) = (if i \<le> M then n_PI_Remote_Get_Home i else chaos
\<triangleright> skip)"
  unfolding n_PI_Remote_Get_Home_def symParamRule_def by auto

definition n_PI_Remote_GetX::"nat \<Rightarrow> rule" where 
"n_PI_Remote_GetX  i\<equiv>
(IVar (Para (''Sta.Proc.ProcCmd'') src)) =\<^sub>f  (Const NODE_None)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') src)) =\<^sub>f  (Const CACHE_I) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.Proc.ProcCmd'') src, (Const NODE_GetX)))||
(assign (Para (''NxtSta.UniMsg.Cmd'') src, (Const UNI_GetX)))||
(assign (Para (''NxtSta.UniMsg.HomeProc'') src, (Const true)))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symPI_Remote_GetX:
  "symParamRule N n_PI_Remote_GetX"
  "wellFormedStatement N (act (n_PI_Remote_GetX i))"
  "absTransfRule M (n_PI_Remote_GetX i) = (if i \<le> M then n_PI_Remote_GetX i else chaos
\<triangleright> skip)"
  unfolding n_PI_Remote_GetX_def symParamRule_def by auto

definition n_PI_Remote_GetX_Home::"nat \<Rightarrow> rule" where 
"n_PI_Remote_GetX_Home  i\<equiv>
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_None)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_I) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign ((Ident ''NxtSta.HomeProc.ProcCmd''), (Const NODE_GetX)))||
(assign ((Ident ''NxtSta.HomeUniMsg.Cmd''), (Const UNI_GetX)))||
(assign ((Ident ''NxtSta.HomeUniMsg.HomeProc''), (Const true)))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symPI_Remote_GetX_Home:
  "symParamRule N n_PI_Remote_GetX_Home"
  "wellFormedStatement N (act (n_PI_Remote_GetX_Home i))"
  "absTransfRule M (n_PI_Remote_GetX_Home i) = (if i \<le> M then n_PI_Remote_GetX_Home i else chaos
\<triangleright> skip)"
  unfolding n_PI_Remote_GetX_Home_def symParamRule_def by auto

definition n_PI_Remote_PutX::"nat \<Rightarrow> rule" where 
"n_PI_Remote_PutX  i\<equiv>
(IVar (Para (''Sta.Proc.ProcCmd'') dst)) =\<^sub>f  (Const NODE_None)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign ((Ident ''NxtSta.WbMsg.Cmd''), (Const WB_Wb)))||
(assign ((Ident ''NxtSta.WbMsg.Proc''), (Const (index dst))))||
(assign ((Ident ''NxtSta.WbMsg.Data''), (IVar (Para (''Sta.Proc.CacheData'') dst))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symPI_Remote_PutX:
  "symParamRule N n_PI_Remote_PutX"
  "wellFormedStatement N (act (n_PI_Remote_PutX i))"
  "absTransfRule M (n_PI_Remote_PutX i) = (if i \<le> M then n_PI_Remote_PutX i else chaos
\<triangleright> skip)"
  unfolding n_PI_Remote_PutX_def symParamRule_def by auto

definition n_PI_Remote_Replace::"nat \<Rightarrow> rule" where 
"n_PI_Remote_Replace  i\<equiv>
(IVar (Para (''Sta.Proc.ProcCmd'') src)) =\<^sub>f  (Const NODE_None)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') src)) =\<^sub>f  (Const CACHE_S) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.Proc.CacheState'') src, (Const CACHE_I)))||
(assign (Para (''NxtSta.RpMsg.Cmd'') src, (Const RP_Replace)))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symPI_Remote_Replace:
  "symParamRule N n_PI_Remote_Replace"
  "wellFormedStatement N (act (n_PI_Remote_Replace i))"
  "absTransfRule M (n_PI_Remote_Replace i) = (if i \<le> M then n_PI_Remote_Replace i else chaos
\<triangleright> skip)"
  unfolding n_PI_Remote_Replace_def symParamRule_def by auto

definition n_NI_Nak::"nat \<Rightarrow> rule" where 
"n_NI_Nak  i\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =\<^sub>f  (Const UNI_Nak) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''NxtSta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''NxtSta.Proc.InvMarked'') dst, (Const false)))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Nak:
  "symParamRule N n_NI_Nak"
  "wellFormedStatement N (act (n_NI_Nak i))"
  "absTransfRule M (n_NI_Nak i) = (if i \<le> M then n_NI_Nak i else chaos
\<triangleright> skip)"
  unfolding n_NI_Nak_def symParamRule_def by auto

definition n_NI_Nak_Home::"nat \<Rightarrow> rule" where 
"n_NI_Nak_Home  i\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Nak) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign ((Ident ''NxtSta.HomeUniMsg.Cmd''), (Const UNI_None)))||
(assign ((Ident ''NxtSta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''NxtSta.HomeProc.InvMarked''), (Const false)))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Nak_Home:
  "symParamRule N n_NI_Nak_Home"
  "wellFormedStatement N (act (n_NI_Nak_Home i))"
  "absTransfRule M (n_NI_Nak_Home i) = (if i \<le> M then n_NI_Nak_Home i else chaos
\<triangleright> skip)"
  unfolding n_NI_Nak_Home_def symParamRule_def by auto

definition n_NI_Local_Get_Get::"nat \<Rightarrow> rule" where 
"n_NI_Local_Get_Get  i\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= RP_Replace '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''Sta.Dir.Pending '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident '' Sta.Dir.Dirty '') =\<^sub>f true \<and>\<^sub>f
\<^sub>f IVar (Ident ''Sta.Dir.Local '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= src'') =\<^sub>f false
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.UniMsg.Cmd'') src, (Const UNI_Get)))||
(assign (Para (''NxtSta.UniMsg.Proc'') src, (Const Sta.Dir.HeadPtr)))||
(assign ((Ident ''NxtSta.Collecting''), (Const false)))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Local_Get_Get:
  "symParamRule N n_NI_Local_Get_Get"
  "wellFormedStatement N (act (n_NI_Local_Get_Get i))"
  "absTransfRule M (n_NI_Local_Get_Get i) = (if i \<le> M then n_NI_Local_Get_Get i else chaos
\<triangleright> skip)"
  unfolding n_NI_Local_Get_Get_def symParamRule_def by auto

definition n_NI_Remote_Get_Nak::"nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Nak  i\<equiv>
\<^sub>f IVar (Ident ''= dst '') =\<^sub>f false \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''NxtSta.UniMsg.Proc'') src, (Const (index dst))))||
(assign ((Ident ''NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''NxtSta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''NxtSta.FwdSrc''), (Const (index src))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Remote_Get_Nak:
  "symParamRule N n_NI_Remote_Get_Nak"
  "wellFormedStatement N (act (n_NI_Remote_Get_Nak i))"
  "absTransfRule M (n_NI_Remote_Get_Nak i) = (if i \<le> M then n_NI_Remote_Get_Nak i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_Get_Nak_def symParamRule_def by auto

definition n_NI_Remote_Get_Nak_Home::"nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Nak_Home  i\<equiv>
\<^sub>f IVar (Ident ''= dst '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index dst))  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign ((Ident ''NxtSta.HomeUniMsg.Cmd''), (Const UNI_Nak)))||
(assign ((Ident ''NxtSta.HomeUniMsg.Proc''), (Const (index dst))))||
(assign ((Ident ''NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''NxtSta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''NxtSta.FwdSrc''), (Const (index src))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Remote_Get_Nak_Home:
  "symParamRule N n_NI_Remote_Get_Nak_Home"
  "wellFormedStatement N (act (n_NI_Remote_Get_Nak_Home i))"
  "absTransfRule M (n_NI_Remote_Get_Nak_Home i) = (if i \<le> M then n_NI_Remote_Get_Nak_Home i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_Get_Nak_Home_def symParamRule_def by auto

definition n_NI_Remote_Get_Put::"nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Put  i\<equiv>
\<^sub>f IVar (Ident ''= dst '') =\<^sub>f false \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.Proc.CacheState'') dst, (Const CACHE_S)))||
(assign (Para (''NxtSta.UniMsg.Cmd'') src, (Const UNI_Put)))||
(assign (Para (''NxtSta.UniMsg.Proc'') src, (Const (index dst))))||
(assign (Para (''NxtSta.UniMsg.Data'') src, (IVar (Para (''Sta.Proc.CacheData'') dst))))||
(assign ((Ident ''NxtSta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''NxtSta.FwdSrc''), (Const (index src))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Remote_Get_Put:
  "symParamRule N n_NI_Remote_Get_Put"
  "wellFormedStatement N (act (n_NI_Remote_Get_Put i))"
  "absTransfRule M (n_NI_Remote_Get_Put i) = (if i \<le> M then n_NI_Remote_Get_Put i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_Get_Put_def symParamRule_def by auto

definition n_NI_Remote_Get_Put_Home::"nat \<Rightarrow> rule" where 
"n_NI_Remote_Get_Put_Home  i\<equiv>
\<^sub>f IVar (Ident ''= dst '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index dst))  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.Proc.CacheState'') dst, (Const CACHE_S)))||
(assign ((Ident ''NxtSta.HomeUniMsg.Cmd''), (Const UNI_Put)))||
(assign ((Ident ''NxtSta.HomeUniMsg.Proc''), (Const (index dst))))||
(assign ((Ident ''NxtSta.HomeUniMsg.Data''), (IVar (Para (''Sta.Proc.CacheData'') dst))))||
(assign ((Ident ''NxtSta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''NxtSta.FwdSrc''), (Const (index src))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Remote_Get_Put_Home:
  "symParamRule N n_NI_Remote_Get_Put_Home"
  "wellFormedStatement N (act (n_NI_Remote_Get_Put_Home i))"
  "absTransfRule M (n_NI_Remote_Get_Put_Home i) = (if i \<le> M then n_NI_Remote_Get_Put_Home i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_Get_Put_Home_def symParamRule_def by auto

definition n_NI_Local_GetX_GetX::"nat \<Rightarrow> rule" where 
"n_NI_Local_GetX_GetX  i\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =\<^sub>f  (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''Sta.Dir.Pending '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident '' Sta.Dir.Dirty '') =\<^sub>f true \<and>\<^sub>f
\<^sub>f IVar (Ident ''Sta.Dir.Local '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= src'') =\<^sub>f false
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.UniMsg.Cmd'') src, (Const UNI_GetX)))||
(assign (Para (''NxtSta.UniMsg.Proc'') src, (Const Sta.Dir.HeadPtr)))||
(assign ((Ident ''NxtSta.Collecting''), (Const false)))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Local_GetX_GetX:
  "symParamRule N n_NI_Local_GetX_GetX"
  "wellFormedStatement N (act (n_NI_Local_GetX_GetX i))"
  "absTransfRule M (n_NI_Local_GetX_GetX i) = (if i \<le> M then n_NI_Local_GetX_GetX i else chaos
\<triangleright> skip)"
  unfolding n_NI_Local_GetX_GetX_def symParamRule_def by auto

definition n_NI_Remote_GetX_Nak::"nat \<Rightarrow> rule" where 
"n_NI_Remote_GetX_Nak  i\<equiv>
\<^sub>f IVar (Ident ''= dst '') =\<^sub>f false \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''NxtSta.UniMsg.Proc'') src, (Const (index dst))))||
(assign ((Ident ''NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''NxtSta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''NxtSta.FwdSrc''), (Const (index src))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Remote_GetX_Nak:
  "symParamRule N n_NI_Remote_GetX_Nak"
  "wellFormedStatement N (act (n_NI_Remote_GetX_Nak i))"
  "absTransfRule M (n_NI_Remote_GetX_Nak i) = (if i \<le> M then n_NI_Remote_GetX_Nak i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_GetX_Nak_def symParamRule_def by auto

definition n_NI_Remote_GetX_Nak_Home::"nat \<Rightarrow> rule" where 
"n_NI_Remote_GetX_Nak_Home  i\<equiv>
\<^sub>f IVar (Ident ''= dst '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index dst))  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign ((Ident ''NxtSta.HomeUniMsg.Cmd''), (Const UNI_Nak)))||
(assign ((Ident ''NxtSta.HomeUniMsg.Proc''), (Const (index dst))))||
(assign ((Ident ''NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc)))||
(assign ((Ident ''NxtSta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''NxtSta.FwdSrc''), (Const (index src))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Remote_GetX_Nak_Home:
  "symParamRule N n_NI_Remote_GetX_Nak_Home"
  "wellFormedStatement N (act (n_NI_Remote_GetX_Nak_Home i))"
  "absTransfRule M (n_NI_Remote_GetX_Nak_Home i) = (if i \<le> M then n_NI_Remote_GetX_Nak_Home i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_GetX_Nak_Home_def symParamRule_def by auto

definition n_NI_Remote_GetX_PutX::"nat \<Rightarrow> rule" where 
"n_NI_Remote_GetX_PutX  i\<equiv>
\<^sub>f IVar (Ident ''= dst '') =\<^sub>f false \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =\<^sub>f  (Const (index dst))  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign (Para (''NxtSta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign (Para (''NxtSta.UniMsg.Proc'') src, (Const (index dst))))||
(assign (Para (''NxtSta.UniMsg.Data'') src, (IVar (Para (''Sta.Proc.CacheData'') dst))))||
(assign ((Ident ''NxtSta.ShWbMsg.Cmd''), (Const SHWB_FAck)))||
(assign ((Ident ''NxtSta.ShWbMsg.Proc''), (Const (index src))))||
(assign ((Ident ''NxtSta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''NxtSta.FwdSrc''), (Const (index src))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Remote_GetX_PutX:
  "symParamRule N n_NI_Remote_GetX_PutX"
  "wellFormedStatement N (act (n_NI_Remote_GetX_PutX i))"
  "absTransfRule M (n_NI_Remote_GetX_PutX i) = (if i \<le> M then n_NI_Remote_GetX_PutX i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_GetX_PutX_def symParamRule_def by auto

definition n_NI_Remote_GetX_PutX_Home::"nat \<Rightarrow> rule" where 
"n_NI_Remote_GetX_PutX_Home  i\<equiv>
\<^sub>f IVar (Ident ''= dst '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index dst))  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =\<^sub>f  (Const CACHE_E) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign ((Ident ''NxtSta.HomeUniMsg.Cmd''), (Const UNI_PutX)))||
(assign ((Ident ''NxtSta.HomeUniMsg.Proc''), (Const (index dst))))||
(assign ((Ident ''NxtSta.HomeUniMsg.Data''), (IVar (Para (''Sta.Proc.CacheData'') dst))))||
(assign ((Ident ''NxtSta.FwdCmd''), (Const UNI_None)))||
(assign ((Ident ''NxtSta.FwdSrc''), (Const (index src))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Remote_GetX_PutX_Home:
  "symParamRule N n_NI_Remote_GetX_PutX_Home"
  "wellFormedStatement N (act (n_NI_Remote_GetX_PutX_Home i))"
  "absTransfRule M (n_NI_Remote_GetX_PutX_Home i) = (if i \<le> M then n_NI_Remote_GetX_PutX_Home i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_GetX_PutX_Home_def symParamRule_def by auto

definition n_NI_Remote_Put::"nat \<Rightarrow> rule" where 
"n_NI_Remote_Put  i\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =\<^sub>f  (Const UNI_Put) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''NxtSta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''NxtSta.Proc.InvMarked'') dst, (Const false)))||
(assign (Para (''NxtSta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign (Para (''NxtSta.Proc.CacheState'') dst, (Const CACHE_S)))||
(assign (Para (''NxtSta.Proc.CacheData'') dst, (IVar (Para (''Sta.UniMsg.Data'') dst))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Remote_Put:
  "symParamRule N n_NI_Remote_Put"
  "wellFormedStatement N (act (n_NI_Remote_Put i))"
  "absTransfRule M (n_NI_Remote_Put i) = (if i \<le> M then n_NI_Remote_Put i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_Put_def symParamRule_def by auto

definition n_NI_Remote_PutX::"nat \<Rightarrow> rule" where 
"n_NI_Remote_PutX  i\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =\<^sub>f  (Const UNI_PutX)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.ProcCmd'') dst)) =\<^sub>f  (Const NODE_GetX) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''NxtSta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''NxtSta.Proc.InvMarked'') dst, (Const false)))||
(assign (Para (''NxtSta.Proc.CacheState'') dst, (Const CACHE_E)))||
(assign (Para (''NxtSta.Proc.CacheData'') dst, (IVar (Para (''Sta.UniMsg.Data'') dst))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Remote_PutX:
  "symParamRule N n_NI_Remote_PutX"
  "wellFormedStatement N (act (n_NI_Remote_PutX i))"
  "absTransfRule M (n_NI_Remote_PutX i) = (if i \<le> M then n_NI_Remote_PutX i else chaos
\<triangleright> skip)"
  unfolding n_NI_Remote_PutX_def symParamRule_def by auto

definition n_NI_Inv::"nat \<Rightarrow> rule" where 
"n_NI_Inv  i\<equiv>
(IVar (Para (''Sta.InvMsg.Cmd'') dst)) =\<^sub>f  (Const INV_Inv) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.InvMsg.Cmd'') dst, (Const INV_InvAck)))||
(assign (Para (''NxtSta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign (Para (''if (Sta.Proc.ProcCmd'') dst, (Const NODE_Get) then)))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Inv:
  "symParamRule N n_NI_Inv"
  "wellFormedStatement N (act (n_NI_Inv i))"
  "absTransfRule M (n_NI_Inv i) = (if i \<le> M then n_NI_Inv i else chaos
\<triangleright> skip)"
  unfolding n_NI_Inv_def symParamRule_def by auto

definition n_NI_InvAck::"nat \<Rightarrow> nat \<Rightarrow> rule" where 
"n_NI_InvAck  i N\<equiv>
(IVar (Para (''Sta.InvMsg.Cmd'') src)) =\<^sub>f  (Const INV_InvAck)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''
  Sta.Dir.Pending '') =\<^sub>f true \<and>\<^sub>f
\<^sub>f IVar (Ident '' Sta.Dir.InvSet[src]  
'') =\<^sub>f true
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.InvMsg.Cmd'') src, (Const INV_None)))||
(assign (Para (''NxtSta.Dir.InvSet'') src, (Const false)))||
forallStm(\<lambda>j. (assign ((Ident ''if (p !''), (IVar (Para (''src & Sta.Dir.InvSet'') p)))))N||
(assign ((Ident ''NxtSta.Dir.Local''), (Const false)))||
(assign ((Ident ''NxtSta.Collecting''), (Const false)))||
(assign ((Ident ''NxtSta.LastInvAck''), (Const (index src))))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_InvAck:
  "symParamRule N n_NI_InvAck"
  "wellFormedStatement N (act (n_NI_InvAck i))"
  "absTransfRule M (n_NI_InvAck i) = (if i \<le> M then n_NI_InvAck i else chaos
\<triangleright> skip)"
  unfolding n_NI_InvAck_def symParamRule_def by auto

definition n_NI_Replace::"nat \<Rightarrow> rule" where 
"n_NI_Replace  i\<equiv>
(IVar (Para (''Sta.RpMsg.Cmd'') src)) =\<^sub>f  (Const RP_Replace) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign (Para (''NxtSta.RpMsg.Cmd'') src, (Const RP_None)))||
(assign (Para (''NxtSta.Dir.ShrSet'') src, (Const false)))||
(assign (Para (''NxtSta.Dir.InvSet'') src, (Const false)))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Replace:
  "symParamRule N n_NI_Replace"
  "wellFormedStatement N (act (n_NI_Replace i))"
  "absTransfRule M (n_NI_Replace i) = (if i \<le> M then n_NI_Replace i else chaos
\<triangleright> skip)"
  unfolding n_NI_Replace_def symParamRule_def by auto

definition n_NI_Replace::"nat \<Rightarrow> rule" where 
"n_NI_Replace  i\<equiv>
(IVar (Ident ''Sta.HomeRpMsg.Cmd''))  =\<^sub>f (Const RP_Replace) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta)))||
(assign ((Ident ''NxtSta.HomeRpMsg.Cmd''), (Const RP_None)))||
(assign ((Ident ''NxtSta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''NxtSta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta''), (Const NxtSta)))"

lemma symNI_Replace:
  "symParamRule N n_NI_Replace"
  "wellFormedStatement N (act (n_NI_Replace i))"
  "absTransfRule M (n_NI_Replace i) = (if i \<le> M then n_NI_Replace i else chaos
\<triangleright> skip)"
  unfolding n_NI_Replace_def symParamRule_def by auto

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

definition n_NI_Local_Get_Gets::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_Get_Gets N== oneParamCons N  n_NI_Local_Get_Get"

definition n_NI_Remote_Get_Naks::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Get_Naks N== oneParamCons N  n_NI_Remote_Get_Nak"

definition n_NI_Remote_Get_Nak_Homes::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Get_Nak_Homes N== oneParamCons N  n_NI_Remote_Get_Nak_Home"

definition n_NI_Remote_Get_Puts::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Get_Puts N== oneParamCons N  n_NI_Remote_Get_Put"

definition n_NI_Remote_Get_Put_Homes::" nat\<Rightarrow>rule set" where 
  "n_NI_Remote_Get_Put_Homes N== oneParamCons N  n_NI_Remote_Get_Put_Home"

definition n_NI_Local_GetX_GetXs::" nat\<Rightarrow>rule set" where 
  "n_NI_Local_GetX_GetXs N== oneParamCons N  n_NI_Local_GetX_GetX"

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

definition n_NI_Replaces::" nat\<Rightarrow>rule set" where 
  "n_NI_Replaces N== oneParamCons N  n_NI_Replace"

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
 (n_NI_Local_Get_Gets N) \<union>
 (n_NI_Remote_Get_Naks N) \<union>
 (n_NI_Remote_Get_Nak_Homes N) \<union>
 (n_NI_Remote_Get_Puts N) \<union>
 (n_NI_Remote_Get_Put_Homes N) \<union>
 (n_NI_Local_GetX_GetXs N) \<union>
 (n_NI_Remote_GetX_Naks N) \<union>
 (n_NI_Remote_GetX_Nak_Homes N) \<union>
 (n_NI_Remote_GetX_PutXs N) \<union>
 (n_NI_Remote_GetX_PutX_Homes N) \<union>
 (n_NI_Remote_Puts N) \<union>
 (n_NI_Remote_PutXs N) \<union>
 (n_NI_Invs N) \<union>
 (n_NI_InvAcks N) \<union>
 (n_NI_Replaces N) \<union>
 (n_NI_Replaces N) 
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

lemma n_NI_Local_Get_GetsIsSym:
  "symProtRules' N (n_NI_Local_Get_Gets N)"
  using symNI_Local_Get_Get(1) n_NI_Local_Get_Gets_def symParaRuleInfSymRuleSet by auto

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

lemma n_NI_Local_GetX_GetXsIsSym:
  "symProtRules' N (n_NI_Local_GetX_GetXs N)"
  using symNI_Local_GetX_GetX(1) n_NI_Local_GetX_GetXs_def symParaRuleInfSymRuleSet by auto

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

lemma n_NI_ReplacesIsSym:
  "symProtRules' N (n_NI_Replaces N)"
  using symNI_Replace(1) n_NI_Replaces_def symParaRuleInfSymRuleSet by auto

lemma rulesSym':
  shows "symProtRules' N (rules' N)"
  using n_StoresIsSym n_Store_HomesIsSym n_PI_Remote_GetsIsSym n_PI_Remote_Get_HomesIsSym n_PI_Remote_GetXsIsSym n_PI_Remote_GetX_HomesIsSym n_PI_Remote_PutXsIsSym n_PI_Remote_ReplacesIsSym n_NI_NaksIsSym n_NI_Nak_HomesIsSym n_NI_Local_Get_GetsIsSym n_NI_Remote_Get_NaksIsSym n_NI_Remote_Get_Nak_HomesIsSym n_NI_Remote_Get_PutsIsSym n_NI_Remote_Get_Put_HomesIsSym n_NI_Local_GetX_GetXsIsSym n_NI_Remote_GetX_NaksIsSym n_NI_Remote_GetX_Nak_HomesIsSym n_NI_Remote_GetX_PutXsIsSym n_NI_Remote_GetX_PutX_HomesIsSym n_NI_Remote_PutsIsSym n_NI_Remote_PutXsIsSym n_NI_InvsIsSym n_NI_InvAcksIsSym n_NI_ReplacesIsSym n_NI_ReplacesIsSym rules'_def symProtRulesUnion by presburger 



subsection{*Definitions of each abstracted rule*}

definition  NC::"nat " where [simp]: "NC==1"

definition n_Store_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_Store_abs  j M\<equiv>
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false \<and>\<^sub>f
(\<forall>\<^sub>fj. \<^sub>f IVar (Ident ''= NODE_2'') =\<^sub>f false) M

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.CurrData''), (IVar (Ident ''['DATA_1']'') )))||
(assign ((Ident ''	NxtSta.LastWrVld''), (Const true )))||
(assign ((Ident ''	NxtSta.LastWrPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_Store_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_Store_Home_abs  j M\<equiv>
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_E) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeProc.CacheData''), (IVar (Ident ''['DATA_1']'') )))||
(assign ((Ident ''	NxtSta.CurrData''), (IVar (Ident ''['DATA_1']'') )))||
(assign ((Ident ''	NxtSta.LastWrVld''), (Const true )))||
(assign ((Ident ''	NxtSta.LastWrPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_PI_Remote_Get_abs::"nat \<Rightarrow> rule" where [simp]:
"n_PI_Remote_Get_abs  j\<equiv>
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.HomeProc''), (Const true )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_PI_Remote_Get_Home_abs::"nat \<Rightarrow> rule" where [simp]:
"n_PI_Remote_Get_Home_abs  j\<equiv>
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_None)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_I) 

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeProc.ProcCmd''), (Const NODE_Get )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_Get )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.HomeProc''), (Const true )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_PI_Remote_GetX_abs::"nat \<Rightarrow> rule" where [simp]:
"n_PI_Remote_GetX_abs  j\<equiv>
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_PI_Remote_GetX_Home_abs::"nat \<Rightarrow> rule" where [simp]:
"n_PI_Remote_GetX_Home_abs  j\<equiv>
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =\<^sub>f (Const NODE_None)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =\<^sub>f (Const CACHE_I) 

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeProc.ProcCmd''), (Const NODE_GetX )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_GetX )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.HomeProc''), (Const true )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_PI_Remote_PutX_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_PI_Remote_PutX_abs  j M\<equiv>
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false \<and>\<^sub>f
(\<forall>\<^sub>fj. \<^sub>f IVar (Ident ''= NODE_2'') =\<^sub>f false) M

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.WbMsg.Cmd''), (Const WB_Wb )))||
(assign ((Ident ''	NxtSta.WbMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_PI_Remote_Replace_abs::"nat \<Rightarrow> rule" where [simp]:
"n_PI_Remote_Replace_abs  j\<equiv>
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Nak_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Nak_abs  j\<equiv>
\<^sub>f IVar (Ident ''

	True
'') =\<^sub>f true
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Nak_Home_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Nak_Home_abs  j\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Nak) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.HomeProc.ProcCmd''), (Const NODE_None )))||
(assign ((Ident ''	NxtSta.HomeProc.InvMarked''), (Const false )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Local_Get_Get_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Get_abs  j M\<equiv>
\<^sub>f IVar (Ident ''Sta.Dir.Pending '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''
	Sta.Dir.Dirty '') =\<^sub>f true \<and>\<^sub>f
\<^sub>f IVar (Ident ''Sta.Dir.Local '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= Other'') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.Dir.Pending''), (Const true )))||
(assign ((Ident ''	NxtSta.PendReqSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.PendReqCmd''), (Const UNI_Get )))||
(assign ((Ident ''	NxtSta.Collecting''), (Const false )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Get_Nak_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak_abs  j M\<equiv>
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Get_Nak_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak_abs  j M\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign (Para (''	NxtSta.UniMsg.Cmd'') j, (Const UNI_Nak )))||
(assign (Para (''	NxtSta.UniMsg.Proc'') j, (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (Const NODE_1 )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Get_Nak_abs_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak_abs_abs  j M\<equiv>
\<^sub>f IVar (Ident ''= Other'') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Get_Nak_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak_Home_abs  j M\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const NODE_2)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_Nak )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Proc''), (Const NODE_2 )))||
(assign ((Ident ''	NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Get_Nak_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak_Home_abs  j M\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_Nak )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (Const NODE_1 )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Get_Nak_Home_abs_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak_Home_abs_abs  j M\<equiv>
\<^sub>f IVar (Ident ''= Other '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_Nak )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Get_Put_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put_abs  j M\<equiv>
(IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign (Para (''	NxtSta.Proc.CacheState'') j, (Const CACHE_S )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Get_Put_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put_abs  j M\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_Get)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= UNI_PutX '') =\<^sub>f false \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign (Para (''	NxtSta.UniMsg.Cmd'') j, (Const UNI_Put )))||
(assign (Para (''	NxtSta.UniMsg.Proc'') j, (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (Const NODE_1 )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Get_Put_abs_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put_abs_abs  j M\<equiv>
\<^sub>f IVar (Ident ''= Other'') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<^sub>f IVar (Ident ''= UNI_PutX '') =\<^sub>f false) M \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Get_Put_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put_Home_abs  j M\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const NODE_2)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign (Para (''	NxtSta.Proc.CacheState'') j, (Const CACHE_S )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_Put )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Proc''), (Const NODE_2 )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Data''), (IVar (Para (''Sta.Proc.CacheData '') j))))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Get_Put_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put_Home_abs  j M\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= UNI_PutX '') =\<^sub>f false \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_Put )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (Const NODE_1 )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Get_Put_Home_abs_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put_Home_abs_abs  j M\<equiv>
\<^sub>f IVar (Ident ''= Other '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<^sub>f IVar (Ident ''= UNI_PutX '') =\<^sub>f false) M \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_Put )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Local_GetX_GetX_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_GetX_abs  j M\<equiv>
\<^sub>f IVar (Ident ''Sta.Dir.Pending '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''
	Sta.Dir.Dirty '') =\<^sub>f true \<and>\<^sub>f
\<^sub>f IVar (Ident ''Sta.Dir.Local '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= Other'') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.Dir.Pending''), (Const true )))||
(assign ((Ident ''	NxtSta.PendReqSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.PendReqCmd''), (Const UNI_GetX )))||
(assign ((Ident ''	NxtSta.Collecting''), (Const false )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_GetX_Nak_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_abs  j M\<equiv>
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_GetX_Nak_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_abs  j M\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign (Para (''	NxtSta.UniMsg.Cmd'') j, (Const UNI_Nak )))||
(assign (Para (''	NxtSta.UniMsg.Proc'') j, (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (Const NODE_1 )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_GetX_Nak_abs_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_abs_abs  j M\<equiv>
\<^sub>f IVar (Ident ''= Other'') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_GetX_Nak_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_Home_abs  j M\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const NODE_2)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_Nak )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Proc''), (Const NODE_2 )))||
(assign ((Ident ''	NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_GetX_Nak_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_Home_abs  j M\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_Nak )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (Const NODE_1 )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_GetX_Nak_Home_abs_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_Home_abs_abs  j M\<equiv>
\<^sub>f IVar (Ident ''= Other '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_Nak )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.NakcMsg.Cmd''), (Const NAKC_Nakc )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_GetX_PutX_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX_abs  j M\<equiv>
(IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign (Para (''	NxtSta.Proc.CacheState'') j, (Const CACHE_I )))||
(assign ((Ident ''	NxtSta.ShWbMsg.Cmd''), (Const SHWB_FAck )))||
(assign ((Ident ''	NxtSta.ShWbMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_GetX_PutX_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX_abs  j M\<equiv>
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =\<^sub>f  (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Para (''Sta.UniMsg.Proc'') j)) =\<^sub>f  (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= UNI_PutX '') =\<^sub>f false \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign (Para (''	NxtSta.UniMsg.Cmd'') j, (Const UNI_PutX )))||
(assign (Para (''	NxtSta.UniMsg.Proc'') j, (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.ShWbMsg.Cmd''), (Const SHWB_FAck )))||
(assign ((Ident ''	NxtSta.ShWbMsg.Proc''), (Const NODE_1 )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (Const NODE_1 )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_GetX_PutX_abs_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX_abs_abs  j M\<equiv>
\<^sub>f IVar (Ident ''= Other'') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<^sub>f IVar (Ident ''= UNI_PutX '') =\<^sub>f false) M \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.ShWbMsg.Cmd''), (Const SHWB_FAck )))||
(assign ((Ident ''	NxtSta.ShWbMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_GetX_PutX_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX_Home_abs  j M\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const NODE_2)  \<and>\<^sub>f
(IVar (Para (''Sta.Proc.CacheState'') j)) =\<^sub>f  (Const CACHE_E)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false) 

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign (Para (''	NxtSta.Proc.CacheState'') j, (Const CACHE_I )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_PutX )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Proc''), (Const NODE_2 )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Data''), (IVar (Para (''Sta.Proc.CacheData '') j))))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_GetX_PutX_Home_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX_Home_abs  j M\<equiv>
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= UNI_PutX '') =\<^sub>f false \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_PutX )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (Const NODE_1 )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_GetX_PutX_Home_abs_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX_Home_abs_abs  j M\<equiv>
\<^sub>f IVar (Ident ''= Other '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(\<forall>\<^sub>fj. \<^sub>f IVar (Ident ''= UNI_PutX '') =\<^sub>f false) M \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Cmd''), (Const UNI_PutX )))||
(assign ((Ident ''	NxtSta.HomeUniMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	NxtSta.FwdCmd''), (Const UNI_None )))||
(assign ((Ident ''	NxtSta.FwdSrc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_Put_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Put_abs  j\<equiv>
\<^sub>f IVar (Ident ''

	True
'') =\<^sub>f true
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Remote_PutX_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_PutX_abs  j M\<equiv>
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= SHWB_ShWb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''= WB_Wb '') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(\<forall>\<^sub>fj. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false) ) M \<and>\<^sub>f
\<^sub>f IVar (Ident ''= NODE_2 '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= CACHE_E '') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''= UNI_PutX'') =\<^sub>f false

   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Inv_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Inv_abs  j\<equiv>
\<^sub>f IVar (Ident ''

	True
'') =\<^sub>f true
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_InvAck_abs::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_InvAck_abs  j M\<equiv>
\<^sub>f IVar (Ident ''

	Sta.Dir.Pending
'') =\<^sub>f true
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''NxtSta.LastInvAck''), (IVar (Ident '' Other'') )))||
forallStm(\<lambda>j. TODOTODOTODOTODOTODOTODO




)M||
TODOTODOTODOTODOTODOTODO




||
TODOTODOTODOTODOTODOTODO




||
(assign ((Ident ''NxtSta.Dir.Pending''), (Const false )))||
(assign ((Ident ''NxtSta.Dir.Local''), (Const false )))||
TODOTODOTODOTODOTODOTODO




||
(assign ((Ident ''	NxtSta.Collecting''), (Const false )))||
(assign ((Ident ''	NxtSta.LastInvAck''), (IVar (Ident '' Other'') )))||
TODOTODOTODOTODOTODOTODO




||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Replace_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Replace_abs  j\<equiv>
\<^sub>f IVar (Ident ''

	True
'') =\<^sub>f true
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	Sta''), (Const NxtSta)))"

definition n_NI_Replace_abs::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Replace_abs  j\<equiv>
(IVar (Ident ''Sta.HomeRpMsg.Cmd''))  =\<^sub>f (Const RP_Replace) 
   \<triangleright>
(assign ((Ident ''NxtSta''), (Const Sta )))||
(assign ((Ident ''	NxtSta.HomeRpMsg.Cmd''), (Const RP_None )))||
(assign ((Ident ''NxtSta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''	NxtSta.Dir.HomeInvSet''), (Const false )))||
TODOTODOTODOTODOTODOTODO




||
(assign ((Ident ''	Sta''), (Const NxtSta)))"


end

definition pair1:: "((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula))" where [simp]:
 "pair1 ==(%i. (IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=SHWB_ShWb'') =\<^sub>f false,

 (\<lambda>j. \<^sub>f IVar (Ident ''=NODE_2'') =\<^sub>f false))"

definition pair2:: "((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula))" where [simp]:
 "pair2 ==(%i. (IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=SHWB_ShWb'') =\<^sub>f false,

 (\<lambda>j. \<^sub>f IVar (Ident ''=NODE_2'') =\<^sub>f false))"

definition pair3:: "((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula))" where [simp]:
 "pair3 ==(%i. \<^sub>f IVar (Ident ''=Other'') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=SHWB_ShWb'') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''=WB_Wb'') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false) ,

 (\<lambda>j. \<^sub>f IVar (Ident ''=UNI_PutX'') =\<^sub>f false \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=CACHE_E'') =\<^sub>f false))"

definition pair4:: "((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula))" where [simp]:
 "pair4 ==(%i. \<^sub>f IVar (Ident ''=Other'') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_Get)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=WB_Wb'') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false) ,

 (\<lambda>j. \<^sub>f IVar (Ident ''=UNI_PutX'') =\<^sub>f false \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=CACHE_E'') =\<^sub>f false))"

definition pair5:: "((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula))" where [simp]:
 "pair5 ==(%i. \<^sub>f IVar (Ident ''=Other'') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=SHWB_ShWb'') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''=WB_Wb'') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false) ,

 (\<lambda>j. \<^sub>f IVar (Ident ''=UNI_PutX'') =\<^sub>f false \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=CACHE_E'') =\<^sub>f false))"

definition pair6:: "((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula))" where [simp]:
 "pair6 ==(%i. \<^sub>f IVar (Ident ''=Other'') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =\<^sub>f (Const UNI_GetX)  \<and>\<^sub>f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =\<^sub>f (Const (index (M+1)))  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=WB_Wb'') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false) ,

 (\<lambda>j. \<^sub>f IVar (Ident ''=UNI_PutX'') =\<^sub>f false \<and>\<^sub>f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=CACHE_E'') =\<^sub>f false))"

definition pair7:: "((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula))" where [simp]:
 "pair7 ==(%i. (IVar (Ident ''Sta.Dir.Dirty''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=SHWB_ShWb'') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.HeadVld''))  =\<^sub>f (Const true)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=WB_Wb'') =\<^sub>f false \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.Local''))  =\<^sub>f (Const false)  \<and>\<^sub>f
(IVar (Ident ''Sta.Dir.ShrVld''))  =\<^sub>f (Const false) ,

 (\<lambda>j. (IVar (Para (''Sta.Dir.ShrSet'') j)) =\<^sub>f  (Const false)  \<and>\<^sub>f
\<^sub>f IVar (Ident ''=NODE_2'') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''=CACHE_E'') =\<^sub>f false \<and>\<^sub>f
\<^sub>f IVar (Ident ''=UNI_PutX'') =\<^sub>f false))"

definition F::"((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula)) set" where  
"F \<equiv> {pair1 pair2 pair3 pair4 pair5 pair6 pair7 }"

definition n_Store2s::" nat \<Rightarrow>rule set" where
  "n_Store2s N==
  (oneParamCons N  (%i. (strengthenRule2  (constrInvByExcl pair1 i N) (n_Store i))))"

definition n_PI_Remote_PutX2s::" nat \<Rightarrow>rule set" where
  "n_PI_Remote_PutX2s N==
  (oneParamCons N  (%i. (strengthenRule2  (constrInvByExcl pair2 i N) (n_PI_Remote_PutX i))))"

definition n_NI_Remote_Get_Put2s::" nat \<Rightarrow>rule set" where
  "n_NI_Remote_Get_Put2s N==
  (oneParamCons N  (%i. (strengthenRule2  (constrInvByExcl pair3 i N) (n_NI_Remote_Get_Put i))))"

definition n_NI_Remote_Get_Put_Home2s::" nat \<Rightarrow>rule set" where
  "n_NI_Remote_Get_Put_Home2s N==
  (oneParamCons N  (%i. (strengthenRule2  (constrInvByExcl pair4 i N) (n_NI_Remote_Get_Put_Home i))))"

definition n_NI_Remote_GetX_PutX2s::" nat \<Rightarrow>rule set" where
  "n_NI_Remote_GetX_PutX2s N==
  (oneParamCons N  (%i. (strengthenRule2  (constrInvByExcl pair5 i N) (n_NI_Remote_GetX_PutX i))))"

definition n_NI_Remote_GetX_PutX_Home2s::" nat \<Rightarrow>rule set" where
  "n_NI_Remote_GetX_PutX_Home2s N==
  (oneParamCons N  (%i. (strengthenRule2  (constrInvByExcl pair6 i N) (n_NI_Remote_GetX_PutX_Home i))))"

definition n_NI_Remote_PutX2s::" nat \<Rightarrow>rule set" where
  "n_NI_Remote_PutX2s N==
  (oneParamCons N  (%i. (strengthenRule2  (constrInvByExcl pair7 i N) (n_NI_Remote_PutX i))))"

lemma n_Store2sIsSym:
  "symProtRules' N (n_Store2s N)"
  unfolding n_Store2s_def
  apply (rule symParaRuleInfSymRuleSet)
  using invAux1_def n_Store2Eq symStore2_ref(1) constrInvByExcl_def
  by (auto simp add: pair1_def)

lemma n_PI_Remote_PutX2sIsSym:
  "symProtRules' N (n_PI_Remote_PutX2s N)"
  unfolding n_PI_Remote_PutX2s_def
  apply (rule symParaRuleInfSymRuleSet)
  using invAux1_def n_PI_Remote_PutX2Eq symPI_Remote_PutX2_ref(1) constrInvByExcl_def
  by (auto simp add: pair2_def)

lemma n_NI_Remote_Get_Put2sIsSym:
  "symProtRules' N (n_NI_Remote_Get_Put2s N)"
  unfolding n_NI_Remote_Get_Put2s_def
  apply (rule symParaRuleInfSymRuleSet)
  using invAux1_def n_NI_Remote_Get_Put2Eq symNI_Remote_Get_Put2_ref(1) constrInvByExcl_def
  by (auto simp add: pair3_def)

lemma n_NI_Remote_Get_Put_Home2sIsSym:
  "symProtRules' N (n_NI_Remote_Get_Put_Home2s N)"
  unfolding n_NI_Remote_Get_Put_Home2s_def
  apply (rule symParaRuleInfSymRuleSet)
  using invAux1_def n_NI_Remote_Get_Put_Home2Eq symNI_Remote_Get_Put_Home2_ref(1) constrInvByExcl_def
  by (auto simp add: pair4_def)

lemma n_NI_Remote_GetX_PutX2sIsSym:
  "symProtRules' N (n_NI_Remote_GetX_PutX2s N)"
  unfolding n_NI_Remote_GetX_PutX2s_def
  apply (rule symParaRuleInfSymRuleSet)
  using invAux1_def n_NI_Remote_GetX_PutX2Eq symNI_Remote_GetX_PutX2_ref(1) constrInvByExcl_def
  by (auto simp add: pair5_def)

lemma n_NI_Remote_GetX_PutX_Home2sIsSym:
  "symProtRules' N (n_NI_Remote_GetX_PutX_Home2s N)"
  unfolding n_NI_Remote_GetX_PutX_Home2s_def
  apply (rule symParaRuleInfSymRuleSet)
  using invAux1_def n_NI_Remote_GetX_PutX_Home2Eq symNI_Remote_GetX_PutX_Home2_ref(1) constrInvByExcl_def
  by (auto simp add: pair6_def)

lemma n_NI_Remote_PutX2sIsSym:
  "symProtRules' N (n_NI_Remote_PutX2s N)"
  unfolding n_NI_Remote_PutX2s_def
  apply (rule symParaRuleInfSymRuleSet)
  using invAux1_def n_NI_Remote_PutX2Eq symNI_Remote_PutX2_ref(1) constrInvByExcl_def
  by (auto simp add: pair7_def)

definition rules2' :: "nat \<Rightarrow> rule set" where [simp]:
  "rules2' N \<equiv> (n_Store2s N) \<union>
(n_Store_Homes N) \<union>
(n_PI_Remote_Gets N) \<union>
(n_PI_Remote_Get_Homes N) \<union>
(n_PI_Remote_GetXs N) \<union>
(n_PI_Remote_GetX_Homes N) \<union>
(n_PI_Remote_PutX2s N) \<union>
(n_PI_Remote_Replaces N) \<union>
(n_NI_Naks N) \<union>
(n_NI_Nak_Homes N) \<union>
(n_NI_Local_Get_Gets N) \<union>
(n_NI_Remote_Get_Naks N) \<union>
(n_NI_Remote_Get_Nak_Homes N) \<union>
(n_NI_Remote_Get_Put2s N) \<union>
(n_NI_Remote_Get_Put_Home2s N) \<union>
(n_NI_Local_GetX_GetXs N) \<union>
(n_NI_Remote_GetX_Naks N) \<union>
(n_NI_Remote_GetX_Nak_Homes N) \<union>
(n_NI_Remote_GetX_PutX2s N) \<union>
(n_NI_Remote_GetX_PutX_Home2s N) \<union>
(n_NI_Remote_Puts N) \<union>
(n_NI_Remote_PutX2s N) \<union>
(n_NI_Invs N) \<union>
(n_NI_InvAcks N) \<union>
(n_NI_Replaces N) \<union>
(n_NI_Replaces N)"

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
 (n_NI_Local_Get_Gets M)  \<union>
 (n_NI_Remote_Get_Naks M)  \<union>
 (n_NI_Remote_Get_Nak_Homes M)  \<union>
 (n_NI_Remote_Get_Puts M)  \<union>
 (n_NI_Remote_Get_Put_Homes M)  \<union>
 (n_NI_Local_GetX_GetXs M)  \<union>
 (n_NI_Remote_GetX_Naks M)  \<union>
 (n_NI_Remote_GetX_Nak_Homes M)  \<union>
 (n_NI_Remote_GetX_PutXs M)  \<union>
 (n_NI_Remote_GetX_PutX_Homes M)  \<union>
 (n_NI_Remote_Puts M)  \<union>
 (n_NI_Remote_PutXs M)  \<union>
 (n_NI_Invs M)  \<union>
 (n_NI_InvAcks M)  \<union>
 (n_NI_Replaces M)  \<union>
 (n_NI_Replaces M)  \<union>
 (n_Store_abss M)  \<union>
 (n_Store_Home_abss M)  \<union>
 (n_PI_Remote_Get_abss M)  \<union>
 (n_PI_Remote_Get_Home_abss M)  \<union>
 (n_PI_Remote_GetX_abss M)  \<union>
 (n_PI_Remote_GetX_Home_abss M)  \<union>
 (n_PI_Remote_PutX_abss M)  \<union>
 (n_PI_Remote_Replace_abss M)  \<union>
 (n_NI_Nak_abss M)  \<union>
 (n_NI_Nak_Home_abss M)  \<union>
 (n_NI_Local_Get_Get_abss M)  \<union>
 (n_NI_Remote_Get_Nak_abss M)  \<union>
 (n_NI_Remote_Get_Nak_abss M)  \<union>
 (n_NI_Remote_Get_Nak_abs_abss M)  \<union>
 (n_NI_Remote_Get_Nak_Home_abss M)  \<union>
 (n_NI_Remote_Get_Nak_Home_abss M)  \<union>
 (n_NI_Remote_Get_Nak_Home_abs_abss M)  \<union>
 (n_NI_Remote_Get_Put_abss M)  \<union>
 (n_NI_Remote_Get_Put_abss M)  \<union>
 (n_NI_Remote_Get_Put_abs_abss M)  \<union>
 (n_NI_Remote_Get_Put_Home_abss M)  \<union>
 (n_NI_Remote_Get_Put_Home_abss M)  \<union>
 (n_NI_Remote_Get_Put_Home_abs_abss M)  \<union>
 (n_NI_Local_GetX_GetX_abss M)  \<union>
 (n_NI_Remote_GetX_Nak_abss M)  \<union>
 (n_NI_Remote_GetX_Nak_abss M)  \<union>
 (n_NI_Remote_GetX_Nak_abs_abss M)  \<union>
 (n_NI_Remote_GetX_Nak_Home_abss M)  \<union>
 (n_NI_Remote_GetX_Nak_Home_abss M)  \<union>
 (n_NI_Remote_GetX_Nak_Home_abs_abss M)  \<union>
 (n_NI_Remote_GetX_PutX_abss M)  \<union>
 (n_NI_Remote_GetX_PutX_abss M)  \<union>
 (n_NI_Remote_GetX_PutX_abs_abss M)  \<union>
 (n_NI_Remote_GetX_PutX_Home_abss M)  \<union>
 (n_NI_Remote_GetX_PutX_Home_abss M)  \<union>
 (n_NI_Remote_GetX_PutX_Home_abs_abss M)  \<union>
 (n_NI_Remote_Put_abss M)  \<union>
 (n_NI_Remote_PutX_abss M)  \<union>
 (n_NI_Inv_abss M)  \<union>
 (n_NI_InvAck_abss M)  \<union>
 (n_NI_Replace_abss M)  \<union>
 (n_NI_Replace_abss M)  \<union>
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

lemma absNI_Local_Get_Gets:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Local_Get_Gets N) = (n_NI_Local_Get_Gets M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Local_Get_Gets_def apply (rule absGen) 
  using symNI_Local_Get_Get(3) apply blast
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

lemma absNI_Local_GetX_GetXs:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Local_GetX_GetXs N) = (n_NI_Local_GetX_GetXs M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Local_GetX_GetXs_def apply (rule absGen) 
  using symNI_Local_GetX_GetX(3) apply blast
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

lemma absNI_Replaces:
  "M < N \<Longrightarrow> absTransfRule M ` (n_NI_Replaces N) = (n_NI_Replaces M) 
\<union> {chaos \<triangleright> skip}"
  unfolding n_NI_Replaces_def apply (rule absGen) 
  using symNI_Replace(3) apply blast
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
 (n_NI_Local_Get_Gets M)  \<union>
 (n_NI_Remote_Get_Naks M)  \<union>
 (n_NI_Remote_Get_Nak_Homes M)  \<union>
 (n_NI_Remote_Get_Puts M)  \<union>
 (n_NI_Remote_Get_Put_Homes M)  \<union>
 (n_NI_Local_GetX_GetXs M)  \<union>
 (n_NI_Remote_GetX_Naks M)  \<union>
 (n_NI_Remote_GetX_Nak_Homes M)  \<union>
 (n_NI_Remote_GetX_PutXs M)  \<union>
 (n_NI_Remote_GetX_PutX_Homes M)  \<union>
 (n_NI_Remote_Puts M)  \<union>
 (n_NI_Remote_PutXs M)  \<union>
 (n_NI_Invs M)  \<union>
 (n_NI_InvAcks M)  \<union>
 (n_NI_Replaces M)  \<union>
 (n_NI_Replaces M)  \<union>
 (n_Store_abss M)  \<union>
 (n_Store_Home_abss M)  \<union>
 (n_PI_Remote_Get_abss M)  \<union>
 (n_PI_Remote_Get_Home_abss M)  \<union>
 (n_PI_Remote_GetX_abss M)  \<union>
 (n_PI_Remote_GetX_Home_abss M)  \<union>
 (n_PI_Remote_PutX_abss M)  \<union>
 (n_PI_Remote_Replace_abss M)  \<union>
 (n_NI_Nak_abss M)  \<union>
 (n_NI_Nak_Home_abss M)  \<union>
 (n_NI_Local_Get_Get_abss M)  \<union>
 (n_NI_Remote_Get_Nak_abss M)  \<union>
 (n_NI_Remote_Get_Nak_abss M)  \<union>
 (n_NI_Remote_Get_Nak_abs_abss M)  \<union>
 (n_NI_Remote_Get_Nak_Home_abss M)  \<union>
 (n_NI_Remote_Get_Nak_Home_abss M)  \<union>
 (n_NI_Remote_Get_Nak_Home_abs_abss M)  \<union>
 (n_NI_Remote_Get_Put_abss M)  \<union>
 (n_NI_Remote_Get_Put_abss M)  \<union>
 (n_NI_Remote_Get_Put_abs_abss M)  \<union>
 (n_NI_Remote_Get_Put_Home_abss M)  \<union>
 (n_NI_Remote_Get_Put_Home_abss M)  \<union>
 (n_NI_Remote_Get_Put_Home_abs_abss M)  \<union>
 (n_NI_Local_GetX_GetX_abss M)  \<union>
 (n_NI_Remote_GetX_Nak_abss M)  \<union>
 (n_NI_Remote_GetX_Nak_abss M)  \<union>
 (n_NI_Remote_GetX_Nak_abs_abss M)  \<union>
 (n_NI_Remote_GetX_Nak_Home_abss M)  \<union>
 (n_NI_Remote_GetX_Nak_Home_abss M)  \<union>
 (n_NI_Remote_GetX_Nak_Home_abs_abss M)  \<union>
 (n_NI_Remote_GetX_PutX_abss M)  \<union>
 (n_NI_Remote_GetX_PutX_abss M)  \<union>
 (n_NI_Remote_GetX_PutX_abs_abss M)  \<union>
 (n_NI_Remote_GetX_PutX_Home_abss M)  \<union>
 (n_NI_Remote_GetX_PutX_Home_abss M)  \<union>
 (n_NI_Remote_GetX_PutX_Home_abs_abss M)  \<union>
 (n_NI_Remote_Put_abss M)  \<union>
 (n_NI_Remote_PutX_abss M)  \<union>
 (n_NI_Inv_abss M)  \<union>
 (n_NI_InvAck_abss M)  \<union>
 (n_NI_Replace_abss M)  \<union>
 (n_NI_Replace_abss M)  \<union>
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
    absNI_Local_Get_Gets
    absNI_Remote_Get_Naks
    absNI_Remote_Get_Nak_Homes
    absNI_Remote_Get_Puts
    absNI_Remote_Get_Put_Homes
    absNI_Local_GetX_GetXs
    absNI_Remote_GetX_Naks
    absNI_Remote_GetX_Nak_Homes
    absNI_Remote_GetX_PutXs
    absNI_Remote_GetX_PutX_Homes
    absNI_Remote_Puts
    absNI_Remote_PutXs
    absNI_Invs
    absNI_InvAcks
    absNI_Replaces
    absNI_Replaces
by auto

text \<open>type value information on variables occurring in aux(0,1)\<close> 
definition type_inv_Sta.Proc_ProcCmd :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_Sta.Proc_ProcCmd N s = 
(\<forall>i. i \<le> N \<longrightarrow>
 s (Para ''Sta.Proc_ProcCmd'' i) = NODE_None \<or>  s (Para ''Sta.Proc_ProcCmd'' i) = NODE_GetX)"

lemma inv_Sta.Proc_ProcCmd' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_Sta.Proc_ProcCmd N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_Sta.Proc_ProcCmd_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
done
done

lemma inv_Sta.Proc_ProcCmd'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N 
\<longrightarrow> i \<le> N \<longrightarrow> isEnumVal s (Para ''Sta.Proc_ProcCmd'' i)"
  using inv_Sta.Proc_ProcCmd' unfolding type_inv_CurCmd_def 
NODE_None_def NODE_GetX_def 
  by (metis  assms getValueType.simps(1) isEnumVal_def typeOf_def) 

definition type_inv_Sta.Dir.ShrSet[j] :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_Sta.Dir.ShrSet[j] N s = 
(\<forall>i. i \<le> N \<longrightarrow>
 s (Para ''Sta.Dir.ShrSet[j]'' i) = false)"

lemma inv_Sta.Dir.ShrSet[j]' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_Sta.Dir.ShrSet[j] N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_Sta.Dir.ShrSet[j]_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
done
done

lemma inv_Sta.Dir.ShrSet[j]'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N 
\<longrightarrow> i \<le> N \<longrightarrow> isBoolVal s (Para ''Sta.Dir.ShrSet[j]'' i)"
  using inv_Sta.Dir.ShrSet[j]' unfolding type_inv_CurCmd_def 
false_def 
    using assms by fastforce 

definition type_inv_Sta.Proc_CacheState :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_Sta.Proc_CacheState N s = 
(\<forall>i. i \<le> N \<longrightarrow>
 s (Para ''Sta.Proc_CacheState'' i) = CACHE_I \<or>  s (Para ''Sta.Proc_CacheState'' i) = CACHE_E)"

lemma inv_Sta.Proc_CacheState' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_Sta.Proc_CacheState N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_Sta.Proc_CacheState_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
done
done

lemma inv_Sta.Proc_CacheState'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N 
\<longrightarrow> i \<le> N \<longrightarrow> isEnumVal s (Para ''Sta.Proc_CacheState'' i)"
  using inv_Sta.Proc_CacheState' unfolding type_inv_CurCmd_def 
CACHE_I_def CACHE_E_def 
  by (metis  assms getValueType.simps(1) isEnumVal_def typeOf_def) 

definition type_inv_Sta.Dir.ShrVld :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_Sta.Dir.ShrVld N s = 
(\<forall>i. i \<le> N \<longrightarrow>
 s (Para ''Sta.Dir.ShrVld'' i) = false)"

lemma inv_Sta.Dir.ShrVld' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_Sta.Dir.ShrVld N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_Sta.Dir.ShrVld_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
done
done

lemma inv_Sta.Dir.ShrVld'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N 
false_def 
    using assms by fastforce 

definition type_inv_Sta.Dir.Local :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_Sta.Dir.Local N s = 
(\<forall>i. i \<le> N \<longrightarrow>
 s (Para ''Sta.Dir.Local'' i) = false)"

lemma n_NI_Local_GetX_GetX_type_inv_Sta.Dir.Local [intro]:
  "type_inv_Sta.Dir.Local N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
type_inv_Sta.Dir.Local N (trans1 (act (n_NI_Local_GetX_GetX i)) sk)"
  unfolding type_inv_Sta.Dir.Local_def n_NI_Local_GetX_GetX_def by auto

lemma n_NI_Local_Get_Get_type_inv_Sta.Dir.Local [intro]:
  "type_inv_Sta.Dir.Local N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
type_inv_Sta.Dir.Local N (trans1 (act (n_NI_Local_Get_Get i)) sk)"
  unfolding type_inv_Sta.Dir.Local_def n_NI_Local_Get_Get_def by auto

lemma inv_Sta.Dir.Local' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_Sta.Dir.Local N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_Sta.Dir.Local_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
    subgoal using n_NI_Local_GetX_GetXs_def  by auto
    subgoal using n_NI_Local_Get_Gets_def  by auto
done
done

lemma inv_Sta.Dir.Local'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N 
false_def 
    using assms by fastforce 

definition type_inv_Sta.Dir.Dirty :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_Sta.Dir.Dirty N s = 
(\<forall>i. i \<le> N \<longrightarrow>
 s (Para ''Sta.Dir.Dirty'' i) = true)"

lemma n_NI_Local_GetX_GetX_type_inv_Sta.Dir.Dirty [intro]:
  "type_inv_Sta.Dir.Dirty N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
type_inv_Sta.Dir.Dirty N (trans1 (act (n_NI_Local_GetX_GetX i)) sk)"
  unfolding type_inv_Sta.Dir.Dirty_def n_NI_Local_GetX_GetX_def by auto

lemma n_NI_Local_Get_Get_type_inv_Sta.Dir.Dirty [intro]:
  "type_inv_Sta.Dir.Dirty N sk \<Longrightarrow> i \<le> N \<Longrightarrow> 
type_inv_Sta.Dir.Dirty N (trans1 (act (n_NI_Local_Get_Get i)) sk)"
  unfolding type_inv_Sta.Dir.Dirty_def n_NI_Local_Get_Get_def by auto

lemma inv_Sta.Dir.Dirty' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_Sta.Dir.Dirty N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_Sta.Dir.Dirty_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
    subgoal using n_NI_Local_GetX_GetXs_def  by auto
    subgoal using n_NI_Local_Get_Gets_def  by auto
done
done

lemma inv_Sta.Dir.Dirty'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N 
true_def 
    using assms by fastforce 

definition type_inv_Sta.Dir.HeadVld :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_Sta.Dir.HeadVld N s = 
(\<forall>i. i \<le> N \<longrightarrow>
 s (Para ''Sta.Dir.HeadVld'' i) = true)"

lemma inv_Sta.Dir.HeadVld' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_Sta.Dir.HeadVld N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_Sta.Dir.HeadVld_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
done
done

lemma inv_Sta.Dir.HeadVld'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N 
true_def 
    using assms by fastforce 

definition type_inv_Sta.UniMsg_Cmd :: "nat \<Rightarrow> state \<Rightarrow> bool" where
  "type_inv_Sta.UniMsg_Cmd N s = 
(\<forall>i. i \<le> N \<longrightarrow>
 s (Para ''Sta.UniMsg_Cmd'' i) = UNI_GetX \<or>  s (Para ''Sta.UniMsg_Cmd'' i) = UNI_Get \<or>  s (Para ''Sta.UniMsg_Cmd'' i) = UNI_PutX)"

lemma inv_Sta.UniMsg_Cmd' [simp,intro]:
  assumes "reachableUpTo (set (allInitSpecs N)) (rules2' N) k s"
  shows "type_inv_Sta.UniMsg_Cmd N s"
  apply (rule invIntro[OF _ _ assms])
  subgoal for s
    by (auto simp add: type_inv_Sta.UniMsg_Cmd_def allInitSpecs_def )
  subgoal for r sk
    unfolding rules2'_def apply (auto simp add: pair1_def)
done
done

lemma inv_Sta.UniMsg_Cmd'' [simp,intro]:
  assumes a: "reachableUpTo fs rs k s"
  shows "fs =(set (allInitSpecs N))  \<longrightarrow> rs = rules2' N 
\<longrightarrow> i \<le> N \<longrightarrow> isEnumVal s (Para ''Sta.UniMsg_Cmd'' i)"
  using inv_Sta.UniMsg_Cmd' unfolding type_inv_CurCmd_def 
UNI_GetX_def UNI_Get_def UNI_PutX_def 
  by (metis  assms getValueType.simps(1) isEnumVal_def typeOf_def) 

