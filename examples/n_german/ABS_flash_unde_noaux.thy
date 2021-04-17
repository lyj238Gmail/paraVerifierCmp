theory ABS_flash_unde_noaux
  imports CMP
begin

subsection ‹Definitions›

text ‹type definitions ›

definition CACHE_I :: scalrValueType where [simp]: "CACHE_I≡ enum ''control'' ''CACHE_I''"
definition CACHE_S :: scalrValueType where [simp]: "CACHE_S≡ enum ''control'' ''CACHE_S''"
definition CACHE_E :: scalrValueType where [simp]: "CACHE_E≡ enum ''control'' ''CACHE_E''"
definition NODE_None :: scalrValueType where [simp]: "NODE_None≡ enum ''control'' ''NODE_None''"
definition NODE_Get :: scalrValueType where [simp]: "NODE_Get≡ enum ''control'' ''NODE_Get''"
definition NODE_GetX :: scalrValueType where [simp]: "NODE_GetX≡ enum ''control'' ''NODE_GetX''"
definition UNI_None :: scalrValueType where [simp]: "UNI_None≡ enum ''control'' ''UNI_None''"
definition UNI_Get :: scalrValueType where [simp]: "UNI_Get≡ enum ''control'' ''UNI_Get''"
definition UNI_GetX :: scalrValueType where [simp]: "UNI_GetX≡ enum ''control'' ''UNI_GetX''"
definition UNI_Put :: scalrValueType where [simp]: "UNI_Put≡ enum ''control'' ''UNI_Put''"
definition UNI_PutX :: scalrValueType where [simp]: "UNI_PutX≡ enum ''control'' ''UNI_PutX''"
definition UNI_Nak :: scalrValueType where [simp]: "UNI_Nak≡ enum ''control'' ''UNI_Nak''"
definition INV_None :: scalrValueType where [simp]: "INV_None≡ enum ''control'' ''INV_None''"
definition INV_Inv :: scalrValueType where [simp]: "INV_Inv≡ enum ''control'' ''INV_Inv''"
definition INV_InvAck :: scalrValueType where [simp]: "INV_InvAck≡ enum ''control'' ''INV_InvAck''"
definition RP_None :: scalrValueType where [simp]: "RP_None≡ enum ''control'' ''RP_None''"
definition RP_Replace :: scalrValueType where [simp]: "RP_Replace≡ enum ''control'' ''RP_Replace''"
definition WB_None :: scalrValueType where [simp]: "WB_None≡ enum ''control'' ''WB_None''"
definition WB_Wb :: scalrValueType where [simp]: "WB_Wb≡ enum ''control'' ''WB_Wb''"
definition SHWB_None :: scalrValueType where [simp]: "SHWB_None≡ enum ''control'' ''SHWB_None''"
definition SHWB_ShWb :: scalrValueType where [simp]: "SHWB_ShWb≡ enum ''control'' ''SHWB_ShWb''"
definition SHWB_FAck :: scalrValueType where [simp]: "SHWB_FAck≡ enum ''control'' ''SHWB_FAck''"
definition NAKC_None :: scalrValueType where [simp]: "NAKC_None≡ enum ''control'' ''NAKC_None''"
definition NAKC_Nakc :: scalrValueType where [simp]: "NAKC_Nakc≡ enum ''control'' ''NAKC_Nakc''"
definition true::"scalrValueType" where [simp]: "true≡ boolV True"
definition false::"scalrValueType" where [simp]: "false≡ boolV False"

text ‹initial state ›

definition initSpec0::"nat ⇒ formula" where [simp]:
"initSpec0 N≡ (∀⇩fp. (IVar (Para (''Sta.Proc.ProcCmd'') p)) =⇩f  (Const NODE_None) ) N "

definition initSpec1::"nat ⇒ formula" where [simp]:
"initSpec1 N≡ (∀⇩fp. (IVar (Para (''Sta.Proc.InvMarked'') p)) =⇩f  (Const false) ) N "

definition initSpec2::"nat ⇒ formula" where [simp]:
"initSpec2 N≡ (∀⇩fp. (IVar (Para (''Sta.Proc.CacheState'') p)) =⇩f  (Const CACHE_I) ) N "

definition initSpec3::"nat ⇒ formula" where [simp]:
"initSpec3 N≡ (∀⇩fp. (IVar (Para (''Sta.Proc.CacheData'') p)) =⇩f  (IVar(Ident ''d'')) ) N "

definition initSpec4::"nat ⇒ formula" where [simp]:
"initSpec4 N≡ (∀⇩fp. (IVar (Para (''Sta.Dir.ShrSet'') p)) =⇩f  (Const false) ) N "

definition initSpec5::"nat ⇒ formula" where [simp]:
"initSpec5 N≡ (∀⇩fp. (IVar (Para (''Sta.Dir.InvSet'') p)) =⇩f  (Const false) ) N "

definition initSpec6::"nat ⇒ formula" where [simp]:
"initSpec6 N≡ (∀⇩fp. (IVar (Para (''Sta.UniMsg.Cmd'') p)) =⇩f  (Const UNI_None) ) N "

definition initSpec7::"nat ⇒ formula" where [simp]:
"initSpec7 N≡ (∀⇩fp. (IVar (Para (''Sta.UniMsg.Proc'') p)) =⇩f  (Const (index h)) ) N "

definition initSpec8::"nat ⇒ formula" where [simp]:
"initSpec8 N≡ (∀⇩fp. (IVar (Para (''Sta.UniMsg.HomeProc'') p)) =⇩f  (Const true) ) N "

definition initSpec9::"nat ⇒ formula" where [simp]:
"initSpec9 N≡ (∀⇩fp. (IVar (Para (''Sta.UniMsg.Data'') p)) =⇩f  (IVar(Ident ''d'')) ) N "

definition initSpec10::"nat ⇒ formula" where [simp]:
"initSpec10 N≡ (∀⇩fp. (IVar (Para (''Sta.InvMsg.Cmd'') p)) =⇩f  (Const INV_None) ) N "

definition initSpec11::"nat ⇒ formula" where [simp]:
"initSpec11 N≡ (∀⇩fp. (IVar (Para (''Sta.RpMsg.Cmd'') p)) =⇩f  (Const RP_None) ) N "

definition initSpec12::"formula" where [simp]:
"initSpec12 ≡ (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_None) "

definition initSpec13::"formula" where [simp]:
"initSpec13 ≡ (IVar (Ident ''Sta.HomeProc.InvMarked'')) =⇩f  (Const false) "

definition initSpec14::"formula" where [simp]:
"initSpec14 ≡ (IVar (Ident ''Sta.HomeProc.CacheState'')) =⇩f  (Const CACHE_I) "

definition initSpec15::"formula" where [simp]:
"initSpec15 ≡ (IVar (Ident ''Sta.Dir.HomeShrSet'')) =⇩f  (Const false) "

definition initSpec16::"formula" where [simp]:
"initSpec16 ≡ (IVar (Ident ''Sta.Dir.HomeInvSet'')) =⇩f  (Const false) "

definition initSpec17::"formula" where [simp]:
"initSpec17 ≡ (IVar (Ident ''Sta.HomeUniMsg.Cmd'')) =⇩f  (Const UNI_None) "

definition initSpec18::"formula" where [simp]:
"initSpec18 ≡ (IVar (Ident ''Sta.HomeUniMsg.HomeProc'')) =⇩f  (Const true) "

definition initSpec19::"formula" where [simp]:
"initSpec19 ≡ (IVar (Ident ''Sta.HomeInvMsg.Cmd'')) =⇩f  (Const INV_None) "

definition initSpec20::"formula" where [simp]:
"initSpec20 ≡ (IVar (Ident ''Sta.HomeRpMsg.Cmd'')) =⇩f  (Const RP_None) "

lemma absInitSpec:
assumes "M ≤ N"
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


definition allInitSpecs::"nat ⇒ formula list" where
"allInitSpecs N ≡ [
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
  "symPredSet' N (    {(initSpec0 N)} ∪
    {(initSpec1 N)} ∪
    {(initSpec2 N)} ∪
    {(initSpec3 N)} ∪
    {(initSpec4 N)} ∪
    {(initSpec5 N)} ∪
    {(initSpec6 N)} ∪
    {(initSpec7 N)} ∪
    {(initSpec8 N)} ∪
    {(initSpec9 N)} ∪
    {(initSpec10 N)} ∪
    {(initSpec11 N)} ∪
    {initSpec12} ∪
    {initSpec13} ∪
    {initSpec14} ∪
    {initSpec15} ∪
    {initSpec16} ∪
    {initSpec17} ∪
    {initSpec18} ∪
    {initSpec19} ∪
    {initSpec20})"

  apply (meson symPreds0 symPreds1 symPreds2 symPreds3 symPreds4 symPreds5 symPreds6 symPreds7 symPreds8 symPreds9 symPreds10 symPreds11 symPreds12 symPreds13 symPreds14 symPreds15 symPreds16 symPreds17 symPreds18 symPreds19 symPreds20 
symPredsUnion)
  done

lemma symPreds':
"symPredSet' N (set (allInitSpecs N))"
  proof -
    have b1:"(set (allInitSpecs N)) =
    {(initSpec0 N)}∪
    {(initSpec1 N)}∪
    {(initSpec2 N)}∪
    {(initSpec3 N)}∪
    {(initSpec4 N)}∪
    {(initSpec5 N)}∪
    {(initSpec6 N)}∪
    {(initSpec7 N)}∪
    {(initSpec8 N)}∪
    {(initSpec9 N)}∪
    {(initSpec10 N)}∪
    {(initSpec11 N)}∪
    {(initSpec12 )}∪
    {(initSpec13 )}∪
    {(initSpec14 )}∪
    {(initSpec15 )}∪
    {(initSpec16 )}∪
    {(initSpec17 )}∪
    {(initSpec18 )}∪
    {(initSpec19 )}∪
    {(initSpec20 )}" (is "?LHS=?RHS")
      using allInitSpecs_def by auto
    have b2:"symPredSet' N ?RHS"
      using symPreds by blast
    show "symPredSet' N (set (allInitSpecs N))"
      using b1 b2 by auto
  qed

definition n_NI_Replace_Home1::"nat ⇒ rule" where 
"n_NI_Replace_Home1  src ≡
(IVar (Ident ''Sta.HomeRpMsg.Cmd''))  =⇩f (Const RP_Replace) ∧⇩f
IVar (Ident ''  Sta.Dir.ShrVld'') =⇩f  (Const true)
   ▹
(assign ((Ident ''Sta.HomeRpMsg.Cmd''), (Const RP_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))"

definition n_NI_Replace_Home2::"nat ⇒ rule" where 
"n_NI_Replace_Home2  src ≡
(IVar (Ident ''Sta.HomeRpMsg.Cmd''))  =⇩f (Const RP_Replace) ∧⇩f
IVar (Ident ''Sta.Dir.ShrVld'') =⇩f  (Const false)
   ▹
(assign ((Ident ''Sta.HomeRpMsg.Cmd''), (Const RP_None)))"

definition n_NI_Replace3::"nat ⇒ rule" where 
"n_NI_Replace3  src ≡
(IVar (Para (''Sta.RpMsg.Cmd'') src)) =⇩f  (Const RP_Replace) ∧⇩f
IVar (Ident ''  Sta.Dir.ShrVld'') =⇩f  (Const true)
   ▹
(assign (Para (''Sta.RpMsg.Cmd'') src, (Const RP_None)))||
(assign (Para (''Sta.Dir.ShrSet'') src, (Const false)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))"

definition n_NI_Replace4::"nat ⇒ rule" where 
"n_NI_Replace4  src ≡
(IVar (Para (''Sta.RpMsg.Cmd'') src)) =⇩f  (Const RP_Replace) ∧⇩f
IVar (Ident ''Sta.Dir.ShrVld'') =⇩f  (Const false)
   ▹
(assign (Para (''Sta.RpMsg.Cmd'') src, (Const RP_None)))"

definition n_NI_ShWb5::"nat ⇒ nat ⇒ rule" where 
"n_NI_ShWb5  src  ≡
(IVar (Ident ''Sta.ShWbMsg.Cmd''))  =⇩f (Const SHWB_ShWb) ∧⇩f
IVar (Ident ''  Sta.ShWbMsg.HomeProc'') =⇩f  (Const true)
   ▹
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_None)))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const true)))||
forallStm(λj. (assign ((Ident ''if (p''), (IVar (Para (''Sta.ShWbMsg.Proc & Sta.ShWbMsg.HomeProc = false) | Sta.Dir.ShrSet'') p)))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.Dir.ShrSet'') p, (Const false)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))"

definition n_NI_ShWb6::"nat ⇒ nat ⇒ rule" where 
"n_NI_ShWb6  src  ≡
(IVar (Ident ''Sta.ShWbMsg.Cmd''))  =⇩f (Const SHWB_ShWb) ∧⇩f
IVar (Ident ''  Sta.Dir.HomeShrSet'') =⇩f  (Const true)
   ▹
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_None)))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const true)))||
forallStm(λj. (assign ((Ident ''if (p''), (IVar (Para (''Sta.ShWbMsg.Proc & Sta.ShWbMsg.HomeProc = false) | Sta.Dir.ShrSet'') p)))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.Dir.ShrSet'') p, (Const false)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))"

definition n_NI_ShWb7::"nat ⇒ nat ⇒ rule" where 
"n_NI_ShWb7  src  ≡
(IVar (Ident ''Sta.ShWbMsg.Cmd''))  =⇩f (Const SHWB_ShWb) ∧⇩f
IVar (Ident ''Sta.ShWbMsg.HomeProc '') =⇩f  (Const false) ∧⇩f
IVar (Ident ''Sta.Dir.HomeShrSet'') =⇩f  (Const false)
   ▹
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_None)))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const true)))||
forallStm(λj. (assign ((Ident ''if (p''), (IVar (Para (''Sta.ShWbMsg.Proc & Sta.ShWbMsg.HomeProc = false) | Sta.Dir.ShrSet'') p)))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.Dir.ShrSet'') p, (Const false)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))"

definition n_NI_FAck8::"nat ⇒ rule" where 
"n_NI_FAck8  src ≡
(IVar (Ident ''Sta.ShWbMsg.Cmd''))  =⇩f (Const SHWB_FAck) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)
   ▹
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_None)))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), ((Ident ''Sta.ShWbMsg.Proc''))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const Sta.ShWbMsg.HomeProc)))"

definition n_NI_FAck9::"nat ⇒ rule" where 
"n_NI_FAck9  src ≡
(IVar (Ident ''Sta.ShWbMsg.Cmd''))  =⇩f (Const SHWB_FAck) ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.Dirty'')) =⇩f  (Const true)
   ▹
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_None)))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Wb10::"nat ⇒ rule" where 
"n_NI_Wb10  src ≡
(IVar (Ident ''Sta.WbMsg.Cmd''))  =⇩f (Const WB_Wb)
   ▹
(assign ((Ident ''Sta.WbMsg.Cmd''), (Const WB_None)))||
(assign ((Ident ''Sta.WbMsg.HomeProc''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const false)))"

definition n_NI_InvAck_311::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_InvAck_311  src p N ≡
(IVar (Para (''Sta.InvMsg.Cmd'') src)) =⇩f  (Const INV_InvAck) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true) ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') src)) =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =⇩f (Const false) ∧⇩f
(∀⇩fj. (IVar (Para (''p = src | Sta.Dir.InvSet'') p)) =⇩f  (Const false) ) N
   ▹
(assign (Para (''Sta.InvMsg.Cmd'') src, (Const INV_None)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))"

definition n_NI_InvAck_212::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_InvAck_212 src p N ≡
(IVar (Para (''Sta.InvMsg.Cmd'') src)) =⇩f  (Const INV_InvAck) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true) ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') src)) =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =⇩f (Const false) ∧⇩f
(∀⇩fj. (IVar (Para (''Sta.Dir.InvSet'') p)) =⇩f  (Const false) ) N
   ▹
(assign (Para (''Sta.InvMsg.Cmd'') src, (Const INV_None)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))"

definition n_NI_InvAck_113::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_InvAck_113  src p N ≡
(IVar (Para (''Sta.InvMsg.Cmd'') src)) =⇩f  (Const INV_InvAck) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true) ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') src)) =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =⇩f (Const false) ∧⇩f
(∀⇩fj. (IVar (Para (''Sta.Dir.InvSet'') p)) =⇩f  (Const false) ) N
   ▹
(assign (Para (''Sta.InvMsg.Cmd'') src, (Const INV_None)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))"

definition n_NI_InvAck_exists14::"nat ⇒ nat ⇒ rule" where 
"n_NI_InvAck_exists14  dst src  ≡
(IVar (Para (''Sta.InvMsg.Cmd'') src)) =⇩f  (Const INV_InvAck) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true) ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') src)) =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Ident ''dst'')) =⇩f  (Const (index src)) ∧⇩f
IVar (Ident ''  Sta.Dir.InvSet[dst]'') =⇩f  (Const true)
   ▹
(assign (Para (''Sta.InvMsg.Cmd'') src, (Const INV_None)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))"

definition n_NI_InvAck_exists_Home15::"nat ⇒ rule" where 
"n_NI_InvAck_exists_Home15  src ≡
(IVar (Para (''Sta.InvMsg.Cmd'') src)) =⇩f  (Const INV_InvAck) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true) ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') src)) =⇩f  (Const true) ∧⇩f
IVar (Ident ''  Sta.Dir.HomeInvSet'') =⇩f  (Const true)
   ▹
(assign (Para (''Sta.InvMsg.Cmd'') src, (Const INV_None)))||
(assign (Para (''Sta.Dir.InvSet'') src, (Const false)))"

definition n_NI_Inv16::"nat ⇒ rule" where 
"n_NI_Inv16  dst ≡
(IVar (Para (''Sta.InvMsg.Cmd'') dst)) =⇩f  (Const INV_Inv) ∧⇩f
(IVar (Para (''Sta.Proc.ProcCmd'') dst)) =⇩f  (Const NODE_Get)
   ▹
(assign (Para (''Sta.InvMsg.Cmd'') dst, (Const INV_InvAck)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign (Para (''Sta.Proc.InvMarked'') dst, (Const true)))"

definition n_NI_Inv17::"nat ⇒ rule" where 
"n_NI_Inv17  dst ≡
(IVar (Para (''Sta.InvMsg.Cmd'') dst)) =⇩f  (Const INV_Inv) ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.ProcCmd'') dst)) =⇩f  (Const NODE_Get)
   ▹
(assign (Para (''Sta.InvMsg.Cmd'') dst, (Const INV_InvAck)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))"

definition n_NI_Remote_PutX18::"nat ⇒ rule" where 
"n_NI_Remote_PutX18  dst ≡
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =⇩f  (Const UNI_PutX) ∧⇩f
(IVar (Para (''Sta.Proc.ProcCmd'') dst)) =⇩f  (Const NODE_GetX)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''Sta.UniMsg.HomeProc'') dst, (Const false)))||
(assign (Para (''Sta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''Sta.Proc.InvMarked'') dst, (Const false)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_E)))||
(assign (Para (''Sta.Proc.CacheData'') dst, (IVar (Para (''Sta.UniMsg.Data'') dst))))"

definition n_NI_Local_PutXAcksDone19::"nat ⇒ rule" where 
"n_NI_Local_PutXAcksDone19  src ≡
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =⇩f (Const UNI_PutX)
   ▹
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.HomeUniMsg.HomeProc''), (Const false)))||
(assign ((Ident ''Sta.Dir.Local''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_E)))||
(assign ((Ident ''Sta.HomeProc.CacheData''), (IVar (Ident ''Sta.HomeUniMsg.Data''))))"

definition n_NI_Remote_Put20::"nat ⇒ rule" where 
"n_NI_Remote_Put20  dst ≡
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =⇩f  (Const UNI_Put) ∧⇩f
IVar (Ident ''  Sta.Proc[dst].InvMarked'') =⇩f  (Const true)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''Sta.UniMsg.HomeProc'') dst, (Const false)))||
(assign (Para (''Sta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''Sta.Proc.InvMarked'') dst, (Const false)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))"

definition n_NI_Remote_Put21::"nat ⇒ rule" where 
"n_NI_Remote_Put21  dst ≡
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =⇩f  (Const UNI_Put) ∧⇩f
IVar (Ident ''Sta.Proc[dst].InvMarked'') =⇩f  (Const false)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''Sta.UniMsg.HomeProc'') dst, (Const false)))||
(assign (Para (''Sta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_S)))||
(assign (Para (''Sta.Proc.CacheData'') dst, (IVar (Para (''Sta.UniMsg.Data'') dst))))"

definition n_NI_Local_Put22::"nat ⇒ rule" where 
"n_NI_Local_Put22  src ≡
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =⇩f (Const UNI_Put) ∧⇩f
IVar (Ident ''  Sta.HomeProc.InvMarked'') =⇩f  (Const true)
   ▹
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.HomeUniMsg.HomeProc''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))||
(assign ((Ident ''Sta.Dir.Local''), (Const true)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_Put23::"nat ⇒ rule" where 
"n_NI_Local_Put23  src ≡
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =⇩f (Const UNI_Put) ∧⇩f
IVar (Ident ''Sta.HomeProc.InvMarked'') =⇩f  (Const false)
   ▹
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.HomeUniMsg.HomeProc''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))||
(assign ((Ident ''Sta.Dir.Local''), (Const true)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_S)))"

definition n_NI_Remote_GetX_PutX_Home24::"nat ⇒ rule" where 
"n_NI_Remote_GetX_PutX_Home24  dst ≡
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =⇩f (Const UNI_GetX) ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =⇩f (Const (index dst)) ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =⇩f (Const false) ∧⇩f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =⇩f  (Const CACHE_E)
   ▹
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeUniMsg.Data''), (IVar (Para (''Sta.Proc.CacheData'') dst))))"

definition n_NI_Remote_GetX_PutX25::"nat ⇒ nat ⇒ rule" where 
"n_NI_Remote_GetX_PutX25  dst src  ≡
¬⇩f (IVar (Ident ''src'')) =⇩f  (Const (index dst)) ∧⇩f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =⇩f  (Const (index dst)) ∧⇩f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =⇩f  (Const false) ∧⇩f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =⇩f  (Const CACHE_E)
   ▹
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign (Para (''Sta.UniMsg.Data'') src, (IVar (Para (''Sta.Proc.CacheData'') dst))))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_FAck)))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index src))))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_GetX_Nak_Home26::"nat ⇒ rule" where 
"n_NI_Remote_GetX_Nak_Home26  dst ≡
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =⇩f (Const UNI_GetX) ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =⇩f (Const (index dst)) ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =⇩f (Const false) ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') dst)) =⇩f  (Const CACHE_E)
   ▹
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Nak)))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_GetX_Nak27::"nat ⇒ nat ⇒ rule" where 
"n_NI_Remote_GetX_Nak27  dst src  ≡
¬⇩f (IVar (Ident ''src'')) =⇩f  (Const (index dst)) ∧⇩f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =⇩f  (Const (index dst)) ∧⇩f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =⇩f  (Const false) ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') dst)) =⇩f  (Const CACHE_E)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (Const (index dst))))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const false)))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Local_GetX_PutX_1128::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_1128  src p N  ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_E)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign (Para (''Sta.UniMsg.Data'') src, (IVar (Ident ''StaHomeProcCacheData''))))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_1029::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_1029  N src p  ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.ShrSet[dst] '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))"

definition n_NI_Local_GetX_PutX_10_Home30::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_10_Home30  src p N  ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HomeShrSet '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))"

definition n_NI_Local_GetX_PutX_931::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_931  src p N ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))"

definition n_NI_Local_GetX_PutX_932::"nat ⇒nat ⇒  nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_932  src p N ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))"

definition n_NI_Local_GetX_PutX_8_NODE_Get33::"nat ⇒nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_8_NODE_Get33  p src N ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.ShrSet[dst] '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_834::"nat ⇒nat ⇒  nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_834  N src p ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.ShrSet[dst] '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_8_Home_NODE_Get35::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_8_Home_NODE_Get35  src p N ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HomeShrSet '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_8_Home36::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_8_Home36  src p N  ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HomeShrSet '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_7_NODE_Get37::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_7_NODE_Get37  src p N  ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_7_NODE_Get38::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_7_NODE_Get38  src p N  ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_739::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_739  src p N  ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_740::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_740  src p N  ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_641::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_641  src p N ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =⇩f (Const false) ∧⇩f
(∀⇩fj. (IVar (Para (''Sta.Dir.ShrSet'') p)) =⇩f  (Const false) ) N ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_542::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_542 p N src  ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =⇩f (Const false) ∧⇩f
(∀⇩fj. (IVar (Para (''Sta.Dir.ShrSet'') p)) =⇩f  (Const false) ) N ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_443::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_443 p N src  ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =⇩f (Const false) ∧⇩f
(∀⇩fj. (IVar (Para (''Sta.Dir.ShrSet'') p)) =⇩f  (Const false) ) N ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_344::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_344  src p N ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_245::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_245  src p N ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_146::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_NI_Local_GetX_PutX_146  src p N ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_PutX)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_GetX47::"nat ⇒ rule" where 
"n_NI_Local_GetX_GetX47  src ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false) ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index src))
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_GetX)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident ''StaDirHeadPtr''))))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (IVar (Ident ''StaDirHomeHeadPtr''))))"

definition n_NI_Local_GetX_GetX48::"nat ⇒ rule" where 
"n_NI_Local_GetX_GetX48  src ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const true)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_GetX)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident ''StaDirHeadPtr''))))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (IVar (Ident ''StaDirHomeHeadPtr''))))"

definition n_NI_Local_GetX_Nak49::"nat ⇒ rule" where 
"n_NI_Local_GetX_Nak49  src ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_NI_Local_GetX_Nak50::"nat ⇒ rule" where 
"n_NI_Local_GetX_Nak50  src ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.CacheState'')) =⇩f  (Const CACHE_E)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_NI_Local_GetX_Nak51::"nat ⇒ rule" where 
"n_NI_Local_GetX_Nak51  src ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_GetX) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_NI_Remote_Get_Put_Home52::"nat ⇒ rule" where 
"n_NI_Remote_Get_Put_Home52  dst ≡
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =⇩f (Const UNI_Get) ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =⇩f (Const (index dst)) ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =⇩f (Const false) ∧⇩f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =⇩f  (Const CACHE_E)
   ▹
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_S)))||
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Put)))||
(assign ((Ident ''Sta.HomeUniMsg.Data''), (IVar (Para (''Sta.Proc.CacheData'') dst))))"

definition n_NI_Remote_Get_Put53::"nat ⇒ nat ⇒ rule" where 
"n_NI_Remote_Get_Put53  dst src  ≡
¬⇩f (IVar (Ident ''src'')) =⇩f  (Const (index dst)) ∧⇩f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_Get) ∧⇩f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =⇩f  (Const (index dst)) ∧⇩f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =⇩f  (Const false) ∧⇩f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =⇩f  (Const CACHE_E)
   ▹
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_S)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Put)))||
(assign (Para (''Sta.UniMsg.Data'') src, (IVar (Para (''Sta.Proc.CacheData'') dst))))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_ShWb)))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index src))))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))||
(assign ((Ident ''Sta.ShWbMsg.Data''), (IVar (Para (''Sta.Proc.CacheData'') dst))))"

definition n_NI_Remote_Get_Nak_Home54::"nat ⇒ rule" where 
"n_NI_Remote_Get_Nak_Home54  dst ≡
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =⇩f (Const UNI_Get) ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =⇩f (Const (index dst)) ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =⇩f (Const false) ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') dst)) =⇩f  (Const CACHE_E)
   ▹
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Nak)))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_Get_Nak55::"nat ⇒ nat ⇒ rule" where 
"n_NI_Remote_Get_Nak55  dst src  ≡
¬⇩f (IVar (Ident ''src'')) =⇩f  (Const (index dst)) ∧⇩f
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_Get) ∧⇩f
(IVar (Para (''Sta.UniMsg.Proc'') src)) =⇩f  (Const (index dst)) ∧⇩f
(IVar (Para (''Sta.UniMsg.HomeProc'') src)) =⇩f  (Const false) ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') dst)) =⇩f  (Const CACHE_E)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (Const (index dst))))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const false)))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Local_Get_Put_Dirty56::"nat ⇒ rule" where 
"n_NI_Local_Get_Put_Dirty56  src ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_Get) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =⇩f  (Const RP_Replace) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_E)
   ▹
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_S)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Put)))||
(assign (Para (''Sta.UniMsg.Data'') src, (IVar (Ident ''StaHomeProcCacheData''))))"

definition n_NI_Local_Get_Put57::"nat ⇒ rule" where 
"n_NI_Local_Get_Put57  src ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_Get) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =⇩f  (Const RP_Replace) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false)
   ▹
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index src))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Put)))"

definition n_NI_Local_Get_Put_Head58::"nat ⇒ nat ⇒ rule" where 
"n_NI_Local_Get_Put_Head58  src  ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_Get) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =⇩f  (Const RP_Replace) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.Dir.HeadVld'') =⇩f  (Const true)
   ▹
(assign ((Ident ''Sta.Dir.ShrVld''), (Const true)))||
(assign (Para (''Sta.Dir.ShrSet'') src, (Const true)))||
forallStm(λj. (assign ((Ident ''if (p''), (Const src) then))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (IVar (Para (''Sta.Dir.ShrSet'') p))))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const Sta.Dir.HomeShrSet)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Put)))||
(assign (Para (''Sta.UniMsg.Data'') src, (Const Sta.MemData)))"

definition n_NI_Local_Get_Get59::"nat ⇒ rule" where 
"n_NI_Local_Get_Get59  src ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_Get) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =⇩f  (Const RP_Replace) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false) ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index src))
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Get)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident ''StaDirHeadPtr''))))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (IVar (Ident ''StaDirHomeHeadPtr''))))"

definition n_NI_Local_Get_Get60::"nat ⇒ rule" where 
"n_NI_Local_Get_Get60  src ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_Get) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =⇩f  (Const RP_Replace) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const true)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Get)))||
(assign (Para (''Sta.UniMsg.Proc'') src, (IVar (Ident ''StaDirHeadPtr''))))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (IVar (Ident ''StaDirHomeHeadPtr''))))"

definition n_NI_Local_Get_Nak61::"nat ⇒ rule" where 
"n_NI_Local_Get_Nak61  src ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_Get) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =⇩f  (Const RP_Replace) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_NI_Local_Get_Nak62::"nat ⇒ rule" where 
"n_NI_Local_Get_Nak62  src ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_Get) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =⇩f  (Const RP_Replace) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.CacheState'')) =⇩f  (Const CACHE_E)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_NI_Local_Get_Nak63::"nat ⇒ rule" where 
"n_NI_Local_Get_Nak63  src ≡
(IVar (Para (''Sta.UniMsg.Cmd'') src)) =⇩f  (Const UNI_Get) ∧⇩f
IVar (Ident ''  Sta.UniMsg[src].HomeProc '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Para (''Sta.RpMsg.Cmd'') src)) =⇩f  (Const RP_Replace) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index src)) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Nak)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_NI_Nak_Clear64::"nat ⇒ rule" where 
"n_NI_Nak_Clear64  src ≡
(IVar (Ident ''Sta.NakcMsg.Cmd''))  =⇩f (Const NAKC_Nakc)
   ▹
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_None)))"

definition n_NI_Nak_Home65::"nat ⇒ rule" where 
"n_NI_Nak_Home65  src ≡
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =⇩f (Const UNI_Nak)
   ▹
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_None)))||
(assign ((Ident ''Sta.HomeUniMsg.HomeProc''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const false)))"

definition n_NI_Nak66::"nat ⇒ rule" where 
"n_NI_Nak66  dst ≡
(IVar (Para (''Sta.UniMsg.Cmd'') dst)) =⇩f  (Const UNI_Nak)
   ▹
(assign (Para (''Sta.UniMsg.Cmd'') dst, (Const UNI_None)))||
(assign (Para (''Sta.UniMsg.HomeProc'') dst, (Const false)))||
(assign (Para (''Sta.Proc.ProcCmd'') dst, (Const NODE_None)))||
(assign (Para (''Sta.Proc.InvMarked'') dst, (Const false)))"

definition n_PI_Local_Replace67::"nat ⇒ rule" where 
"n_PI_Local_Replace67  src ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_S)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_PI_Remote_Replace68::"nat ⇒ rule" where 
"n_PI_Remote_Replace68  src ≡
(IVar (Para (''Sta.Proc.ProcCmd'') src)) =⇩f  (Const NODE_None) ∧⇩f
(IVar (Para (''Sta.Proc.CacheState'') src)) =⇩f  (Const CACHE_S)
   ▹
(assign (Para (''Sta.Proc.CacheState'') src, (Const CACHE_I)))||
(assign (Para (''Sta.RpMsg.Cmd'') src, (Const RP_Replace)))"

definition n_PI_Local_PutX69::"nat ⇒ rule" where 
"n_PI_Local_PutX69  src ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_E) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)
   ▹
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))"

definition n_PI_Local_PutX70::"nat ⇒ rule" where 
"n_PI_Local_PutX70  src ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_E) ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.Pending'')) =⇩f  (Const true)
   ▹
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const false)))"

definition n_PI_Remote_PutX71::"nat ⇒ rule" where 
"n_PI_Remote_PutX71  dst ≡
(IVar (Para (''Sta.Proc.ProcCmd'') dst)) =⇩f  (Const NODE_None) ∧⇩f
(IVar (Para (''Sta.Proc.CacheState'') dst)) =⇩f  (Const CACHE_E)
   ▹
(assign (Para (''Sta.Proc.CacheState'') dst, (Const CACHE_I)))||
(assign ((Ident ''Sta.WbMsg.Cmd''), (Const WB_Wb)))||
(assign ((Ident ''Sta.WbMsg.Proc''), (Const (index dst))))||
(assign ((Ident ''Sta.WbMsg.HomeProc''), (Const false)))||
(assign ((Ident ''Sta.WbMsg.Data''), (IVar (Para (''Sta.Proc.CacheData'') dst))))"

definition n_PI_Local_GetX_PutX_HeadVld7572::"nat ⇒nat ⇒ nat ⇒ rule" where 
"n_PI_Local_GetX_PutX_HeadVld7572  src p N ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_S) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const true)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_E)))"

definition n_PI_Local_GetX_PutX_HeadVld7473::"nat ⇒nat ⇒ nat ⇒ rule" where 
"n_PI_Local_GetX_PutX_HeadVld7473  src p N ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_I) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const true)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_E)))"

definition n_PI_Local_GetX_PutX7374::"nat ⇒ rule" where 
"n_PI_Local_GetX_PutX7374  src ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_S) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const true)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_E)))"

definition n_PI_Local_GetX_PutX7275::"nat ⇒ rule" where 
"n_PI_Local_GetX_PutX7275  src ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_I) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const true)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_E)))"

definition n_PI_Local_GetX_PutX_HeadVld76::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_PI_Local_GetX_PutX_HeadVld76  src p N ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_I) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const true)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_E)))"

definition n_PI_Local_GetX_PutX_HeadVld77::"nat ⇒ nat ⇒ nat ⇒ rule" where 
"n_PI_Local_GetX_PutX_HeadVld77  src p N ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_S) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const true)))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true)))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const false)))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false)))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false))))N||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv)))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false)))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None)))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false)))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false)))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_E)))"

definition n_PI_Local_GetX_GetX78::"nat ⇒ rule" where 
"n_PI_Local_GetX_GetX78  src ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_I) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)
   ▹
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_GetX)))||
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_GetX)))||
(assign ((Ident ''Sta.HomeUniMsg.Proc''), (IVar (Ident ''Sta.Dir.HeadPtr''))))||
(assign ((Ident ''Sta.HomeUniMsg.HomeProc''), (IVar (Ident ''Sta.Dir.HomeHeadPtr''))))"

definition n_PI_Local_GetX_GetX79::"nat ⇒ rule" where 
"n_PI_Local_GetX_GetX79  src ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_S) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)
   ▹
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_GetX)))||
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_GetX)))||
(assign ((Ident ''Sta.HomeUniMsg.Proc''), (IVar (Ident ''Sta.Dir.HeadPtr''))))||
(assign ((Ident ''Sta.HomeUniMsg.HomeProc''), (IVar (Ident ''Sta.Dir.HomeHeadPtr''))))"

definition n_PI_Remote_GetX80::"nat ⇒ rule" where 
"n_PI_Remote_GetX80  src ≡
(IVar (Para (''Sta.Proc.ProcCmd'') src)) =⇩f  (Const NODE_None) ∧⇩f
(IVar (Para (''Sta.Proc.CacheState'') src)) =⇩f  (Const CACHE_I)
   ▹
(assign (Para (''Sta.Proc.ProcCmd'') src, (Const NODE_GetX)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_GetX)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_PI_Local_Get_Put81::"nat ⇒ rule" where 
"n_PI_Local_Get_Put81  src ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_I) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''  Sta.HomeProc.InvMarked'') =⇩f  (Const true)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const true)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const false)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_PI_Local_Get_Put82::"nat ⇒ rule" where 
"n_PI_Local_Get_Put82  src ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_I) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false) ∧⇩f
IVar (Ident ''Sta.HomeProc.InvMarked'') =⇩f  (Const false)
   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const true)))||
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_None)))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_S)))"

definition n_PI_Local_Get_Get83::"nat ⇒ rule" where 
"n_PI_Local_Get_Get83  src ≡
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_None) ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_I) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false) ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)
   ▹
(assign ((Ident ''Sta.HomeProc.ProcCmd''), (Const NODE_Get)))||
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Get)))||
(assign ((Ident ''Sta.HomeUniMsg.Proc''), (IVar (Ident ''Sta.Dir.HeadPtr''))))||
(assign ((Ident ''Sta.HomeUniMsg.HomeProc''), (IVar (Ident ''Sta.Dir.HomeHeadPtr''))))"

definition n_PI_Remote_Get84::"nat ⇒ rule" where 
"n_PI_Remote_Get84  src ≡
(IVar (Para (''Sta.Proc.ProcCmd'') src)) =⇩f  (Const NODE_None) ∧⇩f
(IVar (Para (''Sta.Proc.CacheState'') src)) =⇩f  (Const CACHE_I)
   ▹
(assign (Para (''Sta.Proc.ProcCmd'') src, (Const NODE_Get)))||
(assign (Para (''Sta.UniMsg.Cmd'') src, (Const UNI_Get)))||
(assign (Para (''Sta.UniMsg.HomeProc'') src, (Const true)))"

definition n_Store_Home85::"nat ⇒ rule" where 
"n_Store_Home85 src ≡
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_E)
   ▹
(assign ((Ident ''Sta.HomeProc.CacheData''), (IVar(Ident ''data''))))||
(assign ((Ident ''Sta.CurrData''), (IVar(Ident ''data''))))"

definition n_Store86::"nat ⇒ rule" where 
"n_Store86  src ≡
(IVar (Para (''Sta.Proc.CacheState'') src)) =⇩f  (Const CACHE_E)
   ▹
(assign (Para (''Sta.Proc.CacheData'') src, (IVar(Ident ''data''))))||
(assign ((Ident ''Sta.CurrData''), (IVar(Ident ''data''))))"

subsection ‹Putting everything together ---definition of rules›

definition n_NI_Replace_Home1s::" nat⇒rule set" where 
  "n_NI_Replace_Home1s N== oneParamCons N  n_NI_Replace_Home1"

definition n_NI_Replace_Home2s::" nat⇒rule set" where 
  "n_NI_Replace_Home2s N== oneParamCons N  n_NI_Replace_Home2"

definition n_NI_Replace3s::" nat⇒rule set" where 
  "n_NI_Replace3s N== oneParamCons N  n_NI_Replace3"

definition n_NI_Replace4s::" nat⇒rule set" where 
  "n_NI_Replace4s N== oneParamCons N  n_NI_Replace4"

definition n_NI_ShWb5s::" nat⇒rule set" where 
  "n_NI_ShWb5s N== oneParamCons N  (n_NI_ShWb5 N)"

definition n_NI_ShWb6s::" nat⇒rule set" where 
  "n_NI_ShWb6s N== oneParamCons N  (n_NI_ShWb6 N)"

definition n_NI_ShWb7s::" nat⇒rule set" where 
  "n_NI_ShWb7s N== oneParamCons N  (n_NI_ShWb7 N)"

definition n_NI_FAck8s::" nat⇒rule set" where 
  "n_NI_FAck8s N== oneParamCons N  n_NI_FAck8"

definition n_NI_FAck9s::" nat⇒rule set" where 
  "n_NI_FAck9s N== oneParamCons N  n_NI_FAck9"

definition n_NI_Wb10s::" nat⇒rule set" where 
  "n_NI_Wb10s N== oneParamCons N  n_NI_Wb10"

definition n_NI_InvAck_311s::" nat⇒ nat⇒rule set" where 
  "n_NI_InvAck_311s N p== oneParamCons N  (n_NI_InvAck_311 N p)"

definition n_NI_InvAck_212s::" nat⇒ nat⇒rule set" where 
  "n_NI_InvAck_212s N p== oneParamCons N  (n_NI_InvAck_212 N p)"

definition n_NI_InvAck_113s::" nat⇒ nat⇒rule set" where 
  "n_NI_InvAck_113s N p== oneParamCons N  (n_NI_InvAck_113 N p)"

definition n_NI_InvAck_exists14s::" nat⇒ nat⇒rule set" where 
  "n_NI_InvAck_exists14s dst src == oneParamCons N  (n_NI_InvAck_exists14 dst src)"

definition n_NI_InvAck_exists_Home15s::" nat⇒rule set" where 
  "n_NI_InvAck_exists_Home15s N== oneParamCons N  n_NI_InvAck_exists_Home15"

definition n_NI_Inv16s::" nat⇒rule set" where 
  "n_NI_Inv16s N== oneParamCons N  n_NI_Inv16"

definition n_NI_Inv17s::" nat⇒rule set" where 
  "n_NI_Inv17s N== oneParamCons N  n_NI_Inv17"

definition n_NI_Remote_PutX18s::" nat⇒rule set" where 
  "n_NI_Remote_PutX18s N== oneParamCons N  n_NI_Remote_PutX18"

definition n_NI_Local_PutXAcksDone19s::" nat⇒rule set" where 
  "n_NI_Local_PutXAcksDone19s N== oneParamCons N  n_NI_Local_PutXAcksDone19"

definition n_NI_Remote_Put20s::" nat⇒rule set" where 
  "n_NI_Remote_Put20s N== oneParamCons N  n_NI_Remote_Put20"

definition n_NI_Remote_Put21s::" nat⇒rule set" where 
  "n_NI_Remote_Put21s N== oneParamCons N  n_NI_Remote_Put21"

definition n_NI_Local_Put22s::" nat⇒rule set" where 
  "n_NI_Local_Put22s N== oneParamCons N  n_NI_Local_Put22"

definition n_NI_Local_Put23s::" nat⇒rule set" where 
  "n_NI_Local_Put23s N== oneParamCons N  n_NI_Local_Put23"

definition n_NI_Remote_GetX_PutX_Home24s::" nat⇒rule set" where 
  "n_NI_Remote_GetX_PutX_Home24s N== oneParamCons N  n_NI_Remote_GetX_PutX_Home24"

definition n_NI_Remote_GetX_PutX25s::" nat⇒ nat⇒rule set" where 
  "n_NI_Remote_GetX_PutX25s N p== oneParamCons N  (n_NI_Remote_GetX_PutX25 N p)"

definition n_NI_Remote_GetX_Nak_Home26s::" nat⇒rule set" where 
  "n_NI_Remote_GetX_Nak_Home26s N== oneParamCons N  n_NI_Remote_GetX_Nak_Home26"

definition n_NI_Remote_GetX_Nak27s::" nat⇒rule set" where 
  "n_NI_Remote_GetX_Nak27s N== oneParamCons N  n_NI_Remote_GetX_Nak27"

definition n_NI_Local_GetX_PutX_1128s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_1128s N p== oneParamCons N  (n_NI_Local_GetX_PutX_1128 N p)"

definition n_NI_Local_GetX_PutX_1029s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_1029s N p== oneParamCons N  (n_NI_Local_GetX_PutX_1029 N p)"

definition n_NI_Local_GetX_PutX_10_Home30s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_10_Home30s N p== oneParamCons N  (n_NI_Local_GetX_PutX_10_Home30 N p)"

definition n_NI_Local_GetX_PutX_931s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_931s N p== oneParamCons N  (n_NI_Local_GetX_PutX_931 N p)"

definition n_NI_Local_GetX_PutX_932s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_932s N p== oneParamCons N  (n_NI_Local_GetX_PutX_932 N p)"

definition n_NI_Local_GetX_PutX_8_NODE_Get33s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_8_NODE_Get33s N p== oneParamCons N  (n_NI_Local_GetX_PutX_8_NODE_Get33 N p)"

definition n_NI_Local_GetX_PutX_834s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_834s N p== oneParamCons N  (n_NI_Local_GetX_PutX_834 N p)"

definition n_NI_Local_GetX_PutX_8_Home_NODE_Get35s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_8_Home_NODE_Get35s N p== oneParamCons N  (n_NI_Local_GetX_PutX_8_Home_NODE_Get35 N p)"

definition n_NI_Local_GetX_PutX_8_Home36s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_8_Home36s N p== oneParamCons N  (n_NI_Local_GetX_PutX_8_Home36 N p)"

definition n_NI_Local_GetX_PutX_7_NODE_Get37s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_7_NODE_Get37s N p == oneParamCons N  (n_NI_Local_GetX_PutX_7_NODE_Get37 N p)"

definition n_NI_Local_GetX_PutX_7_NODE_Get38s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_7_NODE_Get38s N p== oneParamCons N  (n_NI_Local_GetX_PutX_7_NODE_Get38 N p)"

definition n_NI_Local_GetX_PutX_739s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_739s N p== oneParamCons N  (n_NI_Local_GetX_PutX_739 N p)"

definition n_NI_Local_GetX_PutX_740s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_740s N p== oneParamCons N  (n_NI_Local_GetX_PutX_740 N p)"

definition n_NI_Local_GetX_PutX_641s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_641s N p== oneParamCons N  (n_NI_Local_GetX_PutX_641 N p)"

definition n_NI_Local_GetX_PutX_542s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_542s N p== oneParamCons N  (n_NI_Local_GetX_PutX_542 N p)"

definition n_NI_Local_GetX_PutX_443s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_443s N p== oneParamCons N  (n_NI_Local_GetX_PutX_443 N p)"

definition n_NI_Local_GetX_PutX_344s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_344s N p== oneParamCons N  (n_NI_Local_GetX_PutX_344 N p)"

definition n_NI_Local_GetX_PutX_245s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_245s N p== oneParamCons N  (n_NI_Local_GetX_PutX_245 N p)"

definition n_NI_Local_GetX_PutX_146s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_GetX_PutX_146s N p== oneParamCons N  (n_NI_Local_GetX_PutX_146 N p)"

definition n_NI_Local_GetX_GetX47s::" nat⇒rule set" where 
  "n_NI_Local_GetX_GetX47s N== oneParamCons N  n_NI_Local_GetX_GetX47"

definition n_NI_Local_GetX_GetX48s::" nat⇒rule set" where 
  "n_NI_Local_GetX_GetX48s N== oneParamCons N  n_NI_Local_GetX_GetX48"

definition n_NI_Local_GetX_Nak49s::" nat⇒rule set" where 
  "n_NI_Local_GetX_Nak49s N== oneParamCons N  n_NI_Local_GetX_Nak49"

definition n_NI_Local_GetX_Nak50s::" nat⇒rule set" where 
  "n_NI_Local_GetX_Nak50s N== oneParamCons N  n_NI_Local_GetX_Nak50"

definition n_NI_Local_GetX_Nak51s::" nat⇒rule set" where 
  "n_NI_Local_GetX_Nak51s N== oneParamCons N  n_NI_Local_GetX_Nak51"

definition n_NI_Remote_Get_Put_Home52s::" nat⇒rule set" where 
  "n_NI_Remote_Get_Put_Home52s N== oneParamCons N  n_NI_Remote_Get_Put_Home52"

definition n_NI_Remote_Get_Put53s::" nat⇒rule set" where 
  "n_NI_Remote_Get_Put53s N== oneParamCons N  n_NI_Remote_Get_Put53"

definition n_NI_Remote_Get_Nak_Home54s::" nat⇒rule set" where 
  "n_NI_Remote_Get_Nak_Home54s N== oneParamCons N  n_NI_Remote_Get_Nak_Home54"

definition n_NI_Remote_Get_Nak55s::" nat⇒rule set" where 
  "n_NI_Remote_Get_Nak55s N== oneParamCons N  n_NI_Remote_Get_Nak55"

definition n_NI_Local_Get_Put_Dirty56s::" nat⇒rule set" where 
  "n_NI_Local_Get_Put_Dirty56s N== oneParamCons N  n_NI_Local_Get_Put_Dirty56"

definition n_NI_Local_Get_Put57s::" nat⇒rule set" where 
  "n_NI_Local_Get_Put57s N== oneParamCons N  n_NI_Local_Get_Put57"

definition n_NI_Local_Get_Put_Head58s::" nat⇒ nat⇒rule set" where 
  "n_NI_Local_Get_Put_Head58s N p== oneParamCons N  (n_NI_Local_Get_Put_Head58 N p)"

definition n_NI_Local_Get_Get59s::" nat⇒rule set" where 
  "n_NI_Local_Get_Get59s N== oneParamCons N  n_NI_Local_Get_Get59"

definition n_NI_Local_Get_Get60s::" nat⇒rule set" where 
  "n_NI_Local_Get_Get60s N== oneParamCons N  n_NI_Local_Get_Get60"

definition n_NI_Local_Get_Nak61s::" nat⇒rule set" where 
  "n_NI_Local_Get_Nak61s N== oneParamCons N  n_NI_Local_Get_Nak61"

definition n_NI_Local_Get_Nak62s::" nat⇒rule set" where 
  "n_NI_Local_Get_Nak62s N== oneParamCons N  n_NI_Local_Get_Nak62"

definition n_NI_Local_Get_Nak63s::" nat⇒rule set" where 
  "n_NI_Local_Get_Nak63s N== oneParamCons N  n_NI_Local_Get_Nak63"

definition n_NI_Nak_Clear64s::" nat⇒rule set" where 
  "n_NI_Nak_Clear64s N== oneParamCons N  n_NI_Nak_Clear64"

definition n_NI_Nak_Home65s::" nat⇒rule set" where 
  "n_NI_Nak_Home65s N== oneParamCons N  n_NI_Nak_Home65"

definition n_NI_Nak66s::" nat⇒rule set" where 
  "n_NI_Nak66s N== oneParamCons N  n_NI_Nak66"

definition n_PI_Local_Replace67s::" nat⇒rule set" where 
  "n_PI_Local_Replace67s N== oneParamCons N  n_PI_Local_Replace67"

definition n_PI_Remote_Replace68s::" nat⇒rule set" where 
  "n_PI_Remote_Replace68s N== oneParamCons N  n_PI_Remote_Replace68"

definition n_PI_Local_PutX69s::" nat⇒rule set" where 
  "n_PI_Local_PutX69s N== oneParamCons N  n_PI_Local_PutX69"

definition n_PI_Local_PutX70s::" nat⇒rule set" where 
  "n_PI_Local_PutX70s N== oneParamCons N  n_PI_Local_PutX70"

definition n_PI_Remote_PutX71s::" nat⇒rule set" where 
  "n_PI_Remote_PutX71s N== oneParamCons N  n_PI_Remote_PutX71"

definition n_PI_Local_GetX_PutX_HeadVld7572s::" nat⇒ nat⇒rule set" where 
  "n_PI_Local_GetX_PutX_HeadVld7572s N p== oneParamCons N  (n_PI_Local_GetX_PutX_HeadVld7572 N p)"

definition n_PI_Local_GetX_PutX_HeadVld7473s::" nat⇒ nat⇒rule set" where 
  "n_PI_Local_GetX_PutX_HeadVld7473s N p== oneParamCons N  (n_PI_Local_GetX_PutX_HeadVld7473 N p)"

definition n_PI_Local_GetX_PutX7374s::" nat⇒rule set" where 
  "n_PI_Local_GetX_PutX7374s N== oneParamCons N  n_PI_Local_GetX_PutX7374"

definition n_PI_Local_GetX_PutX7275s::" nat⇒rule set" where 
  "n_PI_Local_GetX_PutX7275s N== oneParamCons N  n_PI_Local_GetX_PutX7275"

definition n_PI_Local_GetX_PutX_HeadVld76s::" nat⇒ nat⇒rule set" where 
  "n_PI_Local_GetX_PutX_HeadVld76s N p== oneParamCons N  (n_PI_Local_GetX_PutX_HeadVld76 N p)"

definition n_PI_Local_GetX_PutX_HeadVld77s::" nat⇒ nat⇒rule set" where 
  "n_PI_Local_GetX_PutX_HeadVld77s N p== oneParamCons N  (n_PI_Local_GetX_PutX_HeadVld77 N p)"

definition n_PI_Local_GetX_GetX78s::" nat⇒rule set" where 
  "n_PI_Local_GetX_GetX78s N== oneParamCons N  n_PI_Local_GetX_GetX78"

definition n_PI_Local_GetX_GetX79s::" nat⇒rule set" where 
  "n_PI_Local_GetX_GetX79s N== oneParamCons N  n_PI_Local_GetX_GetX79"

definition n_PI_Remote_GetX80s::" nat⇒rule set" where 
  "n_PI_Remote_GetX80s N== oneParamCons N  n_PI_Remote_GetX80"

definition n_PI_Local_Get_Put81s::" nat⇒rule set" where 
  "n_PI_Local_Get_Put81s N== oneParamCons N  n_PI_Local_Get_Put81"

definition n_PI_Local_Get_Put82s::" nat⇒rule set" where 
  "n_PI_Local_Get_Put82s N== oneParamCons N  n_PI_Local_Get_Put82"

definition n_PI_Local_Get_Get83s::" nat⇒rule set" where 
  "n_PI_Local_Get_Get83s N== oneParamCons N  n_PI_Local_Get_Get83"

definition n_PI_Remote_Get84s::" nat⇒rule set" where 
  "n_PI_Remote_Get84s N== oneParamCons N  n_PI_Remote_Get84"

definition n_Store_Home85s::" nat⇒rule set" where 
  "n_Store_Home85s N== oneParamCons N  n_Store_Home85"

definition n_Store86s::" nat⇒rule set" where 
  "n_Store86s N== oneParamCons N  n_Store86"

definition rules'::"nat ⇒ rule set" where [simp]:
"rules' N ≡  (n_NI_Replace_Home1s N) ∪
 (n_NI_Replace_Home2s N) ∪
 (n_NI_Replace3s N) ∪
 (n_NI_Replace4s N) ∪
 (n_NI_ShWb5s N) ∪
 (n_NI_ShWb6s N) ∪
 (n_NI_ShWb7s N) ∪
 (n_NI_FAck8s N) ∪
 (n_NI_FAck9s N) ∪
 (n_NI_Wb10s N) ∪
 (n_NI_InvAck_311s N) ∪
 (n_NI_InvAck_212s N) ∪
 (n_NI_InvAck_113s N) ∪
 (n_NI_InvAck_exists14s N) ∪
 (n_NI_InvAck_exists_Home15s N) ∪
 (n_NI_Inv16s N) ∪
 (n_NI_Inv17s N) ∪
 (n_NI_Remote_PutX18s N) ∪
 (n_NI_Local_PutXAcksDone19s N) ∪
 (n_NI_Remote_Put20s N) ∪
 (n_NI_Remote_Put21s N) ∪
 (n_NI_Local_Put22s N) ∪
 (n_NI_Local_Put23s N) ∪
 (n_NI_Remote_GetX_PutX_Home24s N) ∪
 (n_NI_Remote_GetX_PutX25s N) ∪
 (n_NI_Remote_GetX_Nak_Home26s N) ∪
 (n_NI_Remote_GetX_Nak27s N) ∪
 (n_NI_Local_GetX_PutX_1128s N) ∪
 (n_NI_Local_GetX_PutX_1029s N) ∪
 (n_NI_Local_GetX_PutX_10_Home30s N) ∪
 (n_NI_Local_GetX_PutX_931s N) ∪
 (n_NI_Local_GetX_PutX_932s N) ∪
 (n_NI_Local_GetX_PutX_8_NODE_Get33s N) ∪
 (n_NI_Local_GetX_PutX_834s N) ∪
 (n_NI_Local_GetX_PutX_8_Home_NODE_Get35s N) ∪
 (n_NI_Local_GetX_PutX_8_Home36s N) ∪
 (n_NI_Local_GetX_PutX_7_NODE_Get37s N) ∪
 (n_NI_Local_GetX_PutX_7_NODE_Get38s N) ∪
 (n_NI_Local_GetX_PutX_739s N) ∪
 (n_NI_Local_GetX_PutX_740s N) ∪
 (n_NI_Local_GetX_PutX_641s N) ∪
 (n_NI_Local_GetX_PutX_542s N) ∪
 (n_NI_Local_GetX_PutX_443s N) ∪
 (n_NI_Local_GetX_PutX_344s N) ∪
 (n_NI_Local_GetX_PutX_245s N) ∪
 (n_NI_Local_GetX_PutX_146s N) ∪
 (n_NI_Local_GetX_GetX47s N) ∪
 (n_NI_Local_GetX_GetX48s N) ∪
 (n_NI_Local_GetX_Nak49s N) ∪
 (n_NI_Local_GetX_Nak50s N) ∪
 (n_NI_Local_GetX_Nak51s N) ∪
 (n_NI_Remote_Get_Put_Home52s N) ∪
 (n_NI_Remote_Get_Put53s N) ∪
 (n_NI_Remote_Get_Nak_Home54s N) ∪
 (n_NI_Remote_Get_Nak55s N) ∪
 (n_NI_Local_Get_Put_Dirty56s N) ∪
 (n_NI_Local_Get_Put57s N) ∪
 (n_NI_Local_Get_Put_Head58s N) ∪
 (n_NI_Local_Get_Get59s N) ∪
 (n_NI_Local_Get_Get60s N) ∪
 (n_NI_Local_Get_Nak61s N) ∪
 (n_NI_Local_Get_Nak62s N) ∪
 (n_NI_Local_Get_Nak63s N) ∪
 (n_NI_Nak_Clear64s N) ∪
 (n_NI_Nak_Home65s N) ∪
 (n_NI_Nak66s N) ∪
 (n_PI_Local_Replace67s N) ∪
 (n_PI_Remote_Replace68s N) ∪
 (n_PI_Local_PutX69s N) ∪
 (n_PI_Local_PutX70s N) ∪
 (n_PI_Remote_PutX71s N) ∪
 (n_PI_Local_GetX_PutX_HeadVld7572s N) ∪
 (n_PI_Local_GetX_PutX_HeadVld7473s N) ∪
 (n_PI_Local_GetX_PutX7374s N) ∪
 (n_PI_Local_GetX_PutX7275s N) ∪
 (n_PI_Local_GetX_PutX_HeadVld76s N) ∪
 (n_PI_Local_GetX_PutX_HeadVld77s N) ∪
 (n_PI_Local_GetX_GetX78s N) ∪
 (n_PI_Local_GetX_GetX79s N) ∪
 (n_PI_Remote_GetX80s N) ∪
 (n_PI_Local_Get_Put81s N) ∪
 (n_PI_Local_Get_Put82s N) ∪
 (n_PI_Local_Get_Get83s N) ∪
 (n_PI_Remote_Get84s N) ∪
 (n_Store_Home85s N) ∪
 (n_Store86s N) 
"

lemma n_NI_Replace_Home1sIsSym:
  "symProtRules' N (n_NI_Replace_Home1s N)"
  using symNI_Replace_Home1(1) n_NI_Replace_Home1s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Replace_Home2sIsSym:
  "symProtRules' N (n_NI_Replace_Home2s N)"
  using symNI_Replace_Home2(1) n_NI_Replace_Home2s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Replace3sIsSym:
  "symProtRules' N (n_NI_Replace3s N)"
  using symNI_Replace3(1) n_NI_Replace3s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Replace4sIsSym:
  "symProtRules' N (n_NI_Replace4s N)"
  using symNI_Replace4(1) n_NI_Replace4s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_ShWb5sIsSym:
  "symProtRules' N (n_NI_ShWb5s N)"
  using symNI_ShWb5(1) n_NI_ShWb5s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_ShWb6sIsSym:
  "symProtRules' N (n_NI_ShWb6s N)"
  using symNI_ShWb6(1) n_NI_ShWb6s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_ShWb7sIsSym:
  "symProtRules' N (n_NI_ShWb7s N)"
  using symNI_ShWb7(1) n_NI_ShWb7s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_FAck8sIsSym:
  "symProtRules' N (n_NI_FAck8s N)"
  using symNI_FAck8(1) n_NI_FAck8s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_FAck9sIsSym:
  "symProtRules' N (n_NI_FAck9s N)"
  using symNI_FAck9(1) n_NI_FAck9s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Wb10sIsSym:
  "symProtRules' N (n_NI_Wb10s N)"
  using symNI_Wb10(1) n_NI_Wb10s_def symParaRuleInfSymRuleSet by auto

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

lemma n_NI_Local_PutXAcksDone19sIsSym:
  "symProtRules' N (n_NI_Local_PutXAcksDone19s N)"
  using symNI_Local_PutXAcksDone19(1) n_NI_Local_PutXAcksDone19s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_Put20sIsSym:
  "symProtRules' N (n_NI_Remote_Put20s N)"
  using symNI_Remote_Put20(1) n_NI_Remote_Put20s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Remote_Put21sIsSym:
  "symProtRules' N (n_NI_Remote_Put21s N)"
  using symNI_Remote_Put21(1) n_NI_Remote_Put21s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Put22sIsSym:
  "symProtRules' N (n_NI_Local_Put22s N)"
  using symNI_Local_Put22(1) n_NI_Local_Put22s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Local_Put23sIsSym:
  "symProtRules' N (n_NI_Local_Put23s N)"
  using symNI_Local_Put23(1) n_NI_Local_Put23s_def symParaRuleInfSymRuleSet by auto

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

lemma n_NI_Nak_Clear64sIsSym:
  "symProtRules' N (n_NI_Nak_Clear64s N)"
  using symNI_Nak_Clear64(1) n_NI_Nak_Clear64s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Nak_Home65sIsSym:
  "symProtRules' N (n_NI_Nak_Home65s N)"
  using symNI_Nak_Home65(1) n_NI_Nak_Home65s_def symParaRuleInfSymRuleSet by auto

lemma n_NI_Nak66sIsSym:
  "symProtRules' N (n_NI_Nak66s N)"
  using symNI_Nak66(1) n_NI_Nak66s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_Replace67sIsSym:
  "symProtRules' N (n_PI_Local_Replace67s N)"
  using symPI_Local_Replace67(1) n_PI_Local_Replace67s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_Replace68sIsSym:
  "symProtRules' N (n_PI_Remote_Replace68s N)"
  using symPI_Remote_Replace68(1) n_PI_Remote_Replace68s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_PutX69sIsSym:
  "symProtRules' N (n_PI_Local_PutX69s N)"
  using symPI_Local_PutX69(1) n_PI_Local_PutX69s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_PutX70sIsSym:
  "symProtRules' N (n_PI_Local_PutX70s N)"
  using symPI_Local_PutX70(1) n_PI_Local_PutX70s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_PutX71sIsSym:
  "symProtRules' N (n_PI_Remote_PutX71s N)"
  using symPI_Remote_PutX71(1) n_PI_Remote_PutX71s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_GetX_PutX_HeadVld7572sIsSym:
  "symProtRules' N (n_PI_Local_GetX_PutX_HeadVld7572s N)"
  using symPI_Local_GetX_PutX_HeadVld7572(1) n_PI_Local_GetX_PutX_HeadVld7572s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_GetX_PutX_HeadVld7473sIsSym:
  "symProtRules' N (n_PI_Local_GetX_PutX_HeadVld7473s N)"
  using symPI_Local_GetX_PutX_HeadVld7473(1) n_PI_Local_GetX_PutX_HeadVld7473s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_GetX_PutX7374sIsSym:
  "symProtRules' N (n_PI_Local_GetX_PutX7374s N)"
  using symPI_Local_GetX_PutX7374(1) n_PI_Local_GetX_PutX7374s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_GetX_PutX7275sIsSym:
  "symProtRules' N (n_PI_Local_GetX_PutX7275s N)"
  using symPI_Local_GetX_PutX7275(1) n_PI_Local_GetX_PutX7275s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_GetX_PutX_HeadVld76sIsSym:
  "symProtRules' N (n_PI_Local_GetX_PutX_HeadVld76s N)"
  using symPI_Local_GetX_PutX_HeadVld76(1) n_PI_Local_GetX_PutX_HeadVld76s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_GetX_PutX_HeadVld77sIsSym:
  "symProtRules' N (n_PI_Local_GetX_PutX_HeadVld77s N)"
  using symPI_Local_GetX_PutX_HeadVld77(1) n_PI_Local_GetX_PutX_HeadVld77s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_GetX_GetX78sIsSym:
  "symProtRules' N (n_PI_Local_GetX_GetX78s N)"
  using symPI_Local_GetX_GetX78(1) n_PI_Local_GetX_GetX78s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_GetX_GetX79sIsSym:
  "symProtRules' N (n_PI_Local_GetX_GetX79s N)"
  using symPI_Local_GetX_GetX79(1) n_PI_Local_GetX_GetX79s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Remote_GetX80sIsSym:
  "symProtRules' N (n_PI_Remote_GetX80s N)"
  using symPI_Remote_GetX80(1) n_PI_Remote_GetX80s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_Get_Put81sIsSym:
  "symProtRules' N (n_PI_Local_Get_Put81s N)"
  using symPI_Local_Get_Put81(1) n_PI_Local_Get_Put81s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_Get_Put82sIsSym:
  "symProtRules' N (n_PI_Local_Get_Put82s N)"
  using symPI_Local_Get_Put82(1) n_PI_Local_Get_Put82s_def symParaRuleInfSymRuleSet by auto

lemma n_PI_Local_Get_Get83sIsSym:
  "symProtRules' N (n_PI_Local_Get_Get83s N)"
  using symPI_Local_Get_Get83(1) n_PI_Local_Get_Get83s_def symParaRuleInfSymRuleSet by auto

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
  using n_NI_Replace_Home1sIsSym n_NI_Replace_Home2sIsSym n_NI_Replace3sIsSym n_NI_Replace4sIsSym n_NI_ShWb5sIsSym n_NI_ShWb6sIsSym n_NI_ShWb7sIsSym n_NI_FAck8sIsSym n_NI_FAck9sIsSym n_NI_Wb10sIsSym n_NI_InvAck_311sIsSym n_NI_InvAck_212sIsSym n_NI_InvAck_113sIsSym n_NI_InvAck_exists14sIsSym n_NI_InvAck_exists_Home15sIsSym n_NI_Inv16sIsSym n_NI_Inv17sIsSym n_NI_Remote_PutX18sIsSym n_NI_Local_PutXAcksDone19sIsSym n_NI_Remote_Put20sIsSym n_NI_Remote_Put21sIsSym n_NI_Local_Put22sIsSym n_NI_Local_Put23sIsSym n_NI_Remote_GetX_PutX_Home24sIsSym n_NI_Remote_GetX_PutX25sIsSym n_NI_Remote_GetX_Nak_Home26sIsSym n_NI_Remote_GetX_Nak27sIsSym n_NI_Local_GetX_PutX_1128sIsSym n_NI_Local_GetX_PutX_1029sIsSym n_NI_Local_GetX_PutX_10_Home30sIsSym n_NI_Local_GetX_PutX_931sIsSym n_NI_Local_GetX_PutX_932sIsSym n_NI_Local_GetX_PutX_8_NODE_Get33sIsSym n_NI_Local_GetX_PutX_834sIsSym n_NI_Local_GetX_PutX_8_Home_NODE_Get35sIsSym n_NI_Local_GetX_PutX_8_Home36sIsSym n_NI_Local_GetX_PutX_7_NODE_Get37sIsSym n_NI_Local_GetX_PutX_7_NODE_Get38sIsSym n_NI_Local_GetX_PutX_739sIsSym n_NI_Local_GetX_PutX_740sIsSym n_NI_Local_GetX_PutX_641sIsSym n_NI_Local_GetX_PutX_542sIsSym n_NI_Local_GetX_PutX_443sIsSym n_NI_Local_GetX_PutX_344sIsSym n_NI_Local_GetX_PutX_245sIsSym n_NI_Local_GetX_PutX_146sIsSym n_NI_Local_GetX_GetX47sIsSym n_NI_Local_GetX_GetX48sIsSym n_NI_Local_GetX_Nak49sIsSym n_NI_Local_GetX_Nak50sIsSym n_NI_Local_GetX_Nak51sIsSym n_NI_Remote_Get_Put_Home52sIsSym n_NI_Remote_Get_Put53sIsSym n_NI_Remote_Get_Nak_Home54sIsSym n_NI_Remote_Get_Nak55sIsSym n_NI_Local_Get_Put_Dirty56sIsSym n_NI_Local_Get_Put57sIsSym n_NI_Local_Get_Put_Head58sIsSym n_NI_Local_Get_Get59sIsSym n_NI_Local_Get_Get60sIsSym n_NI_Local_Get_Nak61sIsSym n_NI_Local_Get_Nak62sIsSym n_NI_Local_Get_Nak63sIsSym n_NI_Nak_Clear64sIsSym n_NI_Nak_Home65sIsSym n_NI_Nak66sIsSym n_PI_Local_Replace67sIsSym n_PI_Remote_Replace68sIsSym n_PI_Local_PutX69sIsSym n_PI_Local_PutX70sIsSym n_PI_Remote_PutX71sIsSym n_PI_Local_GetX_PutX_HeadVld7572sIsSym n_PI_Local_GetX_PutX_HeadVld7473sIsSym n_PI_Local_GetX_PutX7374sIsSym n_PI_Local_GetX_PutX7275sIsSym n_PI_Local_GetX_PutX_HeadVld76sIsSym n_PI_Local_GetX_PutX_HeadVld77sIsSym n_PI_Local_GetX_GetX78sIsSym n_PI_Local_GetX_GetX79sIsSym n_PI_Remote_GetX80sIsSym n_PI_Local_Get_Put81sIsSym n_PI_Local_Get_Put82sIsSym n_PI_Local_Get_Get83sIsSym n_PI_Remote_Get84sIsSym n_Store_Home85sIsSym n_Store86sIsSym rules'_def symProtRulesUnion by presburger 




subsection{*Definitions of each abstracted rule*}

definition  NC::"nat " where [simp]: "NC==1"

definition n_NI_InvAck_311_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_InvAck_311_abs_abs  j M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =⇩f (Const false)  ∧⇩f
(∀⇩fj. (IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false) ) M ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index j)) ) M ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_PutX)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1))) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const false)))"

definition n_NI_InvAck_212_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_InvAck_212_abs_abs  j M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =⇩f (Const false)  ∧⇩f
(∀⇩fj. (IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false) ) M ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const true)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index j)) ) M ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_PutX)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1))) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const false)))"

definition n_NI_InvAck_113_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_InvAck_113_abs_abs  j M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeInvSet''))  =⇩f (Const false)  ∧⇩f
(∀⇩fj. (IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false) ) M ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f (Const (index j)) ) M ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_PutX)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1))) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const false )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false)))"

definition n_NI_InvAck_exists14_abs_abs::"nat ⇒ rule" where [simp]:
"n_NI_InvAck_exists14_abs_abs  j≡
(IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.WbMsg.Cmd'')) =⇩f  (Const WB_Wb)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false) 

   ▹
(assign (Para (''Sta.InvMsg.Cmd'') j, (Const INV_None )))||
(assign (Para (''Sta.Dir.InvSet'') j, (Const false)))"

definition n_NI_Remote_GetX_PutX_Home24_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_GetX_PutX_Home24_abs_abs  j M≡
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =⇩f (Const UNI_GetX)  ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.WbMsg.Cmd'')) =⇩f  (Const WB_Wb)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_PutX) ) M ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv) 

   ▹
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_PutX)))"

definition n_NI_Remote_GetX_PutX25_1_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_GetX_PutX25_1_abs_abs  j M≡
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_GetX)  ∧⇩f
(IVar (Para (''Sta.UniMsg.Proc'') j)) =⇩f  (Const (index (M+1)))  ∧⇩f
(IVar (Para (''Sta.UniMsg.HomeProc'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index j))  ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_PutX)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.WbMsg.Cmd'')) =⇩f  (Const WB_Wb)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false) 

   ▹
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_PutX )))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_FAck )))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index j))))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_GetX_PutX25_2_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_GetX_PutX25_2_abs_abs  j M≡
(IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_Put)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_S)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(IVar (Para (''Sta.Proc.InvMarked'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.WbMsg.Cmd'')) =⇩f  (Const WB_Wb)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index (M+1))) 

   ▹
(assign (Para (''Sta.Proc.CacheState'') j, (Const CACHE_I )))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_FAck )))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_GetX_PutX25_12_abs_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_GetX_PutX25_12_abs_abs_abs  j M≡
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.WbMsg.Cmd'')) =⇩f  (Const WB_Wb)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f (Const (index j)) ) M ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_PutX)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_S) ) M ∧⇩f
(IVar (Para (''Sta.Proc.InvMarked'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_Put)  ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck) 

   ▹
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_FAck )))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_GetX_Nak_Home26_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_GetX_Nak_Home26_abs_abs  src M≡
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =⇩f (Const UNI_GetX)  ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =⇩f (Const false) 

   ▹
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Nak )))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_GetX_Nak27_1_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_GetX_Nak27_1_abs_abs  j M≡
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_GetX)  ∧⇩f
(IVar (Para (''Sta.UniMsg.Proc'') j)) =⇩f  (Const (index (M+1)))  ∧⇩f
(IVar (Para (''Sta.UniMsg.HomeProc'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f (Const (index j))  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false) 

   ▹
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_Nak )))||
(assign (Para (''Sta.UniMsg.Proc'') j, (IVar (Ident '' Other'') )))||
(assign (Para (''Sta.UniMsg.HomeProc'') j, (Const false )))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_GetX_Nak27_2_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_GetX_Nak27_2_abs_abs  j M≡
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_Put)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_S)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Para (''Sta.Proc.InvMarked'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index (M+1))) 

   ▹
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_GetX_Nak27_12_abs_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_GetX_Nak27_12_abs_abs_abs  M j≡
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index (M+1)))  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_Put) ) M ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_S)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Para (''Sta.Proc.InvMarked'') j)) =⇩f  (Const false) 

   ▹
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Local_GetX_PutX_1128_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_1128_abs_abs  p M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_E) 

   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
forallStm(λj. (assign (Para (''Sta.Dir.InvSet'') p, (Const false ))))M||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_1029_1_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_1029_1_abs_abs  p j M≡
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_GetX)  ∧⇩f
IVar (Ident ''
  Sta.UniMsg[j].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index j))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Proc'') j)) =⇩f  (Const (index (M+1))) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index j))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_PutX )))"

definition n_NI_Local_GetX_PutX_1029_2_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_1029_2_abs_abs  p M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.ShrSet[j] '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))"

definition n_NI_Local_GetX_PutX_1029_12_abs_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_1029_12_abs_abs_abs p j M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.UniMsg.Proc'') j)) =⇩f  (Const (index (M+1))) ) M

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))"

definition n_NI_Local_GetX_PutX_10_Home30_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_10_Home30_abs_abs  j M p≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HomeShrSet '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false) 
   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))"

definition n_NI_Local_GetX_PutX_931_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_931_abs_abs p M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))"

definition n_NI_Local_GetX_PutX_932_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_932_abs_abs  p M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None)))"

definition n_NI_Local_GetX_PutX_8_NODE_Get33_1_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_8_NODE_Get33_1_abs_abs  p M j≡
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_GetX)  ∧⇩f
IVar (Ident ''
  Sta.UniMsg[j].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index j))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.UniMsg.Proc'') j)) =⇩f  (Const (index j)) ) M

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index j))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_PutX )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I )))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_8_NODE_Get33_2_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_8_NODE_Get33_2_abs_abs  j M p≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.ShrSet[j] '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I )))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_8_NODE_Get33_12_abs_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_8_NODE_Get33_12_abs_abs_abs p j M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.UniMsg.Proc'') j)) =⇩f  (Const (index (M+1))) ) M

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I )))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_834_1_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_834_1_abs_abs  p M j≡
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_GetX)  ∧⇩f
IVar (Ident ''
  Sta.UniMsg[j].HomeProc '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index j))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.UniMsg.Proc'') j)) =⇩f  (Const (index j)) ) M

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (Const (index j))))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_PutX )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_834_2_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_834_2_abs_abs  j M p≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.ShrSet[j] '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_834_12_abs_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_834_12_abs_abs_abs p j M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.UniMsg.Proc'') j)) =⇩f  (Const (index (M+1))) ) M

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_8_Home_NODE_Get35_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_8_Home_NODE_Get35_abs_abs p j M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HomeShrSet '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I )))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_8_Home36_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_8_Home36_abs_abs p j M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HomeShrSet '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_7_NODE_Get37_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_7_NODE_Get37_abs_abs p j M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I )))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_7_NODE_Get38_abs_abs::"nat ⇒ nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_7_NODE_Get38_abs_abs p j M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I )))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_739_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_739_abs_abs  p M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_740_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_740_abs_abs  p M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''
  Sta.Dir.HeadVld '') =⇩f  (Const true) ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true )))||
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const true )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_Inv )))||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign (Para (''Sta.InvMsg.Cmd'') p, (Const INV_None )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeInvMsg.Cmd''), (Const INV_None )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_641_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_641_abs_abs  p M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
(∀⇩fj. (IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false) ) M

   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_542_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_542_abs_abs  p M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get)  ∧⇩f
(∀⇩fj. (IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false) ) M

   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_443_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_443_abs_abs  p M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadPtr''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeShrSet''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get)  ∧⇩f
(∀⇩fj. (IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false) ) M

   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I )))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_PutX_344_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_344_abs_abs  p M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false) 

   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_245_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_245_abs_abs  p M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.HomeProc.ProcCmd'')) =⇩f  (Const NODE_Get) 

   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I)))"

definition n_NI_Local_GetX_PutX_146_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_PutX_146_abs_abs  p M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.HomeProc.ProcCmd''))  =⇩f (Const NODE_Get) 

   ▹
(assign ((Ident ''Sta.Dir.Local''), (Const false )))||
(assign ((Ident ''Sta.Dir.Dirty''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.Dir.ShrVld''), (Const false )))||
forallStm(λj. (assign (Para (''Sta.Dir.ShrSet'') p, (Const false ))))M||
(assign (Para (''Sta.Dir.InvSet'') p, (Const false )))||
(assign ((Ident ''Sta.Dir.HomeShrSet''), (Const false )))||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const false )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_I )))||
(assign ((Ident ''Sta.HomeProc.InvMarked''), (Const true)))"

definition n_NI_Local_GetX_GetX47_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_GetX47_abs_abs  src M≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index (M+1))) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))"

definition n_NI_Local_GetX_GetX48_abs_abs::"nat ⇒ rule" where [simp]:
"n_NI_Local_GetX_GetX48_abs_abs  src≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const true) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))"

definition n_NI_Remote_Get_Put_Home52_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_Get_Put_Home52_abs_abs  j M≡
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =⇩f (Const UNI_Get)  ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.WbMsg.Cmd'')) =⇩f  (Const WB_Wb)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_PutX) ) M ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv) 

   ▹
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Put)))"

definition n_NI_Remote_Get_Put53_1_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_Get_Put53_1_abs_abs  j M≡
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_Get)  ∧⇩f
(IVar (Para (''Sta.UniMsg.Proc'') j)) =⇩f  (Const (index (M+1)))  ∧⇩f
(IVar (Para (''Sta.UniMsg.HomeProc'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f (Const (index j))  ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_PutX)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.WbMsg.Cmd'')) =⇩f  (Const WB_Wb)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false) 

   ▹
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_Put )))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_ShWb )))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (Const (index j))))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_Get_Put53_2_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_Get_Put53_2_abs_abs  j M≡
(IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_Put)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_S)  ∧⇩f
(IVar (Para (''Sta.Proc.InvMarked'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.WbMsg.Cmd'')) =⇩f  (Const WB_Wb)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index (M+1))) 

   ▹
(assign (Para (''Sta.Proc.CacheState'') j, (Const CACHE_S )))||
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_ShWb )))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false )))||
(assign ((Ident ''Sta.ShWbMsg.Data''), (IVar (Para (''Sta.Proc.CacheData'') j))))"

definition n_NI_Remote_Get_Put53_12_abs_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_Get_Put53_12_abs_abs_abs  j M≡
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.WbMsg.Cmd'')) =⇩f  (Const WB_Wb)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index (M+1))) ) M ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_PutX)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_S) ) M ∧⇩f
(IVar (Para (''Sta.Proc.InvMarked'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_Put)  ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck) 

   ▹
(assign ((Ident ''Sta.ShWbMsg.Cmd''), (Const SHWB_ShWb )))||
(assign ((Ident ''Sta.ShWbMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.ShWbMsg.HomeProc''), (Const false)))"

definition n_NI_Remote_Get_Nak_Home54_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_Get_Nak_Home54_abs_abs  M dst≡
(IVar (Ident ''Sta.HomeUniMsg.Cmd''))  =⇩f (Const UNI_Get)  ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.Proc''))  =⇩f (Const (index (M+1)))  ∧⇩f
(IVar (Ident ''Sta.HomeUniMsg.HomeProc''))  =⇩f (Const false) 

   ▹
(assign ((Ident ''Sta.HomeUniMsg.Cmd''), (Const UNI_Nak )))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_Get_Nak55_1_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_Get_Nak55_1_abs_abs  j M≡
(IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_Get)  ∧⇩f
(IVar (Para (''Sta.UniMsg.Proc'') j)) =⇩f  (Const (index (M+1)))  ∧⇩f
(IVar (Para (''Sta.UniMsg.HomeProc'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index j))  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false) 

   ▹
(assign (Para (''Sta.UniMsg.Cmd'') j, (Const UNI_Nak )))||
(assign (Para (''Sta.UniMsg.Proc'') j, (IVar (Ident '' Other'') )))||
(assign (Para (''Sta.UniMsg.HomeProc'') j, (Const false )))||
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_Get_Nak55_2_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_Get_Nak55_2_abs_abs  j M≡
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_Put)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_S)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Para (''Sta.Proc.InvMarked'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index (M+1))) 

   ▹
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Remote_Get_Nak55_12_abs_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Remote_Get_Nak55_12_abs_abs_abs  M j≡
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_FAck)  ∧⇩f
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.NakcMsg.Cmd'')) =⇩f  (Const NAKC_Nakc)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index (M+1)))  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_Put) ) M ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_S)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Para (''Sta.Proc.InvMarked'') j)) =⇩f  (Const false) 

   ▹
(assign ((Ident ''Sta.NakcMsg.Cmd''), (Const NAKC_Nakc)))"

definition n_NI_Local_Get_Put_Dirty56_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_Get_Put_Dirty56_abs_abs  src dst≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.HomeProc.CacheState''))  =⇩f (Const CACHE_E) 

   ▹
(assign ((Ident ''Sta.Dir.Dirty''), (Const false )))||
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false )))||
(assign ((Ident ''Sta.HomeProc.CacheState''), (Const CACHE_S)))"

definition n_NI_Local_Get_Put57_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_Get_Put57_abs_abs  src dst≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const false) 

   ▹
(assign ((Ident ''Sta.Dir.HeadVld''), (Const true )))||
(assign ((Ident ''Sta.Dir.HeadPtr''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.Dir.HomeHeadPtr''), (Const false)))"

definition n_NI_Local_Get_Put_Head58_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_Get_Put_Head58_abs_abs  src dst≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const false)  ∧⇩f
IVar (Ident ''Sta.Dir.HeadVld'') =⇩f  (Const true)

   ▹
(assign ((Ident ''Sta.Dir.ShrVld''), (Const true )))||
forallStm(λj. (assign (Para (''Sta.Dir.InvSet'') p, (IVar (Para (''Sta.Dir.ShrSet'') p)))))M||
(assign ((Ident ''Sta.Dir.HomeInvSet''), (Const Sta.Dir.HomeShrSet)))"

definition n_NI_Local_Get_Get59_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_NI_Local_Get_Get59_abs_abs  M dst≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.Dir.HeadPtr'')) =⇩f  (Const (index (M+1))) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))"

definition n_NI_Local_Get_Get60_abs_abs::"nat ⇒ rule" where [simp]:
"n_NI_Local_Get_Get60_abs_abs  src≡
(IVar (Ident ''Sta.Dir.Pending''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.HomeHeadPtr''))  =⇩f (Const true) 

   ▹
(assign ((Ident ''Sta.Dir.Pending''), (Const true)))"

definition n_PI_Remote_PutX71_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_PI_Remote_PutX71_abs_abs  j M≡
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.WbMsg.Cmd'')) =⇩f  (Const WB_Wb)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_PutX) ) M ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv) 

   ▹
(assign ((Ident ''Sta.WbMsg.Cmd''), (Const WB_Wb )))||
(assign ((Ident ''Sta.WbMsg.Proc''), (IVar (Ident '' Other'') )))||
(assign ((Ident ''Sta.WbMsg.HomeProc''), (Const false)))"

definition n_Store86_abs_abs::"nat ⇒ nat ⇒ rule" where [simp]:
"n_Store86_abs_abs  j M≡
¬⇩f (IVar (Ident ''Sta.ShWbMsg.Cmd'')) =⇩f  (Const SHWB_ShWb)  ∧⇩f
(IVar (Ident ''Sta.Dir.Local''))  =⇩f (Const false)  ∧⇩f
(IVar (Ident ''Sta.Dir.Dirty''))  =⇩f (Const true)  ∧⇩f
(IVar (Ident ''Sta.Dir.HeadVld''))  =⇩f (Const true)  ∧⇩f
¬⇩f (IVar (Ident ''Sta.WbMsg.Cmd'')) =⇩f  (Const WB_Wb)  ∧⇩f
(IVar (Ident ''Sta.Dir.ShrVld''))  =⇩f (Const false)  ∧⇩f
(∀⇩fj. ¬⇩f (IVar (Para (''Sta.UniMsg.Cmd'') j)) =⇩f  (Const UNI_PutX) ) M ∧⇩f
(IVar (Para (''Sta.Dir.ShrSet'') j)) =⇩f  (Const false)  ∧⇩f
(IVar (Para (''Sta.Dir.InvSet'') j)) =⇩f  (Const false)  ∧⇩f
¬⇩f (IVar (Para (''Sta.Proc.CacheState'') j)) =⇩f  (Const CACHE_E)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_InvAck)  ∧⇩f
¬⇩f (IVar (Para (''Sta.InvMsg.Cmd'') j)) =⇩f  (Const INV_Inv) 

   ▹
(assign ((Ident ''Sta.CurrData''), (IVar (Ident ''['DATA_1']''))))"

