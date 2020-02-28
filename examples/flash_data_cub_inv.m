ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__1"
    ((Sta.Proc[p__Inv4].CacheState = CACHE_E) & (Sta.Proc[p__Inv3].CacheState = CACHE_E));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__2"
    ((Sta.Proc[p__Inv4].CacheState = CACHE_E) & (Sta.HomeProc.CacheState = CACHE_E));
endruleset;
invariant "inv__3"
  ((Sta.Dir.Dirty = false) & (!(Sta.MemData = Sta.CurrData)));
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__4"
    ((Sta.Proc[p__Inv4].CacheState = CACHE_E) & (Sta.UniMsg[p__Inv3].Cmd = UNI_PutX));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__5"
    ((Sta.HomeProc.CacheState = CACHE_E) & (Sta.UniMsg[p__Inv4].Cmd = UNI_PutX));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__6"
    ((Sta.Proc[p__Inv4].CacheState = CACHE_E) & (Sta.Dir.Dirty = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__7"
    ((Sta.Proc[p__Inv4].CacheState = CACHE_E) & (Sta.HomeUniMsg.Cmd = UNI_PutX));
endruleset;
invariant "inv__8"
  ((Sta.Dir.Dirty = false) & (Sta.HomeProc.CacheState = CACHE_E));
invariant "inv__9"
  ((!(Sta.HomeProc.CacheData = Sta.CurrData)) & (Sta.Dir.Local = true));
invariant "inv__10"
  ((!(Sta.HomeProc.CacheData = Sta.CurrData)) & (Sta.HomeProc.CacheState = CACHE_E));
invariant "inv__11"
  ((!(Sta.HomeUniMsg.Data = Sta.CurrData)) & (Sta.HomeUniMsg.Cmd = UNI_Put));
invariant "inv__12"
  ((!(Sta.WbMsg.Data = Sta.CurrData)) & (Sta.WbMsg.Cmd = WB_Wb));
invariant "inv__13"
  ((!(Sta.ShWbMsg.Data = Sta.CurrData)) & (Sta.ShWbMsg.Cmd = SHWB_ShWb));
invariant "inv__14"
  ((Sta.Dir.HomeShrSet = true));
ruleset p__Inv4 : NODE do
  invariant "inv__15"
    ((Sta.Proc[p__Inv4].CacheState = CACHE_E) & (Sta.Dir.Local = true));
endruleset;
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__16"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_PutX) & (Sta.UniMsg[p__Inv3].Cmd = UNI_PutX));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__17"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_PutX) & (Sta.Dir.Dirty = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__18"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_PutX) & (Sta.HomeUniMsg.Cmd = UNI_PutX));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__19"
    ((Sta.Proc[p__Inv4].CacheState = CACHE_E) & (Sta.HomeUniMsg.Cmd = UNI_Put));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__20"
    ((Sta.Proc[p__Inv4].CacheState = CACHE_E) & (Sta.WbMsg.Cmd = WB_Wb));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__21"
    ((Sta.Proc[p__Inv4].CacheState = CACHE_E) & (Sta.ShWbMsg.Cmd = SHWB_ShWb));
endruleset;
invariant "inv__22"
  ((!(Sta.HomeUniMsg.Data = Sta.CurrData)) & (Sta.HomeUniMsg.Cmd = UNI_PutX));
invariant "inv__23"
  ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.HomeProc.CacheState = CACHE_E));
ruleset p__Inv4 : NODE do
  invariant "inv__24"
    ((!(Sta.Proc[p__Inv4].CacheData = Sta.CurrData)) & (Sta.Proc[p__Inv4].CacheState = CACHE_E));
endruleset;
invariant "inv__25"
  ((Sta.WbMsg.Cmd = WB_Wb) & (Sta.HomeProc.CacheState = CACHE_E));
invariant "inv__26"
  ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.HomeProc.CacheState = CACHE_E));
invariant "inv__27"
  ((Sta.Dir.Dirty = false) & (Sta.HomeUniMsg.Cmd = UNI_PutX));
invariant "inv__28"
  ((Sta.HomeProc.InvMarked = true));
invariant "inv__29"
  ((Sta.ShWbMsg.HomeProc = true) & (Sta.ShWbMsg.Cmd = SHWB_ShWb));
ruleset p__Inv4 : NODE do
  invariant "inv__30"
    ((Sta.Dir.Local = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_PutX));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__31"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_PutX) & (Sta.Proc[p__Inv4].CacheState = CACHE_E));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__32"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_PutX) & (Sta.HomeUniMsg.Cmd = UNI_Put));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__33"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_PutX) & (Sta.WbMsg.Cmd = WB_Wb));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__34"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_PutX) & (Sta.ShWbMsg.Cmd = SHWB_ShWb));
endruleset;
invariant "inv__35"
  ((Sta.HomeUniMsg.Cmd = UNI_PutX) & (Sta.Dir.Local = true));
invariant "inv__36"
  ((Sta.HomeUniMsg.Cmd = UNI_PutX) & (Sta.HomeProc.CacheState = CACHE_E));
invariant "inv__37"
  ((Sta.HomeProc.CacheState = CACHE_E) & (Sta.HomeUniMsg.Cmd = UNI_Get));
invariant "inv__38"
  ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.Dir.Dirty = false));
ruleset p__Inv4 : NODE do
  invariant "inv__39"
    ((!(Sta.UniMsg[p__Inv4].Data = Sta.CurrData)) & (Sta.UniMsg[p__Inv4].Cmd = UNI_PutX));
endruleset;
invariant "inv__40"
  ((Sta.WbMsg.Cmd = WB_Wb) & (Sta.Dir.Dirty = false));
invariant "inv__41"
  ((Sta.WbMsg.Cmd = WB_Wb) & (Sta.HomeUniMsg.Cmd = UNI_PutX));
invariant "inv__42"
  ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.Dir.Dirty = false));
invariant "inv__43"
  ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.HomeUniMsg.Cmd = UNI_PutX));
invariant "inv__44"
  ((Sta.HomeUniMsg.Cmd = UNI_PutX) & (Sta.Dir.Pending = false));
invariant "inv__45"
  ((Sta.Dir.Local = true) & (Sta.HomeProc.ProcCmd = NODE_Get));
invariant "inv__46"
  ((Sta.Dir.HeadVld = true) & (Sta.Dir.HomeHeadPtr = true));
invariant "inv__47"
  ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.Dir.Local = true));
invariant "inv__48"
  ((Sta.WbMsg.Cmd = WB_Wb) & (Sta.Dir.Local = true));
invariant "inv__49"
  ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.Dir.Local = true));
invariant "inv__50"
  ((Sta.Dir.Local = true) & (Sta.HomeUniMsg.Cmd = UNI_GetX));
invariant "inv__51"
  ((Sta.HomeProc.CacheState = CACHE_E) & (Sta.HomeUniMsg.Cmd = UNI_GetX));
invariant "inv__52"
  ((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.Dir.Pending = false));
invariant "inv__53"
  ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.Dir.Pending = false));
invariant "inv__54"
  ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.WbMsg.Cmd = WB_Wb));
invariant "inv__55"
  ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.ShWbMsg.Cmd = SHWB_ShWb));
invariant "inv__56"
  ((Sta.WbMsg.Cmd = WB_Wb) & (Sta.ShWbMsg.Cmd = SHWB_ShWb));
invariant "inv__57"
  ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.Dir.Pending = false));
invariant "inv__58"
  ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.HomeUniMsg.Cmd = UNI_GetX));
invariant "inv__59"
  ((Sta.Dir.Pending = false) & (Sta.HomeUniMsg.Cmd = UNI_GetX));
ruleset p__Inv4 : NODE do
  invariant "inv__60"
    ((Sta.HomeUniMsg.Cmd = UNI_PutX) & (Sta.Dir.InvSet[p__Inv4] = true));
endruleset;
invariant "inv__61"
  ((Sta.HomeUniMsg.Cmd = UNI_PutX) & (Sta.NakcMsg.Cmd = NAKC_Nakc));
invariant "inv__62"
  ((Sta.HomeUniMsg.Cmd = UNI_PutX) & (Sta.ShWbMsg.Cmd = SHWB_FAck));
invariant "inv__63"
  ((Sta.Dir.Local = true) & (Sta.Dir.Dirty = true) & (Sta.HomeProc.CacheState = CACHE_I));
invariant "inv__64"
  ((Sta.ShWbMsg.HomeProc = true) & (Sta.ShWbMsg.Cmd = SHWB_FAck));
invariant "inv__65"
  ((Sta.Dir.Local = true) & (Sta.HomeUniMsg.Cmd = UNI_Get));
invariant "inv__66"
  ((Sta.Dir.Dirty = true) & (Sta.HomeProc.CacheState = CACHE_S));
ruleset p__Inv4 : NODE do
  invariant "inv__67"
    ((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.Dir.InvSet[p__Inv4] = true));
endruleset;
invariant "inv__68"
  ((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.NakcMsg.Cmd = NAKC_Nakc));
invariant "inv__69"
  ((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.ShWbMsg.Cmd = SHWB_FAck));
invariant "inv__70"
  ((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.ShWbMsg.Cmd = SHWB_ShWb));
ruleset p__Inv4 : NODE do
  invariant "inv__71"
    ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.Dir.InvSet[p__Inv4] = true));
endruleset;
invariant "inv__72"
  ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.NakcMsg.Cmd = NAKC_Nakc));
invariant "inv__73"
  ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.ShWbMsg.Cmd = SHWB_FAck));
ruleset p__Inv4 : NODE do
  invariant "inv__74"
    ((Sta.Dir.Pending = false) & (Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__75"
    ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.Dir.InvSet[p__Inv4] = true));
endruleset;
invariant "inv__76"
  ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.NakcMsg.Cmd = NAKC_Nakc));
ruleset p__Inv4 : NODE do
  invariant "inv__77"
    ((Sta.HomeUniMsg.Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__78"
    ((Sta.HomeUniMsg.Cmd = UNI_GetX) & (Sta.Dir.InvSet[p__Inv4] = true));
endruleset;
invariant "inv__79"
  ((Sta.HomeUniMsg.Cmd = UNI_GetX) & (Sta.NakcMsg.Cmd = NAKC_Nakc));
invariant "inv__80"
  ((Sta.HomeUniMsg.Cmd = UNI_GetX) & (Sta.ShWbMsg.Cmd = SHWB_FAck));
ruleset p__Inv4 : NODE do
  invariant "inv__81"
    ((Sta.HomeUniMsg.Cmd = UNI_PutX) & (Sta.Dir.ShrSet[p__Inv4] = true));
endruleset;
invariant "inv__82"
  ((Sta.HomeUniMsg.Cmd = UNI_PutX) & (Sta.Dir.ShrVld = true));
ruleset p__Inv4 : NODE do
  invariant "inv__83"
    ((Sta.HomeUniMsg.Cmd = UNI_PutX) & (Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__84"
    ((Sta.HomeUniMsg.Cmd = UNI_PutX) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
invariant "inv__85"
  ((Sta.HomeProc.CacheState = CACHE_S) & (Sta.Dir.Local = false));
ruleset p__Inv4 : NODE do
  invariant "inv__86"
    ((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.Dir.ShrSet[p__Inv4] = true));
endruleset;
invariant "inv__87"
  ((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.Dir.ShrVld = true));
ruleset p__Inv4 : NODE do
  invariant "inv__88"
    ((Sta.Dir.InvSet[p__Inv4] = true) & (Sta.Dir.Dirty = true) & (Sta.Dir.Pending = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__89"
    ((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__90"
    ((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
invariant "inv__91"
  ((Sta.NakcMsg.Cmd = NAKC_Nakc) & (Sta.Dir.Pending = false));
invariant "inv__92"
  ((Sta.ShWbMsg.Cmd = SHWB_FAck) & (Sta.Dir.Pending = false));
ruleset p__Inv4 : NODE do
  invariant "inv__93"
    ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.Dir.ShrSet[p__Inv4] = true));
endruleset;
invariant "inv__94"
  ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.Dir.ShrVld = true));
ruleset p__Inv4 : NODE do
  invariant "inv__95"
    ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__96"
    ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__97"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.Dir.InvSet[p__Inv4] = true));
endruleset;
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__98"
    ((Sta.UniMsg[p__Inv3].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv3].HomeProc = false) & (Sta.Dir.InvSet[p__Inv4] = true));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__99"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.NakcMsg.Cmd = NAKC_Nakc));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__100"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.ShWbMsg.Cmd = SHWB_FAck));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__101"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.ShWbMsg.Cmd = SHWB_ShWb));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__102"
    ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.Dir.ShrSet[p__Inv4] = true));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__103"
    ((Sta.Dir.InvSet[p__Inv4] = true) & (Sta.Proc[p__Inv4].CacheState = CACHE_E));
endruleset;
invariant "inv__104"
  ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.Dir.ShrVld = true));
ruleset p__Inv4 : NODE do
  invariant "inv__105"
    ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__106"
    ((Sta.HomeUniMsg.Cmd = UNI_GetX) & (Sta.Dir.ShrSet[p__Inv4] = true));
endruleset;
invariant "inv__107"
  ((Sta.HomeUniMsg.Cmd = UNI_GetX) & (Sta.Dir.ShrVld = true));
ruleset p__Inv4 : NODE do
  invariant "inv__108"
    ((Sta.HomeUniMsg.Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__109"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.Proc[p__Inv4].CacheState = CACHE_E));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__110"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.Proc[p__Inv4].CacheState = CACHE_E));
endruleset;
invariant "inv__111"
  ((Sta.HomeProc.CacheState = CACHE_S) & (Sta.Dir.Pending = true));
ruleset p__Inv4 : NODE do
  invariant "inv__112"
    ((Sta.Dir.ShrSet[p__Inv4] = true) & (Sta.Dir.Dirty = true));
endruleset;
invariant "inv__113"
  ((Sta.Dir.ShrVld = true) & (Sta.Dir.Dirty = true));
ruleset p__Inv4 : NODE do
  invariant "inv__114"
    ((Sta.Dir.InvSet[p__Inv4] = true) & (Sta.Dir.Pending = false) & (Sta.Dir.HeadVld = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__115"
    ((Sta.Dir.InvSet[p__Inv4] = true) & (Sta.NakcMsg.Cmd = NAKC_Nakc));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__116"
    ((Sta.Dir.InvSet[p__Inv4] = true) & (Sta.ShWbMsg.Cmd = SHWB_FAck));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__117"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.Dir.Pending = false));
endruleset;
invariant "inv__118"
  ((Sta.NakcMsg.Cmd = NAKC_Nakc) & (Sta.ShWbMsg.Cmd = SHWB_FAck));
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__119"
    ((Sta.UniMsg[p__Inv3].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv3].HomeProc = false) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__120"
    ((Sta.UniMsg[p__Inv3].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv3].HomeProc = false) & (Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__121"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.Dir.ShrSet[p__Inv4] = true));
endruleset;
invariant "inv__122"
  ((Sta.Dir.ShrVld = true) & (Sta.Dir.HomeHeadPtr = true));
ruleset p__Inv4 : NODE do
  invariant "inv__123"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.Dir.ShrVld = true));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__124"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.Dir.HeadPtr = p__Inv4));
endruleset;
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__125"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.Dir.ShrSet[p__Inv3] = true));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__126"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.Dir.Local = true));
endruleset;
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__127"
    ((Sta.Dir.ShrSet[p__Inv3] = true) & (Sta.Proc[p__Inv4].CacheState = CACHE_E));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__128"
    ((Sta.Dir.ShrSet[p__Inv4] = true) & (Sta.Proc[p__Inv4].CacheState = CACHE_E));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__129"
    ((Sta.Proc[p__Inv4].CacheState = CACHE_E) & (Sta.Dir.ShrVld = true));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__130"
    ((Sta.Dir.InvSet[p__Inv4] = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_PutX));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__131"
    ((Sta.Proc[p__Inv4].CacheState = CACHE_E) & (Sta.Dir.HomeHeadPtr = true));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__132"
    ((Sta.Dir.ShrSet[p__Inv4] = true) & (Sta.Dir.HeadVld = false));
endruleset;
invariant "inv__133"
  ((Sta.Dir.ShrVld = true) & (Sta.Dir.HeadVld = false));
ruleset p__Inv4 : NODE do
  invariant "inv__134"
    ((Sta.Dir.InvSet[p__Inv4] = true) & (Sta.Dir.Pending = false) & (Sta.WbMsg.Cmd = WB_Wb));
endruleset;
invariant "inv__135"
  ((Sta.Dir.HeadVld = false) & (Sta.ShWbMsg.Cmd = SHWB_ShWb));
ruleset p__Inv4 : NODE do
  invariant "inv__136"
    ((Sta.Dir.ShrSet[p__Inv4] = true) & (Sta.NakcMsg.Cmd = NAKC_Nakc));
endruleset;
invariant "inv__137"
  ((Sta.NakcMsg.Cmd = NAKC_Nakc) & (Sta.Dir.ShrVld = true));
invariant "inv__138"
  ((Sta.NakcMsg.Cmd = NAKC_Nakc) & (Sta.Dir.Local = true));
ruleset p__Inv4 : NODE do
  invariant "inv__139"
    ((Sta.Dir.InvSet[p__Inv4] = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__140"
    ((Sta.Dir.InvSet[p__Inv3] = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__141"
    ((Sta.Dir.ShrSet[p__Inv4] = true) & (Sta.ShWbMsg.Cmd = SHWB_FAck));
endruleset;
invariant "inv__142"
  ((Sta.ShWbMsg.Cmd = SHWB_FAck) & (Sta.Dir.ShrVld = true));
invariant "inv__143"
  ((Sta.ShWbMsg.Cmd = SHWB_FAck) & (Sta.Dir.Local = true));
ruleset p__Inv4 : NODE do
  invariant "inv__144"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.NakcMsg.Cmd = NAKC_Nakc));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__145"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.ShWbMsg.Cmd = SHWB_FAck));
endruleset;
invariant "inv__146"
  ((Sta.Dir.HomeHeadPtr = true) & (Sta.ShWbMsg.Cmd = SHWB_ShWb));
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__147"
    ((Sta.Dir.ShrSet[p__Inv4] = true) & (Sta.UniMsg[p__Inv3].Cmd = UNI_PutX));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__148"
    ((Sta.Dir.ShrSet[p__Inv4] = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_PutX));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__149"
    ((Sta.Dir.ShrVld = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_PutX));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__150"
    ((Sta.Dir.HomeHeadPtr = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_PutX));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__151"
    ((Sta.Dir.ShrSet[p__Inv4] = true) & (Sta.WbMsg.Cmd = WB_Wb));
endruleset;
invariant "inv__152"
  ((Sta.Dir.ShrVld = true) & (Sta.WbMsg.Cmd = WB_Wb));
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__153"
    ((Sta.Dir.InvSet[p__Inv3] = true) & (Sta.Dir.Pending = false) & (Sta.Proc[p__Inv4].CacheState = CACHE_E));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__154"
    ((Sta.Dir.HeadVld = false) & (Sta.Proc[p__Inv4].CacheState = CACHE_E));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__155"
    ((Sta.Dir.ShrSet[p__Inv4] = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__156"
    ((Sta.Dir.ShrSet[p__Inv3] = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__157"
    ((Sta.Dir.ShrVld = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__158"
    ((Sta.Dir.Local = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__159"
    ((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false) & (Sta.Dir.HeadPtr = p__Inv4));
endruleset;
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__160"
    ((Sta.UniMsg[p__Inv3].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv3].HomeProc = false) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false));
endruleset;
ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv__161"
    ((Sta.Dir.InvSet[p__Inv4] = true) & (Sta.Dir.Pending = false) & (Sta.UniMsg[p__Inv3].Cmd = UNI_PutX));
endruleset;
ruleset p__Inv4 : NODE do
  invariant "inv__162"
    ((Sta.Dir.HeadVld = false) & (Sta.UniMsg[p__Inv4].Cmd = UNI_PutX));
endruleset;

