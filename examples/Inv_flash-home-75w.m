



ruleset  i : NODE do
invariant "1"
Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState = CACHE_I;
endruleset;




ruleset  i : NODE do
invariant "2"
Sta.Dir.HomeHeadPtr = true -> Sta.UniMsg[i].Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "3"
i != j -> 
  (Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.InvSet[j] = false);

endruleset;




ruleset do
invariant "4"
Sta.Dir.Local = false -> Sta.HomeProc.CacheState = CACHE_I;
endruleset;




ruleset do
invariant "5"
Sta.HomeProc.CacheState = CACHE_E -> Sta.Dir.Local = true;
endruleset;




ruleset  j : NODE do
invariant "6"
Sta.Dir.ShrSet[j] = true -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset do
invariant "7"
Sta.Dir.HomeInvSet = false -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  j : NODE do
invariant "8"
Sta.Dir.Local = false & Sta.Dir.InvSet[j] = true -> Sta.Dir.Pending = false;
endruleset;




ruleset do
invariant "9"
Sta.HomeProc.CacheState = CACHE_E -> Sta.Dir.HeadVld = false;
endruleset;




ruleset  j : NODE do
invariant "10"
Sta.Dir.ShrSet[j] = true -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset  j : NODE do
invariant "11"
Sta.Dir.HomeHeadPtr = true -> Sta.Proc[j].CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "12"
Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_Put;
endruleset;




ruleset do
invariant "13"
Sta.Dir.HomeHeadPtr = true -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset  j : NODE do
invariant "14"
Sta.Dir.InvSet[j] = true & Sta.Dir.Dirty = true -> Sta.HomeProc.ProcCmd = NODE_None;
endruleset;




ruleset  i : NODE do
invariant "15"
Sta.Dir.HomeHeadPtr = true -> Sta.InvMsg[i].Cmd != INV_Inv;
endruleset;




ruleset  i : NODE do
invariant "16"
Sta.Dir.HeadVld = false -> Sta.Proc[i].CacheState != CACHE_E;
endruleset;




ruleset  i : NODE do
invariant "17"
Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "18"
Sta.Dir.InvSet[i] = true & Sta.Dir.Dirty = true -> Sta.HomeProc.CacheState != CACHE_I;
endruleset;




ruleset  i : NODE do
invariant "19"
Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd != NODE_None;
endruleset;




ruleset  i : NODE do
invariant "20"
Sta.Dir.Pending = true & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HeadPtr = i;
endruleset;




ruleset do
invariant "21"
Sta.HomeProc.CacheState = CACHE_E -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset  j : NODE do
invariant "22"
Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE do
invariant "23"
Sta.UniMsg[i].HomeProc = true -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "24"
Sta.Dir.Dirty = false & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.InvSet[j] = true;
endruleset;




ruleset do
invariant "25"
Sta.Dir.HeadVld = false -> Sta.Dir.ShrVld = false;
endruleset;




ruleset do
invariant "26"
Sta.Dir.HomeHeadPtr = true & Sta.Dir.Dirty = true -> Sta.HomeProc.CacheState = CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "27"
Sta.Dir.InvSet[j] = true -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset  i : NODE do
invariant "28"
Sta.Dir.InvSet[i] = true & Sta.Dir.Dirty = true -> Sta.Dir.Local = true;
endruleset;




ruleset  i : NODE do
invariant "29"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].CacheData = Sta.CurrData;
endruleset;




ruleset  j : NODE do
invariant "30"
Sta.UniMsg[j].HomeProc = true -> Sta.Proc[j].CacheState != CACHE_E;
endruleset;




ruleset do
invariant "31"
Sta.Dir.Local = true -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset  j : NODE do
invariant "32"
Sta.Proc[j].CacheState = CACHE_E -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset do
invariant "33"
Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true -> Sta.Dir.Pending = false;
endruleset;




ruleset  i : NODE do
invariant "34"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrVld = false;
endruleset;




ruleset  i : NODE do
invariant "35"
Sta.Dir.HomeHeadPtr = true -> Sta.UniMsg[i].Cmd != UNI_Nak;
endruleset;




ruleset  i : NODE do
invariant "36"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "37"
Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE do
invariant "38"
Sta.Proc[i].CacheState = CACHE_E -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset do
invariant "39"
Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.Dir.Pending = false;
endruleset;




ruleset  j : NODE do
invariant "40"
Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset do
invariant "41"
Sta.HomeProc.ProcCmd != NODE_Get -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  j : NODE do
invariant "42"
Sta.Proc[j].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset  j : NODE do
invariant "43"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "44"
i != j -> 
  (Sta.UniMsg[j].Cmd = UNI_GetX & Sta.Proc[i].CacheState = CACHE_E -> Sta.InvMsg[j].Cmd != INV_Inv);

endruleset;




ruleset  j : NODE do
invariant "45"
Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "46"
Sta.Proc[j].CacheState = CACHE_E -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset do
invariant "47"
Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.HomeProc.CacheData = Sta.CurrData;
endruleset;




ruleset  i : NODE do
invariant "48"
Sta.Proc[i].CacheState = CACHE_E -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset  i : NODE do
invariant "49"
Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.Dir.Dirty = false;
endruleset;




ruleset  i : NODE do
invariant "50"
Sta.RpMsg[i].Cmd != RP_Replace -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "51"
Sta.Dir.Dirty = false & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_FAck;
endruleset;




ruleset  j : NODE do
invariant "52"
Sta.Dir.HeadVld = true & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.InvMsg[j].Cmd != INV_InvAck;
endruleset;




ruleset  i : NODE do
invariant "53"
Sta.Dir.Local = true -> Sta.Proc[i].CacheState != CACHE_E;
endruleset;




ruleset do
invariant "54"
Sta.Dir.HomeHeadPtr = true -> Sta.HomeProc.ProcCmd = NODE_None;
endruleset;




ruleset  i : NODE do
invariant "55"
Sta.Dir.Pending = true & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[i].CacheState != CACHE_S;
endruleset;




ruleset  i : NODE do
invariant "56"
Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE do
invariant "57"
Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.HomeProc.ProcCmd != NODE_Get;
endruleset;




ruleset  j : NODE do
invariant "58"
Sta.Dir.HomeHeadPtr = true -> Sta.RpMsg[j].Cmd != RP_Replace;
endruleset;




ruleset  j : NODE do
invariant "59"
Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "60"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.ShrSet[j] = false;
endruleset;




ruleset  j : NODE do
invariant "61"
Sta.Dir.ShrSet[j] = true -> Sta.Dir.InvSet[j] = true;
endruleset;




ruleset do
invariant "62"
Sta.Dir.HeadVld = false -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset  j : NODE do
invariant "63"
Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].CacheState = CACHE_I;
endruleset;




ruleset  i : NODE do
invariant "64"
Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset  i : NODE do
invariant "65"
Sta.UniMsg[i].Cmd = UNI_Get -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "66"
Sta.Dir.Local = false & Sta.Dir.InvSet[j] = true -> Sta.Dir.Dirty = false;
endruleset;




ruleset  i : NODE do
invariant "67"
Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE do
invariant "68"
Sta.UniMsg[i].HomeProc = false -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  j : NODE do
invariant "69"
Sta.HomeProc.CacheState = CACHE_E -> Sta.Dir.ShrSet[j] = false;
endruleset;




ruleset  j : NODE do
invariant "70"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "71"
Sta.Dir.ShrSet[j] = true -> Sta.MemData = Sta.CurrData;
endruleset;




ruleset  j : NODE do
invariant "72"
Sta.HomeProc.CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_PutX;
endruleset;




ruleset  j : NODE do
invariant "73"
Sta.Dir.Local = true & Sta.Dir.ShrSet[j] = true -> Sta.HomeProc.CacheState != CACHE_I;
endruleset;




ruleset  j : NODE do
invariant "74"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[j].ProcCmd = NODE_None;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "75"
i != j -> 
  (Sta.Dir.ShrSet[i] = true -> Sta.Proc[j].CacheState != CACHE_E);

endruleset;




ruleset  i : NODE do
invariant "76"
Sta.Dir.HomeHeadPtr = true -> Sta.Proc[i].CacheState = CACHE_I;
endruleset;




ruleset  j : NODE do
invariant "77"
Sta.Dir.InvSet[j] = true -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "78"
Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].ProcCmd = NODE_GetX;
endruleset;




ruleset do
invariant "79"
Sta.Dir.Local = true & Sta.Dir.Dirty = true -> Sta.HomeProc.CacheState = CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "80"
Sta.Dir.InvSet[j] = true -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset  i : NODE do
invariant "81"
Sta.Dir.ShrSet[i] = true -> Sta.Dir.ShrVld = true;
endruleset;




ruleset  i : NODE do
invariant "82"
Sta.Dir.InvSet[i] = true & Sta.Dir.Dirty = true -> Sta.HomeProc.CacheData = Sta.CurrData;
endruleset;




ruleset  j : NODE do
invariant "83"
Sta.HomeProc.CacheState = CACHE_E -> Sta.Proc[j].CacheState != CACHE_E;
endruleset;




ruleset do
invariant "84"
Sta.Dir.HomeHeadPtr = false -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "85"
Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[j] = false;
endruleset;




ruleset  j : NODE do
invariant "86"
Sta.Dir.Pending = true -> Sta.Dir.ShrSet[j] = false;
endruleset;




ruleset  j : NODE do
invariant "87"
Sta.UniMsg[j].HomeProc = true -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset do
invariant "88"
Sta.HomeProc.CacheState = CACHE_E -> Sta.Dir.Dirty = true;
endruleset;




ruleset  j : NODE do
invariant "89"
Sta.Dir.ShrSet[j] = true -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset do
invariant "90"
Sta.Dir.Local = true -> Sta.HomeProc.ProcCmd = NODE_None;
endruleset;




ruleset  j : NODE do
invariant "91"
Sta.UniMsg[j].Cmd = UNI_Get -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "92"
Sta.HomeProc.CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_PutX;
endruleset;




ruleset do
invariant "93"
Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "94"
i != j -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrSet[j] = false);

endruleset;




ruleset  i : NODE do
invariant "95"
Sta.Dir.ShrSet[i] = true -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "96"
i != j -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.ShrSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);

endruleset;




ruleset  i : NODE do
invariant "97"
Sta.Dir.Dirty = false & Sta.HomeProc.ProcCmd = NODE_Get -> Sta.InvMsg[i].Cmd != INV_InvAck;
endruleset;




ruleset do
invariant "98"
Sta.Dir.HeadVld = false -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset  j : NODE do
invariant "99"
Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_Get;
endruleset;




ruleset  j : NODE do
invariant "100"
Sta.Dir.HomeHeadPtr = true -> Sta.Proc[j].CacheState = CACHE_I;
endruleset;




ruleset  j : NODE do
invariant "101"
Sta.Proc[j].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset  j : NODE do
invariant "102"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[j].InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "103"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].ProcCmd = NODE_None;
endruleset;




ruleset  i : NODE do
invariant "104"
Sta.Dir.Pending = true -> Sta.Dir.ShrSet[i] = false;
endruleset;




ruleset do
invariant "105"
Sta.Dir.Dirty = false -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "106"
i != j -> 
  (Sta.Dir.ShrSet[j] = true -> Sta.InvMsg[i].Cmd != INV_Inv);

endruleset;




ruleset do
invariant "107"
Sta.Dir.Dirty = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset  i : NODE do
invariant "108"
Sta.UniMsg[i].HomeProc = false -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "109"
Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd = NODE_Get;
endruleset;




ruleset  j : NODE do
invariant "110"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.ShrVld = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "111"
i != j -> 
  (Sta.Dir.ShrSet[i] = true -> Sta.UniMsg[j].Cmd != UNI_PutX);

endruleset;




ruleset  j : NODE do
invariant "112"
Sta.Dir.InvSet[j] = true & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.HomeProc.ProcCmd != NODE_Get;
endruleset;




ruleset  i : NODE do
invariant "113"
Sta.Dir.HomeHeadPtr = true -> Sta.UniMsg[i].HomeProc = true;
endruleset;




ruleset  j : NODE do
invariant "114"
Sta.Dir.HeadPtr = j -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "115"
Sta.Dir.HeadPtr = i -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "116"
Sta.HomeProc.CacheState = CACHE_E -> Sta.Proc[i].CacheState != CACHE_E;
endruleset;




ruleset do
invariant "117"
Sta.HomeProc.CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset do
invariant "118"
Sta.Dir.HeadVld = true -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE do
invariant "119"
Sta.Dir.ShrSet[i] = true -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE do
invariant "120"
Sta.Dir.InvSet[i] = true -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset do
invariant "121"
Sta.Dir.Dirty = false -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset  i : NODE do
invariant "122"
Sta.Dir.InvSet[i] = true -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  j : NODE do
invariant "123"
Sta.Dir.Pending = true & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Proc[j].CacheState != CACHE_S;
endruleset;




ruleset  j : NODE do
invariant "124"
Sta.UniMsg[j].HomeProc = false -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE do
invariant "125"
Sta.Dir.HeadVld = false & Sta.HomeProc.ProcCmd = NODE_Get -> Sta.Dir.InvSet[i] = false;
endruleset;




ruleset do
invariant "126"
Sta.Dir.Dirty = true -> Sta.HomeProc.CacheState != CACHE_S;
endruleset;




ruleset do
invariant "127"
Sta.Dir.Local = false -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset do
invariant "128"
Sta.Dir.Local = true -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset do
invariant "129"
Sta.HomeProc.CacheState = CACHE_E -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset do
invariant "130"
Sta.Dir.HeadVld = false -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset do
invariant "131"
Sta.Dir.HomeHeadPtr = true & Sta.Dir.Local = false -> Sta.MemData = Sta.CurrData;
endruleset;




ruleset do
invariant "132"
Sta.Dir.HeadVld = false & Sta.HomeProc.ProcCmd = NODE_Get -> Sta.MemData = Sta.CurrData;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "133"
i != j -> 
  (Sta.Dir.InvSet[i] = true -> Sta.UniMsg[j].Cmd != UNI_PutX);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "134"
i != j -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[j].CacheState != CACHE_E);

endruleset;




ruleset  i : NODE do
invariant "135"
Sta.HomeProc.ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.InvMsg[i].Cmd != INV_InvAck;
endruleset;




ruleset  i : NODE do
invariant "136"
Sta.Dir.InvSet[i] = true -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset do
invariant "137"
Sta.Dir.HeadVld = false & Sta.Dir.Local = false -> Sta.MemData = Sta.CurrData;
endruleset;




ruleset  i : NODE do
invariant "138"
Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_Get;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "139"
i != j -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.InvSet[i] = false);

endruleset;




ruleset  i : NODE do
invariant "140"
Sta.Dir.ShrSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E;
endruleset;




ruleset do
invariant "141"
Sta.Dir.HeadVld = true -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "142"
i != j -> 
  (Sta.UniMsg[j].Proc = i -> Sta.HomeProc.InvMarked = false);

endruleset;




ruleset do
invariant "143"
Sta.Dir.HomeHeadPtr = true -> Sta.ShWbMsg.HomeProc = true;
endruleset;




ruleset  i : NODE do
invariant "144"
Sta.HomeProc.ProcCmd = NODE_Get & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_Inv;
endruleset;




ruleset  i : NODE do
invariant "145"
Sta.Dir.Pending = true & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset  i : NODE do
invariant "146"
Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[i] = false;
endruleset;




ruleset  i : NODE do
invariant "147"
Sta.Dir.ShrSet[i] = true -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset  i : NODE do
invariant "148"
Sta.Dir.HomeHeadPtr = true -> Sta.RpMsg[i].Cmd != RP_Replace;
endruleset;




ruleset  i : NODE do
invariant "149"
Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset  j : NODE do
invariant "150"
Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_GetX;
endruleset;




ruleset  i : NODE do
invariant "151"
Sta.Dir.ShrSet[i] = true -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset  j : NODE do
invariant "152"
Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].ProcCmd != NODE_Get;
endruleset;




ruleset  i : NODE do
invariant "153"
Sta.Dir.HeadPtr = i -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "154"
Sta.Dir.HomeHeadPtr = true -> Sta.InvMsg[j].Cmd != INV_InvAck;
endruleset;




ruleset  j : NODE do
invariant "155"
Sta.Dir.ShrSet[j] = true -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "156"
i != j -> 
  (Sta.Dir.ShrSet[j] = true -> Sta.Proc[i].CacheState != CACHE_E);

endruleset;




ruleset  j : NODE do
invariant "157"
Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[j].HomeProc = false;
endruleset;




ruleset  i : NODE do
invariant "158"
Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.Dir.Pending = false;
endruleset;




ruleset do
invariant "159"
Sta.Dir.HeadVld = false & Sta.HomeProc.ProcCmd = NODE_Get -> Sta.Dir.Dirty = false;
endruleset;




ruleset do
invariant "160"
Sta.Dir.HomeShrSet = false -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "161"
Sta.Proc[i].CacheState != CACHE_E -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "162"
Sta.Proc[j].CacheState != CACHE_E -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "163"
Sta.Dir.HomeHeadPtr = true -> Sta.Proc[i].CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "164"
Sta.Dir.Dirty = false & Sta.HomeProc.ProcCmd = NODE_Get -> Sta.InvMsg[j].Cmd != INV_InvAck;
endruleset;




ruleset  i : NODE do
invariant "165"
Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE do
invariant "166"
Sta.Proc[i].CacheState = CACHE_E -> Sta.HomeProc.CacheState = CACHE_I;
endruleset;




ruleset  j : NODE do
invariant "167"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[j].CacheData = Sta.CurrData;
endruleset;




ruleset  i : NODE do
invariant "168"
Sta.Proc[i].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset do
invariant "169"
Sta.HomeProc.ProcCmd = NODE_Get -> Sta.HomeProc.CacheState = CACHE_I;
endruleset;




ruleset  j : NODE do
invariant "170"
Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "171"
Sta.Proc[i].ProcCmd = NODE_None -> Sta.UniMsg[i].Cmd != UNI_Get;
endruleset;




ruleset  j : NODE do
invariant "172"
Sta.Dir.InvSet[j] = true & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.HeadPtr = j;
endruleset;




ruleset  i : NODE do
invariant "173"
Sta.Dir.Dirty = false -> Sta.UniMsg[i].Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE do
invariant "174"
Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = true -> Sta.InvMsg[i].Cmd != INV_InvAck;
endruleset;




ruleset do
invariant "175"
Sta.Dir.HomeHeadPtr = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset  j : NODE do
invariant "176"
Sta.UniMsg[j].Cmd = UNI_GetX & Sta.Dir.HeadVld = true -> Sta.InvMsg[j].Cmd != INV_Inv;
endruleset;




ruleset  i : NODE do
invariant "177"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.Dirty = true;
endruleset;




ruleset  j : NODE do
invariant "178"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[j].ProcCmd != NODE_GetX;
endruleset;




ruleset  i : NODE do
invariant "179"
Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.HomeProc.ProcCmd = NODE_None;
endruleset;




ruleset do
invariant "180"
Sta.Dir.Local = false -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset do
invariant "181"
Sta.Dir.Pending = false -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE do
invariant "182"
Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset do
invariant "183"
Sta.Dir.Pending = false -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "184"
i != j -> 
  (Sta.Dir.InvSet[i] = true -> Sta.Proc[j].CacheState != CACHE_E);

endruleset;




ruleset do
invariant "185"
Sta.Dir.Local = true -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  j : NODE do
invariant "186"
Sta.Dir.Dirty = true & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Proc[j].CacheState != CACHE_S;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "187"
i != j -> 
  (Sta.Dir.InvSet[i] = true & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[j] = false);

endruleset;




ruleset  j : NODE do
invariant "188"
Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset do
invariant "189"
Sta.Dir.HomeHeadPtr = true -> Sta.HomeProc.ProcCmd != NODE_Get;
endruleset;




ruleset  j : NODE do
invariant "190"
Sta.UniMsg[j].HomeProc = true -> Sta.Proc[j].CacheState = CACHE_I;
endruleset;




ruleset  i : NODE do
invariant "191"
Sta.Dir.ShrSet[i] = true -> Sta.MemData = Sta.CurrData;
endruleset;




ruleset  i : NODE do
invariant "192"
Sta.Dir.ShrSet[i] = true -> Sta.Dir.Pending = false;
endruleset;




ruleset  i : NODE do
invariant "193"
Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_Inv;
endruleset;




ruleset  j : NODE do
invariant "194"
Sta.Dir.Dirty = false -> Sta.UniMsg[j].Cmd != UNI_PutX;
endruleset;




ruleset do
invariant "195"
Sta.Dir.Local = true -> Sta.HomeProc.ProcCmd != NODE_Get;
endruleset;




ruleset  i : NODE do
invariant "196"
Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset do
invariant "197"
Sta.Dir.Pending = true -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "198"
i != j -> 
  (Sta.Dir.ShrSet[j] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);

endruleset;




ruleset do
invariant "199"
Sta.HomeProc.CacheState = CACHE_E -> Sta.HomeProc.CacheData = Sta.CurrData;
endruleset;




ruleset  j : NODE do
invariant "200"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.Dirty = true;
endruleset;




ruleset  i : NODE do
invariant "201"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.InvSet[i] = false;
endruleset;




ruleset  j : NODE do
invariant "202"
Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset do
invariant "203"
Sta.Dir.HomeHeadPtr = true -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset  i : NODE do
invariant "204"
Sta.Proc[i].ProcCmd = NODE_None -> Sta.Proc[i].InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "205"
Sta.Dir.Local = true -> Sta.Proc[j].CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "206"
Sta.Dir.Local = false & Sta.Dir.Pending = true -> Sta.Dir.InvSet[j] = false;
endruleset;




ruleset  j : NODE do
invariant "207"
Sta.Dir.HeadVld = false & Sta.HomeProc.ProcCmd = NODE_Get -> Sta.InvMsg[j].Cmd != INV_InvAck;
endruleset;




ruleset  i : NODE do
invariant "208"
Sta.Proc[i].CacheState = CACHE_E -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE do
invariant "209"
Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_Nak;
endruleset;




ruleset  j : NODE do
invariant "210"
Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[j] = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "211"
i != j -> 
  (Sta.UniMsg[i].Proc = j -> Sta.Dir.HomeInvSet = false);

endruleset;




ruleset  j : NODE do
invariant "212"
Sta.Dir.InvSet[j] = true & Sta.Dir.Dirty = true -> Sta.HomeProc.ProcCmd != NODE_Get;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "213"
i != j -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.InvMsg[i].Cmd != INV_InvAck);

endruleset;




ruleset  i : NODE do
invariant "214"
Sta.Dir.ShrSet[i] = true -> Sta.Dir.HeadVld = true;
endruleset;




ruleset  j : NODE do
invariant "215"
Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "216"
i != j -> 
  (Sta.Proc[j].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_Inv);

endruleset;




ruleset  i : NODE do
invariant "217"
Sta.Dir.InvSet[i] = true -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset do
invariant "218"
Sta.Dir.HomeHeadPtr = true -> Sta.NakcMsg.Cmd != NAKC_Nakc;
endruleset;




ruleset do
invariant "219"
Sta.Dir.Pending = false -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset do
invariant "220"
Sta.Dir.HeadVld = false -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "221"
i != j -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[j].CacheState != CACHE_E);

endruleset;




ruleset  i : NODE do
invariant "222"
Sta.Proc[i].ProcCmd = NODE_None -> Sta.UniMsg[i].Cmd != UNI_Put;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "223"
i != j -> 
  (Sta.UniMsg[i].Proc = j -> Sta.HomeProc.InvMarked = false);

endruleset;




ruleset  j : NODE do
invariant "224"
Sta.Dir.HomeHeadPtr = true -> Sta.Dir.InvSet[j] = false;
endruleset;




ruleset  i : NODE do
invariant "225"
Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.ShrVld = false;
endruleset;




ruleset  j : NODE do
invariant "226"
Sta.RpMsg[j].Cmd != RP_Replace -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE do
invariant "227"
Sta.Dir.InvSet[i] = true & Sta.Dir.Dirty = true -> Sta.Dir.HeadVld = false;
endruleset;




ruleset do
invariant "228"
Sta.HomeProc.ProcCmd != NODE_Get -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset  i : NODE do
invariant "229"
Sta.Proc[i].CacheState = CACHE_E -> Sta.HomeProc.CacheState != CACHE_E;
endruleset;




ruleset do
invariant "230"
Sta.Dir.Dirty = false -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "231"
i != j -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.InvSet[j] = false);

endruleset;




ruleset  i : NODE do
invariant "232"
Sta.Proc[i].CacheState != CACHE_E -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset do
invariant "233"
Sta.HomeProc.ProcCmd = NODE_Get -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE do
invariant "234"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  j : NODE do
invariant "235"
Sta.Proc[j].ProcCmd = NODE_None -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "236"
i != j -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.InvSet[j] = false);

endruleset;




ruleset do
invariant "237"
Sta.Dir.HomeHeadPtr = true -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset do
invariant "238"
Sta.Dir.HomeHeadPtr = true -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "239"
Sta.Dir.ShrSet[i] = true & Sta.Dir.Local = true -> Sta.HomeProc.CacheState != CACHE_I;
endruleset;




ruleset do
invariant "240"
Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset  i : NODE do
invariant "241"
Sta.UniMsg[i].HomeProc = false -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset  i : NODE do
invariant "242"
Sta.Proc[i].ProcCmd = NODE_None -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  j : NODE do
invariant "243"
Sta.Proc[j].ProcCmd = NODE_None -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "244"
Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_Put;
endruleset;




ruleset  i : NODE do
invariant "245"
Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.HomeProc.ProcCmd = NODE_None;
endruleset;




ruleset do
invariant "246"
Sta.Dir.HomeHeadPtr = true & Sta.Dir.Local = true -> Sta.HomeProc.CacheData = Sta.CurrData;
endruleset;




ruleset do
invariant "247"
Sta.Dir.Pending = true -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE do
invariant "248"
Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.InvSet[i] = true;
endruleset;




ruleset  i : NODE do
invariant "249"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrSet[i] = false;
endruleset;




ruleset do
invariant "250"
Sta.Dir.Dirty = true -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "251"
Sta.Proc[j].CacheState = CACHE_E -> Sta.HomeProc.CacheState = CACHE_I;
endruleset;




ruleset do
invariant "252"
Sta.Dir.HeadVld = false -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  j : NODE do
invariant "253"
Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset do
invariant "254"
Sta.HomeProc.ProcCmd = NODE_Get -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset do
invariant "255"
Sta.Dir.HomeHeadPtr = true -> Sta.Dir.Pending = false;
endruleset;




ruleset do
invariant "256"
Sta.HomeProc.ProcCmd = NODE_Get -> Sta.Dir.Local = false;
endruleset;




ruleset  i : NODE do
invariant "257"
Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_GetX;
endruleset;




ruleset  j : NODE do
invariant "258"
Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "259"
Sta.Dir.HomeHeadPtr = true -> Sta.UniMsg[j].HomeProc = true;
endruleset;




ruleset  j : NODE do
invariant "260"
Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadVld = false;
endruleset;




ruleset  i : NODE do
invariant "261"
Sta.Dir.ShrSet[i] = true -> Sta.Dir.InvSet[i] = true;
endruleset;




ruleset do
invariant "262"
Sta.Dir.HomeHeadPtr = false -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "263"
Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState = CACHE_I;
endruleset;




ruleset  j : NODE do
invariant "264"
Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_Nak;
endruleset;




ruleset  i : NODE do
invariant "265"
Sta.UniMsg[i].HomeProc = true -> Sta.Proc[i].CacheState != CACHE_S;
endruleset;




ruleset  i : NODE do
invariant "266"
Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "267"
Sta.Dir.Local = true & Sta.Dir.ShrSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck;
endruleset;




ruleset do
invariant "268"
Sta.HomeProc.CacheState = CACHE_E -> Sta.Dir.ShrVld = false;
endruleset;




ruleset  i : NODE do
invariant "269"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "270"
Sta.HomeProc.ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_InvAck;
endruleset;




ruleset  i : NODE do
invariant "271"
Sta.Dir.HomeHeadPtr = true -> Sta.Dir.InvSet[i] = false;
endruleset;




ruleset  i : NODE do
invariant "272"
Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Proc[i].CacheState != CACHE_S;
endruleset;




ruleset  j : NODE do
invariant "273"
Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].ProcCmd = NODE_Get;
endruleset;




ruleset  i : NODE do
invariant "274"
Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[i] = false;
endruleset;




ruleset do
invariant "275"
Sta.Dir.Local = false -> Sta.HomeProc.CacheState != CACHE_E;
endruleset;




ruleset do
invariant "276"
Sta.Dir.Local = false -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset do
invariant "277"
Sta.HomeProc.ProcCmd = NODE_Get -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE do
invariant "278"
Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.Local = true;
endruleset;




ruleset do
invariant "279"
Sta.Dir.Dirty = false & Sta.Dir.Pending = true -> Sta.Dir.HeadVld = false;
endruleset;




ruleset  j : NODE do
invariant "280"
Sta.Dir.InvSet[j] = true -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset  j : NODE do
invariant "281"
Sta.UniMsg[j].HomeProc = false -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE do
invariant "282"
Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd != NODE_None;
endruleset;




ruleset  i : NODE do
invariant "283"
Sta.Dir.HeadVld = false -> Sta.UniMsg[i].Cmd != UNI_PutX;
endruleset;




ruleset  j : NODE do
invariant "284"
Sta.UniMsg[j].HomeProc = false -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "285"
Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "286"
Sta.Dir.Local = true & Sta.Dir.ShrSet[j] = true -> Sta.HomeProc.CacheData = Sta.CurrData;
endruleset;




ruleset  j : NODE do
invariant "287"
Sta.Dir.InvSet[j] = true & Sta.Dir.Dirty = true -> Sta.HomeProc.CacheState = CACHE_E;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "288"
i != j -> 
  (Sta.UniMsg[j].Proc = i -> Sta.Dir.HomeShrSet = false);

endruleset;




ruleset  j : NODE do
invariant "289"
Sta.UniMsg[j].HomeProc = true -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "290"
Sta.Dir.Dirty = false & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.HomeProc.ProcCmd = NODE_None;
endruleset;




ruleset  j : NODE do
invariant "291"
Sta.HomeProc.ProcCmd = NODE_Get & Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.InvMsg[j].Cmd != INV_Inv;
endruleset;




ruleset do
invariant "292"
Sta.Dir.Pending = true -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset do
invariant "293"
Sta.Dir.Dirty = false -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "294"
Sta.Dir.HeadVld = false & Sta.HomeProc.ProcCmd = NODE_Get -> Sta.InvMsg[j].Cmd != INV_Inv;
endruleset;




ruleset  j : NODE do
invariant "295"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset do
invariant "296"
Sta.Dir.HomeHeadPtr = true & Sta.Dir.Local = true -> Sta.HomeProc.CacheState != CACHE_I;
endruleset;




ruleset  j : NODE do
invariant "297"
Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset do
invariant "298"
Sta.Dir.HomeHeadPtr = true -> Sta.Dir.HeadVld = false;
endruleset;




ruleset  j : NODE do
invariant "299"
Sta.RpMsg[j].Cmd != RP_Replace -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "300"
i != j -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_PutX);

endruleset;




ruleset  i : NODE do
invariant "301"
Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.HomeProc.ProcCmd = NODE_None;
endruleset;




ruleset  j : NODE do
invariant "302"
Sta.Dir.InvSet[j] = true & Sta.Dir.Dirty = true -> Sta.Dir.HeadVld = false;
endruleset;




ruleset  j : NODE do
invariant "303"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.HeadVld = true;
endruleset;




ruleset  i : NODE do
invariant "304"
Sta.Proc[i].ProcCmd = NODE_None -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE do
invariant "305"
Sta.Dir.HomeHeadPtr = true -> Sta.Proc[i].CacheState != CACHE_S;
endruleset;




ruleset  j : NODE do
invariant "306"
Sta.Dir.Local = true & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.InvSet[j] = true;
endruleset;




ruleset  j : NODE do
invariant "307"
Sta.Dir.Dirty = false & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.HomeProc.ProcCmd != NODE_Get;
endruleset;




ruleset  i : NODE do
invariant "308"
Sta.Dir.ShrSet[i] = true & Sta.Dir.Local = true -> Sta.HomeProc.CacheState = CACHE_S;
endruleset;




ruleset  i : NODE do
invariant "309"
Sta.HomeProc.ProcCmd = NODE_Get & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_InvAck;
endruleset;




ruleset  i : NODE do
invariant "310"
Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd = NODE_GetX;
endruleset;




ruleset do
invariant "311"
Sta.Dir.HomeHeadPtr = true -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "312"
i != j -> 
  (Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Proc[i].CacheState != CACHE_E);

endruleset;




ruleset do
invariant "313"
Sta.Dir.HeadVld = true -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "314"
i != j -> 
  (Sta.Dir.Pending = true & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.UniMsg[j].Cmd != UNI_PutX);

endruleset;




ruleset  j : NODE do
invariant "315"
Sta.UniMsg[j].HomeProc = false -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset  i : NODE do
invariant "316"
Sta.UniMsg[i].HomeProc = true -> Sta.Proc[i].CacheState = CACHE_I;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "317"
i != j -> 
  (Sta.UniMsg[j].Proc = i -> Sta.Dir.HomeInvSet = false);

endruleset;




ruleset  j : NODE do
invariant "318"
Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE do
invariant "319"
Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "320"
Sta.Proc[i].ProcCmd = NODE_None -> Sta.UniMsg[i].Cmd != UNI_GetX;
endruleset;




ruleset do
invariant "321"
Sta.Dir.HomeHeadPtr = true -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset  j : NODE do
invariant "322"
Sta.Proc[j].CacheState = CACHE_E -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset do
invariant "323"
Sta.Dir.Local = true -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset do
invariant "324"
Sta.Dir.HomeShrSet = false -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE do
invariant "325"
Sta.Dir.Local = false & Sta.Dir.Pending = true -> Sta.Dir.InvSet[i] = false;
endruleset;




ruleset  j : NODE do
invariant "326"
Sta.Proc[j].CacheState != CACHE_E -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE do
invariant "327"
Sta.Proc[i].ProcCmd = NODE_None -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset do
invariant "328"
Sta.HomeProc.CacheState = CACHE_E -> Sta.HomeProc.ProcCmd = NODE_None;
endruleset;




ruleset  j : NODE do
invariant "329"
Sta.Dir.ShrSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "330"
i != j -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[j].CacheState = CACHE_E -> Sta.InvMsg[i].Cmd != INV_Inv);

endruleset;




ruleset do
invariant "331"
Sta.Dir.Dirty = false -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE do
invariant "332"
Sta.Proc[i].ProcCmd = NODE_None -> Sta.UniMsg[i].Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "333"
i != j -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_PutX);

endruleset;




ruleset  i : NODE do
invariant "334"
Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd != NODE_Get;
endruleset;




ruleset  i : NODE do
invariant "335"
Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.HomeProc.ProcCmd != NODE_Get;
endruleset;




ruleset  j : NODE do
invariant "336"
Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_Nak;
endruleset;




ruleset  i : NODE do
invariant "337"
Sta.Dir.Dirty = false -> Sta.Proc[i].CacheState != CACHE_E;
endruleset;




ruleset  i : NODE do
invariant "338"
Sta.Proc[i].CacheState = CACHE_E -> Sta.HomeProc.CacheState != CACHE_S;
endruleset;




ruleset  j : NODE do
invariant "339"
Sta.UniMsg[j].HomeProc = true -> Sta.Proc[j].CacheState != CACHE_S;
endruleset;




ruleset  j : NODE do
invariant "340"
Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_GetX;
endruleset;




ruleset  j : NODE do
invariant "341"
Sta.Proc[j].CacheState != CACHE_E -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "342"
Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState != CACHE_E;
endruleset;




ruleset  i : NODE do
invariant "343"
Sta.UniMsg[i].HomeProc = true -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  j : NODE do
invariant "344"
Sta.Dir.Local = true & Sta.Dir.ShrSet[j] = true -> Sta.HomeProc.CacheState = CACHE_S;
endruleset;




ruleset do
invariant "345"
Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Dir.HeadVld = true;
endruleset;




ruleset  i : NODE do
invariant "346"
Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  j : NODE do
invariant "347"
Sta.Dir.InvSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX;
endruleset;




ruleset do
invariant "348"
Sta.HomeProc.ProcCmd = NODE_Get -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "349"
Sta.UniMsg[j].Cmd = UNI_GetX & Sta.Dir.HeadVld = true -> Sta.InvMsg[j].Cmd != INV_InvAck;
endruleset;




ruleset  j : NODE do
invariant "350"
Sta.Dir.Local = true & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.HeadPtr = j;
endruleset;




ruleset  j : NODE do
invariant "351"
Sta.Dir.HomeHeadPtr = true -> Sta.InvMsg[j].Cmd != INV_Inv;
endruleset;




ruleset  j : NODE do
invariant "352"
Sta.Dir.HeadVld = true & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.InvMsg[j].Cmd != INV_Inv;
endruleset;




ruleset  j : NODE do
invariant "353"
Sta.Dir.HomeHeadPtr = true -> Sta.Proc[j].InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "354"
Sta.Dir.Local = true -> Sta.UniMsg[i].Cmd != UNI_PutX;
endruleset;




ruleset  j : NODE do
invariant "355"
Sta.Dir.Dirty = false & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.HeadPtr = j;
endruleset;




ruleset  i : NODE do
invariant "356"
Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].HomeProc = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "357"
i != j -> 
  (Sta.Dir.InvSet[j] = true -> Sta.Proc[i].CacheState != CACHE_E);

endruleset;




ruleset do
invariant "358"
Sta.Dir.HomeHeadPtr = true & Sta.Dir.Dirty = true -> Sta.HomeProc.CacheData = Sta.CurrData;
endruleset;




ruleset  i : NODE do
invariant "359"
Sta.HomeProc.ProcCmd = NODE_Get & Sta.Dir.ShrSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck;
endruleset;




ruleset  i : NODE do
invariant "360"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadVld = true;
endruleset;




ruleset  i : NODE do
invariant "361"
Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset do
invariant "362"
Sta.HomeProc.ProcCmd != NODE_Get -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "363"
i != j -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[i].CacheState != CACHE_E);

endruleset;




ruleset  j : NODE do
invariant "364"
Sta.Dir.Dirty = false -> Sta.Proc[j].CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "365"
Sta.Dir.HeadPtr = j -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset do
invariant "366"
Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset  i : NODE do
invariant "367"
Sta.UniMsg[i].HomeProc = true -> Sta.Proc[i].CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "368"
Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.ShrSet[j] = false;
endruleset;




ruleset  i : NODE do
invariant "369"
Sta.HomeProc.ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.InvMsg[i].Cmd != INV_Inv;
endruleset;




ruleset  i : NODE do
invariant "370"
Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr = i;
endruleset;




ruleset do
invariant "371"
Sta.Dir.Local = true & Sta.Dir.Dirty = true -> Sta.HomeProc.CacheData = Sta.CurrData;
endruleset;




ruleset  i : NODE do
invariant "372"
Sta.Dir.HomeHeadPtr = true -> Sta.InvMsg[i].Cmd != INV_InvAck;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "373"
i != j -> 
  (Sta.Dir.InvSet[j] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);

endruleset;




ruleset do
invariant "374"
Sta.Dir.HeadVld = false -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE do
invariant "375"
Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset  j : NODE do
invariant "376"
Sta.Dir.InvSet[j] = true & Sta.Dir.Dirty = true -> Sta.HomeProc.CacheData = Sta.CurrData;
endruleset;




ruleset do
invariant "377"
Sta.Dir.Dirty = true -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE do
invariant "378"
Sta.Dir.ShrSet[i] = true -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "379"
Sta.Dir.HeadPtr = j -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset do
invariant "380"
Sta.Dir.HomeHeadPtr = false -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "381"
i != j -> 
  (Sta.UniMsg[j].Cmd = UNI_GetX & Sta.Dir.ShrSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);

endruleset;




ruleset do
invariant "382"
Sta.Dir.Dirty = false -> Sta.HomeProc.CacheState != CACHE_E;
endruleset;




ruleset  i : NODE do
invariant "383"
Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd != NODE_GetX;
endruleset;




ruleset  i : NODE do
invariant "384"
Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.ShrSet[i] = false;
endruleset;




ruleset do
invariant "385"
Sta.Dir.Pending = true -> Sta.HomeProc.CacheState != CACHE_S;
endruleset;




ruleset  j : NODE do
invariant "386"
Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "387"
i != j -> 
  (Sta.Dir.InvSet[j] = true & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[i] = false);

endruleset;




ruleset  j : NODE do
invariant "388"
Sta.UniMsg[j].HomeProc = true -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "389"
Sta.Dir.Local = true -> Sta.UniMsg[j].Cmd != UNI_PutX;
endruleset;




ruleset  j : NODE do
invariant "390"
Sta.Dir.ShrSet[j] = true -> Sta.Dir.ShrVld = true;
endruleset;




ruleset  i : NODE do
invariant "391"
Sta.Dir.HeadPtr = i -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE do
invariant "392"
Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE do
invariant "393"
Sta.HomeProc.CacheState = CACHE_E -> Sta.Dir.ShrSet[i] = false;
endruleset;




ruleset do
invariant "394"
Sta.Dir.HomeInvSet = false -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset do
invariant "395"
Sta.HomeProc.CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset  j : NODE do
invariant "396"
Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState != CACHE_S;
endruleset;




ruleset  j : NODE do
invariant "397"
Sta.Dir.InvSet[j] = true -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset do
invariant "398"
Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.MemData = Sta.CurrData;
endruleset;




ruleset  j : NODE do
invariant "399"
Sta.Dir.ShrSet[j] = true -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset do
invariant "400"
Sta.HomeProc.CacheState = CACHE_E -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset do
invariant "401"
Sta.Dir.HomeHeadPtr = true & Sta.Dir.Dirty = true -> Sta.HomeProc.CacheState != CACHE_I;
endruleset;




ruleset  i : NODE do
invariant "402"
Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_Put;
endruleset;




ruleset  j : NODE do
invariant "403"
Sta.RpMsg[j].Cmd != RP_Replace -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE do
invariant "404"
Sta.Dir.InvSet[i] = true -> Sta.HomeUniMsg.Cmd != UNI_Put;
endruleset;




ruleset do
invariant "405"
Sta.Dir.Local = true & Sta.Dir.Dirty = true -> Sta.Dir.HeadVld = false;
endruleset;




ruleset  j : NODE do
invariant "406"
Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].ProcCmd != NODE_None;
endruleset;




ruleset  j : NODE do
invariant "407"
Sta.HomeProc.ProcCmd = NODE_Get & Sta.Dir.ShrSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck;
endruleset;




ruleset  j : NODE do
invariant "408"
Sta.Dir.HomeHeadPtr = true -> Sta.UniMsg[j].Cmd != UNI_Put;
endruleset;




ruleset  i : NODE do
invariant "409"
Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr = i;
endruleset;




ruleset do
invariant "410"
Sta.Dir.Dirty = true -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "411"
Sta.Dir.InvSet[j] = true -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset do
invariant "412"
Sta.Dir.HomeHeadPtr = true & Sta.Dir.Local = false -> Sta.Dir.Dirty = false;
endruleset;




ruleset  i : NODE do
invariant "413"
Sta.Dir.ShrSet[i] = true & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_FAck;
endruleset;




ruleset  i : NODE do
invariant "414"
Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_FAck;
endruleset;




ruleset  i : NODE do
invariant "415"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].ProcCmd != NODE_Get;
endruleset;




ruleset do
invariant "416"
Sta.Dir.HomeHeadPtr = true -> Sta.Dir.ShrVld = false;
endruleset;




ruleset do
invariant "417"
Sta.HomeProc.ProcCmd = NODE_Get -> Sta.HomeProc.CacheState != CACHE_S;
endruleset;




ruleset do
invariant "418"
Sta.Dir.Dirty = true -> Sta.Dir.ShrVld = false;
endruleset;




ruleset  i : NODE do
invariant "419"
Sta.Dir.ShrSet[i] = true -> Sta.Dir.Dirty = false;
endruleset;




ruleset  j : NODE do
invariant "420"
Sta.Dir.HeadVld = false -> Sta.UniMsg[j].Cmd != UNI_PutX;
endruleset;




ruleset do
invariant "421"
Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.Dir.HeadVld = false;
endruleset;




ruleset  j : NODE do
invariant "422"
Sta.Dir.ShrSet[j] = true -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE do
invariant "423"
Sta.Dir.ShrSet[i] = true & Sta.Dir.Local = true -> Sta.HomeProc.CacheData = Sta.CurrData;
endruleset;




ruleset  i : NODE do
invariant "424"
Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Dir.HeadPtr = i;
endruleset;




ruleset  j : NODE do
invariant "425"
Sta.Dir.ShrSet[j] = true -> Sta.HomeProc.CacheState != CACHE_E;
endruleset;




ruleset do
invariant "426"
Sta.HomeProc.ProcCmd = NODE_Get -> Sta.HomeProc.CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "427"
Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].ProcCmd != NODE_None;
endruleset;




ruleset  j : NODE do
invariant "428"
Sta.Dir.HomeHeadPtr = true -> Sta.UniMsg[j].Cmd != UNI_Nak;
endruleset;




ruleset  i : NODE do
invariant "429"
Sta.Dir.ShrSet[i] = true -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset do
invariant "430"
Sta.Dir.HeadVld = true -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset  j : NODE do
invariant "431"
Sta.Proc[j].ProcCmd = NODE_None -> Sta.Proc[j].InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "432"
Sta.Dir.ShrSet[j] = true -> Sta.Dir.HeadVld = true;
endruleset;




ruleset  i : NODE do
invariant "433"
Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState = CACHE_I;
endruleset;




ruleset do
invariant "434"
Sta.Dir.HeadVld = false & Sta.Dir.Local = false -> Sta.Dir.Dirty = false;
endruleset;




ruleset  i : NODE do
invariant "435"
Sta.Dir.ShrSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE do
invariant "436"
Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "437"
i != j -> 
  (Sta.Dir.ShrSet[i] = true -> Sta.InvMsg[j].Cmd != INV_InvAck);

endruleset;




ruleset  j : NODE do
invariant "438"
Sta.Dir.InvSet[j] = true & Sta.Dir.Dirty = true -> Sta.HomeProc.CacheState != CACHE_I;
endruleset;




ruleset  i : NODE do
invariant "439"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.Local = false;
endruleset;




ruleset  j : NODE do
invariant "440"
Sta.Dir.ShrSet[j] = true -> Sta.Dir.Pending = false;
endruleset;




ruleset  i : NODE do
invariant "441"
Sta.Dir.InvSet[i] = true -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE do
invariant "442"
Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX;
endruleset;




ruleset  j : NODE do
invariant "443"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.Local = false;
endruleset;




ruleset  j : NODE do
invariant "444"
Sta.Proc[j].CacheState = CACHE_E -> Sta.HomeProc.CacheState != CACHE_S;
endruleset;




ruleset do
invariant "445"
Sta.HomeProc.ProcCmd = NODE_Get -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset do
invariant "446"
Sta.Dir.Dirty = false & Sta.Dir.Pending = true -> Sta.HomeProc.CacheState = CACHE_I;
endruleset;




ruleset  j : NODE do
invariant "447"
Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.HomeProc.ProcCmd = NODE_None;
endruleset;




ruleset  i : NODE do
invariant "448"
Sta.UniMsg[i].HomeProc = true -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "449"
Sta.Dir.HeadVld = false & Sta.HomeProc.ProcCmd = NODE_Get -> Sta.Dir.InvSet[j] = false;
endruleset;




ruleset do
invariant "450"
Sta.Dir.Local = true & Sta.Dir.Dirty = true -> Sta.HomeProc.CacheState != CACHE_I;
endruleset;




ruleset  i : NODE do
invariant "451"
Sta.Dir.InvSet[i] = true & Sta.Dir.Dirty = true -> Sta.HomeProc.ProcCmd != NODE_Get;
endruleset;




ruleset  i : NODE do
invariant "452"
Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "453"
Sta.Dir.ShrSet[j] = true -> Sta.Dir.Dirty = false;
endruleset;




ruleset  j : NODE do
invariant "454"
Sta.Dir.Local = false & Sta.Dir.InvSet[j] = true -> Sta.MemData = Sta.CurrData;
endruleset;




ruleset  i : NODE do
invariant "455"
Sta.Proc[i].ProcCmd = NODE_None -> Sta.UniMsg[i].Cmd != UNI_Nak;
endruleset;




ruleset do
invariant "456"
Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.Dir.Dirty = false;
endruleset;




ruleset  i : NODE do
invariant "457"
Sta.Dir.HeadVld = false & Sta.HomeProc.ProcCmd = NODE_Get -> Sta.InvMsg[i].Cmd != INV_Inv;
endruleset;




ruleset  i : NODE do
invariant "458"
Sta.Dir.ShrSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset  j : NODE do
invariant "459"
Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset  i : NODE do
invariant "460"
Sta.Dir.HomeHeadPtr = true -> Sta.UniMsg[i].Cmd != UNI_Put;
endruleset;




ruleset  i : NODE do
invariant "461"
Sta.Dir.HeadVld = false & Sta.HomeProc.ProcCmd = NODE_Get -> Sta.InvMsg[i].Cmd != INV_InvAck;
endruleset;




ruleset do
invariant "462"
Sta.HomeProc.CacheState = CACHE_E -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "463"
Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadPtr = j;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "464"
i != j -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.ShrSet[i] = false);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "465"
i != j -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.InvMsg[j].Cmd != INV_InvAck);

endruleset;




ruleset do
invariant "466"
Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.HomeProc.CacheData = Sta.CurrData;
endruleset;




ruleset  j : NODE do
invariant "467"
Sta.Dir.InvSet[j] = true -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "468"
Sta.Dir.Pending = true & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.WbMsg.Cmd != WB_Wb;
endruleset;




ruleset  i : NODE do
invariant "469"
Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "470"
Sta.Dir.HomeHeadPtr = true -> Sta.Proc[j].CacheState != CACHE_S;
endruleset;




ruleset  i : NODE do
invariant "471"
Sta.Dir.InvSet[i] = true & Sta.Dir.Dirty = true -> Sta.HomeProc.CacheState = CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "472"
Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_PutX;
endruleset;




ruleset do
invariant "473"
Sta.Dir.Dirty = false -> Sta.MemData = Sta.CurrData;
endruleset;




ruleset  i : NODE do
invariant "474"
Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState != CACHE_S;
endruleset;




ruleset  j : NODE do
invariant "475"
Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "476"
Sta.Dir.Dirty = false & Sta.HomeProc.ProcCmd = NODE_Get -> Sta.InvMsg[j].Cmd != INV_Inv;
endruleset;




ruleset  i : NODE do
invariant "477"
Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Dir.InvSet[i] = true;
endruleset;




ruleset  i : NODE do
invariant "478"
Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HeadPtr = i;
endruleset;




ruleset  j : NODE do
invariant "479"
Sta.Proc[j].ProcCmd = NODE_None -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset do
invariant "480"
Sta.Dir.Pending = true -> Sta.Dir.ShrVld = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "481"
i != j -> 
  (Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.InvSet[i] = false);

endruleset;




ruleset  i : NODE do
invariant "482"
Sta.UniMsg[i].HomeProc = false -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset do
invariant "483"
Sta.Dir.Local = true -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset  j : NODE do
invariant "484"
Sta.Dir.InvSet[j] = true & Sta.Dir.Dirty = true -> Sta.Dir.Local = true;
endruleset;




ruleset do
invariant "485"
Sta.HomeProc.CacheState = CACHE_E -> Sta.HomeProc.ProcCmd != NODE_Get;
endruleset;




ruleset  i : NODE do
invariant "486"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset do
invariant "487"
Sta.HomeProc.ProcCmd != NODE_Get -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "488"
Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.Local = true;
endruleset;




ruleset  i : NODE do
invariant "489"
Sta.Dir.ShrSet[i] = true -> Sta.HomeProc.CacheState != CACHE_E;
endruleset;




ruleset do
invariant "490"
Sta.Dir.HeadVld = true -> Sta.HomeProc.CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "491"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[j].ProcCmd != NODE_Get;
endruleset;




ruleset do
invariant "492"
Sta.Dir.HomeHeadPtr = true & Sta.Dir.Dirty = true -> Sta.Dir.Local = true;
endruleset;




ruleset  j : NODE do
invariant "493"
Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[j] = false;
endruleset;




ruleset  j : NODE do
invariant "494"
Sta.Dir.InvSet[j] = true & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.HomeProc.ProcCmd = NODE_None;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "495"
i != j -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.ShrSet[j] = false);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "496"
i != j -> 
  (Sta.Dir.ShrSet[i] = true -> Sta.InvMsg[j].Cmd != INV_Inv);

endruleset;




ruleset do
invariant "497"
Sta.Dir.Pending = true -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "498"
Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  j : NODE do
invariant "499"
Sta.HomeProc.ProcCmd = NODE_Get & Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.InvMsg[j].Cmd != INV_InvAck;
endruleset;




ruleset  i : NODE do
invariant "500"
Sta.Proc[i].CacheState != CACHE_E -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE do
invariant "501"
Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadVld = false;
endruleset;




ruleset  j : NODE do
invariant "502"
Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_Get;
endruleset;




ruleset  j : NODE do
invariant "503"
Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.ShrVld = false;
endruleset;




ruleset  j : NODE do
invariant "504"
Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].CacheState != CACHE_S;
endruleset;




ruleset  i : NODE do
invariant "505"
Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[i] = false;
endruleset;




ruleset  j : NODE do
invariant "506"
Sta.HomeProc.ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_Inv;
endruleset;




ruleset  i : NODE do
invariant "507"
Sta.Dir.ShrSet[i] = true -> Sta.Dir.HomeHeadPtr = false;
endruleset;




ruleset do
invariant "508"
Sta.HomeProc.CacheState = CACHE_E -> Sta.HomeUniMsg.Cmd != UNI_PutX;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "509"
i != j -> 
  (Sta.UniMsg[i].Proc = j -> Sta.Dir.HomeShrSet = false);

endruleset;




ruleset  i : NODE do
invariant "510"
Sta.Dir.Dirty = false & Sta.HomeProc.ProcCmd = NODE_Get -> Sta.InvMsg[i].Cmd != INV_Inv;
endruleset;




ruleset  i : NODE do
invariant "511"
Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.MemData = Sta.CurrData;
endruleset;




ruleset  i : NODE do
invariant "512"
Sta.Dir.InvSet[i] = true & Sta.Dir.Dirty = true -> Sta.HomeProc.ProcCmd = NODE_None;
endruleset;




ruleset  i : NODE do
invariant "513"
Sta.Dir.InvSet[i] = true -> Sta.HomeProc.InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "514"
Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].ProcCmd != NODE_GetX;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "515"
i != j -> 
  (Sta.Dir.ShrSet[j] = true -> Sta.InvMsg[i].Cmd != INV_InvAck);

endruleset;




ruleset  j : NODE do
invariant "516"
Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].ProcCmd != NODE_GetX;
endruleset;




ruleset  j : NODE do
invariant "517"
Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.InvSet[j] = false;
endruleset;




ruleset  i : NODE do
invariant "518"
Sta.Dir.HomeHeadPtr = true -> Sta.Proc[i].InvMarked = false;
endruleset;




ruleset  i : NODE do
invariant "519"
Sta.Dir.HomeHeadPtr = true -> Sta.Dir.ShrSet[i] = false;
endruleset;




ruleset  j : NODE do
invariant "520"
Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  i : NODE do
invariant "521"
Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_InvAck;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "522"
i != j -> 
  (Sta.Dir.Pending = true & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.UniMsg[i].Cmd != UNI_PutX);

endruleset;




ruleset  j : NODE do
invariant "523"
Sta.Dir.HomeHeadPtr = true -> Sta.UniMsg[j].Cmd != UNI_PutX;
endruleset;




ruleset do
invariant "524"
Sta.Dir.HomeHeadPtr = true -> Sta.ShWbMsg.Cmd != SHWB_FAck;
endruleset;




ruleset  j : NODE do
invariant "525"
Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset do
invariant "526"
Sta.Dir.Dirty = false -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  j : NODE do
invariant "527"
Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.HomeProc.ProcCmd != NODE_Get;
endruleset;




ruleset do
invariant "528"
Sta.Dir.Local = false -> Sta.HomeProc.CacheState != CACHE_S;
endruleset;




ruleset  i : NODE do
invariant "529"
Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState != CACHE_S;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "530"
i != j -> 
  (Sta.UniMsg[j].Cmd = UNI_Get & Sta.Proc[i].CacheState = CACHE_E -> Sta.InvMsg[j].Cmd != INV_Inv);

endruleset;




ruleset  j : NODE do
invariant "531"
Sta.Proc[j].CacheState = CACHE_E -> Sta.HomeProc.CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "532"
Sta.Dir.HomeHeadPtr = true -> Sta.Dir.ShrSet[j] = false;
endruleset;




ruleset  i : NODE do
invariant "533"
Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].InvMarked = false;
endruleset;




ruleset  j : NODE do
invariant "534"
Sta.Dir.ShrSet[j] = true -> Sta.Dir.HomeShrSet = false;
endruleset;




ruleset  j : NODE do
invariant "535"
Sta.Dir.Pending = true & Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.HeadPtr = j;
endruleset;




ruleset do
invariant "536"
Sta.Dir.Local = true -> Sta.Dir.HomeInvSet = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "537"
i != j -> 
  (Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.InvSet[i] = false);

endruleset;




ruleset  j : NODE do
invariant "538"
Sta.Dir.ShrSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb;
endruleset;




ruleset  i : NODE do
invariant "539"
Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = true -> Sta.InvMsg[i].Cmd != INV_Inv;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "540"
i != j -> 
  (Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.ShrSet[i] = false);

endruleset;




ruleset  i : NODE do
invariant "541"
Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.HomeProc.ProcCmd != NODE_Get;
endruleset;




ruleset  i : NODE do
invariant "542"
Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState != CACHE_E;
endruleset;




ruleset  j : NODE do
invariant "543"
Sta.Dir.ShrSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX;
endruleset;
