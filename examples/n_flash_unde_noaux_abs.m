type
  CACHE_STATE : enum{CACHE_I, CACHE_S, CACHE_E};
  NODE_CMD : enum{NODE_None, NODE_Get, NODE_GetX};
  UNI_CMD : enum{UNI_None, UNI_Get, UNI_GetX, UNI_Put, UNI_PutX, UNI_Nak};
  INV_CMD : enum{INV_None, INV_Inv, INV_InvAck};
  RP_CMD : enum{RP_None, RP_Replace};
  WB_CMD : enum{WB_None, WB_Wb};
  SHWB_CMD : enum{SHWB_None, SHWB_ShWb, SHWB_FAck};
  NAKC_CMD : enum{NAKC_None, NAKC_Nakc};
  NODE : scalarset(2);
  DATA : scalarset(2);



record_0 : record
Cmd :  RP_CMD;
end;


record_1 : record
Data :  DATA;
HomeProc :  boolean;
Proc :  NODE;
Cmd :  UNI_CMD;
end;


record_2 : record
CacheData :  DATA;
CacheState :  CACHE_STATE;
InvMarked :  boolean;
ProcCmd :  NODE_CMD;
end;


record_3 : record
HomeInvSet :  boolean;
HomeShrSet :  boolean;
HomeHeadPtr :  boolean;
InvSet :  boolean;
ShrSet :  boolean;
ShrVld :  boolean;
HeadPtr :  NODE;
HeadVld :  boolean;
Dirty :  boolean;
Local :  boolean;
Pending :  boolean;
end;


record_4 : record
CurrData :  DATA;
HomeRpMsg :  record_0;
HomeInvMsg :  record_0;
HomeUniMsg :  record_1;
HomeProc :  record_2;
NakcMsg :  record_0;
ShWbMsg :  record_1;
WbMsg :  record_1;
RpMsg : array [NODE] of record_0;
InvMsg : array [NODE] of record_0;
UniMsg : array [NODE] of record_1;
MemData :  DATA;
Dir :  record_3;
Proc : array [NODE] of record_2;
end;


var
Sta :  record_4;


startstate
begin
  Sta.MemData := 1;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  Sta.Dir.HeadPtr := 1;
  Sta.Dir.HomeHeadPtr := true;
  Sta.Dir.ShrVld := false;
  Sta.WbMsg.Cmd := WB_None;
  Sta.WbMsg.Proc := 1;
  Sta.WbMsg.HomeProc := true;
  Sta.WbMsg.Data := 1;
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.ShWbMsg.Proc := 1;
  Sta.ShWbMsg.HomeProc := true;
  Sta.ShWbMsg.Data := 1;
  Sta.NakcMsg.Cmd := NAKC_None;
  for p : NODE do
    Sta.Proc[p].ProcCmd := NODE_None;
    Sta.Proc[p].InvMarked := false;
    Sta.Proc[p].CacheState := CACHE_I;
    Sta.Proc[p].CacheData := 1;
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
    Sta.UniMsg[p].Cmd := UNI_None;
    Sta.UniMsg[p].Proc := 1;
    Sta.UniMsg[p].HomeProc := true;
    Sta.UniMsg[p].Data := 1;
    Sta.InvMsg[p].Cmd := INV_None;
    Sta.RpMsg[p].Cmd := RP_None;
  endfor;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.HomeProc.CacheData := 1;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.HomeUniMsg.Proc := 1;
  Sta.HomeUniMsg.HomeProc := true;
  Sta.HomeUniMsg.Data := 1;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.HomeRpMsg.Cmd := RP_None;
  Sta.CurrData := 1;
endstartstate;


ruleset src : NODE do
  rule "n_NI_Replace3"
    ((Sta.RpMsg[src].Cmd = RP_Replace) & (Sta.Dir.ShrVld = true)) ==>
  begin
    Sta.RpMsg[src].Cmd := RP_None;
    Sta.Dir.ShrSet[src] := false;
    Sta.Dir.InvSet[src] := false;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Replace4"
    ((Sta.RpMsg[src].Cmd = RP_Replace) & (Sta.Dir.ShrVld = false)) ==>
  begin
    Sta.RpMsg[src].Cmd := RP_None;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_InvAck_311"
    ((((((Sta.InvMsg[src].Cmd = INV_InvAck) & (Sta.Dir.Pending = true)) & (Sta.Dir.InvSet[src] = true)) & (Sta.Dir.Dirty = true)) & (Sta.Dir.HomeInvSet = false)) & (forall p : NODE do ((p = src) | (Sta.Dir.InvSet[p] = false)) endforall)) ==>
  begin
    Sta.InvMsg[src].Cmd := INV_None;
    Sta.Dir.InvSet[src] := false;
    Sta.Dir.Pending := false;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_InvAck_212"
    ((((((Sta.InvMsg[src].Cmd = INV_InvAck) & (Sta.Dir.Pending = true)) & (Sta.Dir.InvSet[src] = true)) & (Sta.Dir.Local = false)) & (Sta.Dir.HomeInvSet = false)) & (forall p : NODE do ((p = src) | (Sta.Dir.InvSet[p] = false)) endforall)) ==>
  begin
    Sta.InvMsg[src].Cmd := INV_None;
    Sta.Dir.InvSet[src] := false;
    Sta.Dir.Pending := false;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_InvAck_113"
    (((((((Sta.InvMsg[src].Cmd = INV_InvAck) & (Sta.Dir.Pending = true)) & (Sta.Dir.InvSet[src] = true)) & (Sta.Dir.Local = true)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HomeInvSet = false)) & (forall p : NODE do ((p = src) | (Sta.Dir.InvSet[p] = false)) endforall)) ==>
  begin
    Sta.InvMsg[src].Cmd := INV_None;
    Sta.Dir.InvSet[src] := false;
    Sta.Dir.Pending := false;
    Sta.Dir.Local := false;
  endrule;
endruleset;


ruleset dst : NODE; src : NODE do
  rule "n_NI_InvAck_exists14"
    (((((Sta.InvMsg[src].Cmd = INV_InvAck) & (Sta.Dir.Pending = true)) & (Sta.Dir.InvSet[src] = true)) & (!(dst = src))) & (Sta.Dir.InvSet[dst] = true)) ==>
  begin
    Sta.InvMsg[src].Cmd := INV_None;
    Sta.Dir.InvSet[src] := false;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_InvAck_exists_Home15"
    ((((Sta.InvMsg[src].Cmd = INV_InvAck) & (Sta.Dir.Pending = true)) & (Sta.Dir.InvSet[src] = true)) & (Sta.Dir.HomeInvSet = true)) ==>
  begin
    Sta.InvMsg[src].Cmd := INV_None;
    Sta.Dir.InvSet[src] := false;
  endrule;
endruleset;


ruleset dst : NODE do
  rule "n_NI_Inv16"
    ((Sta.InvMsg[dst].Cmd = INV_Inv) & (Sta.Proc[dst].ProcCmd = NODE_Get)) ==>
  begin
    Sta.InvMsg[dst].Cmd := INV_InvAck;
    Sta.Proc[dst].CacheState := CACHE_I;
    Sta.Proc[dst].InvMarked := true;
  endrule;
endruleset;


ruleset dst : NODE do
  rule "n_NI_Inv17"
    ((Sta.InvMsg[dst].Cmd = INV_Inv) & (!(Sta.Proc[dst].ProcCmd = NODE_Get))) ==>
  begin
    Sta.InvMsg[dst].Cmd := INV_InvAck;
    Sta.Proc[dst].CacheState := CACHE_I;
  endrule;
endruleset;


ruleset dst : NODE do
  rule "n_NI_Remote_PutX18"
    ((Sta.UniMsg[dst].Cmd = UNI_PutX) & (Sta.Proc[dst].ProcCmd = NODE_GetX)) ==>
  begin
    Sta.UniMsg[dst].Cmd := UNI_None;
    Sta.UniMsg[dst].HomeProc := false;
    Sta.Proc[dst].ProcCmd := NODE_None;
    Sta.Proc[dst].InvMarked := false;
    Sta.Proc[dst].CacheState := CACHE_E;
    Sta.Proc[dst].CacheData := Sta.UniMsg[dst].Data;
  endrule;
endruleset;


ruleset dst : NODE do
  rule "n_NI_Remote_Put20"
    ((Sta.UniMsg[dst].Cmd = UNI_Put) & (Sta.Proc[dst].InvMarked = true)) ==>
  begin
    Sta.UniMsg[dst].Cmd := UNI_None;
    Sta.UniMsg[dst].HomeProc := false;
    Sta.Proc[dst].ProcCmd := NODE_None;
    Sta.Proc[dst].InvMarked := false;
    Sta.Proc[dst].CacheState := CACHE_I;
  endrule;
endruleset;


ruleset dst : NODE do
  rule "n_NI_Remote_Put21"
    ((Sta.UniMsg[dst].Cmd = UNI_Put) & (Sta.Proc[dst].InvMarked = false)) ==>
  begin
    Sta.UniMsg[dst].Cmd := UNI_None;
    Sta.UniMsg[dst].HomeProc := false;
    Sta.Proc[dst].ProcCmd := NODE_None;
    Sta.Proc[dst].CacheState := CACHE_S;
    Sta.Proc[dst].CacheData := Sta.UniMsg[dst].Data;
  endrule;
endruleset;


ruleset dst : NODE do
  rule "n_NI_Remote_GetX_PutX_Home24"
    ((((Sta.HomeUniMsg.Cmd = UNI_GetX) & (Sta.HomeUniMsg.Proc = dst)) & (Sta.HomeUniMsg.HomeProc = false)) & (Sta.Proc[dst].CacheState = CACHE_E)) ==>
  begin
    Sta.Proc[dst].CacheState := CACHE_I;
    Sta.HomeUniMsg.Cmd := UNI_PutX;
    Sta.HomeUniMsg.Data := Sta.Proc[dst].CacheData;
  endrule;
endruleset;


ruleset dst : NODE; src : NODE do
  rule "n_NI_Remote_GetX_PutX25"
    (((((!(src = dst)) & (Sta.UniMsg[src].Cmd = UNI_GetX)) & (Sta.UniMsg[src].Proc = dst)) & (Sta.UniMsg[src].HomeProc = false)) & (Sta.Proc[dst].CacheState = CACHE_E)) ==>
  begin
    Sta.Proc[dst].CacheState := CACHE_I;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
    Sta.ShWbMsg.Cmd := SHWB_FAck;
    Sta.ShWbMsg.Proc := src;
    Sta.ShWbMsg.HomeProc := false;
  endrule;
endruleset;


ruleset dst : NODE do
  rule "n_NI_Remote_GetX_Nak_Home26"
    ((((Sta.HomeUniMsg.Cmd = UNI_GetX) & (Sta.HomeUniMsg.Proc = dst)) & (Sta.HomeUniMsg.HomeProc = false)) & (!(Sta.Proc[dst].CacheState = CACHE_E))) ==>
  begin
    Sta.HomeUniMsg.Cmd := UNI_Nak;
    Sta.NakcMsg.Cmd := NAKC_Nakc;
  endrule;
endruleset;


ruleset dst : NODE; src : NODE do
  rule "n_NI_Remote_GetX_Nak27"
    (((((!(src = dst)) & (Sta.UniMsg[src].Cmd = UNI_GetX)) & (Sta.UniMsg[src].Proc = dst)) & (Sta.UniMsg[src].HomeProc = false)) & (!(Sta.Proc[dst].CacheState = CACHE_E))) ==>
  begin
    Sta.UniMsg[src].Cmd := UNI_Nak;
    Sta.UniMsg[src].Proc := dst;
    Sta.UniMsg[src].HomeProc := false;
    Sta.NakcMsg.Cmd := NAKC_Nakc;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_1128"
    ((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = true)) & (Sta.Dir.Local = true)) & (Sta.HomeProc.CacheState = CACHE_E)) ==>
  begin
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      Sta.Dir.InvSet[p] := false;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.HomeProc.CacheData;
    Sta.HomeProc.CacheState := CACHE_I;
  endrule;
endruleset;


ruleset dst : NODE; src : NODE do
  rule "n_NI_Local_GetX_PutX_1029"
    (((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) & (Sta.Dir.HeadPtr = src)) & (Sta.Dir.HomeHeadPtr = false)) & (Sta.Dir.ShrSet[dst] = true)) & (Sta.Dir.Local = false)) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_10_Home30"
    (((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) & (Sta.Dir.HeadPtr = src)) & (Sta.Dir.HomeHeadPtr = false)) & (Sta.Dir.HomeShrSet = true)) & (Sta.Dir.Local = false)) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_931"
    (((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) & (!(Sta.Dir.HeadPtr = src))) & (Sta.Dir.Local = false)) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_932"
    (((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) & (Sta.Dir.HomeHeadPtr = true)) & (Sta.Dir.Local = false)) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
  endrule;
endruleset;


ruleset dst : NODE; src : NODE do
  rule "n_NI_Local_GetX_PutX_8_NODE_Get33"
    ((((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) & (Sta.Dir.HeadPtr = src)) & (Sta.Dir.HomeHeadPtr = false)) & (Sta.Dir.ShrSet[dst] = true)) & (Sta.Dir.Local = true)) & (Sta.HomeProc.ProcCmd = NODE_Get)) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
    Sta.HomeProc.InvMarked := true;
  endrule;
endruleset;


ruleset dst : NODE; src : NODE do
  rule "n_NI_Local_GetX_PutX_834"
    ((((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) & (Sta.Dir.HeadPtr = src)) & (Sta.Dir.HomeHeadPtr = false)) & (Sta.Dir.ShrSet[dst] = true)) & (Sta.Dir.Local = true)) & (!(Sta.HomeProc.ProcCmd = NODE_Get))) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_8_Home_NODE_Get35"
    ((((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) & (Sta.Dir.HeadPtr = src)) & (Sta.Dir.HomeHeadPtr = false)) & (Sta.Dir.HomeShrSet = true)) & (Sta.Dir.Local = true)) & (Sta.HomeProc.ProcCmd = NODE_Get)) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
    Sta.HomeProc.InvMarked := true;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_8_Home36"
    ((((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) & (Sta.Dir.HeadPtr = src)) & (Sta.Dir.HomeHeadPtr = false)) & (Sta.Dir.HomeShrSet = true)) & (Sta.Dir.Local = true)) & (!(Sta.HomeProc.ProcCmd = NODE_Get))) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_7_NODE_Get37"
    ((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) & (!(Sta.Dir.HeadPtr = src))) & (Sta.Dir.Local = true)) & (Sta.HomeProc.ProcCmd = NODE_Get)) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
    Sta.HomeProc.InvMarked := true;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_7_NODE_Get38"
    ((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) & (Sta.Dir.HomeHeadPtr = true)) & (Sta.Dir.Local = true)) & (Sta.HomeProc.ProcCmd = NODE_Get)) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
    Sta.HomeProc.InvMarked := true;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_739"
    ((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) & (!(Sta.Dir.HeadPtr = src))) & (Sta.Dir.Local = true)) & (!(Sta.HomeProc.ProcCmd = NODE_Get))) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_740"
    ((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) & (Sta.Dir.HomeHeadPtr = false)) & (Sta.Dir.Local = true)) & (!(Sta.HomeProc.ProcCmd = NODE_Get))) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_641"
    (((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadPtr = src)) & (Sta.Dir.HomeHeadPtr = false)) & (Sta.Dir.HomeShrSet = false)) & (forall p : NODE do ((!(p = src)) -> (Sta.Dir.ShrSet[p] = false)) endforall)) & (Sta.Dir.Local = false)) ==>
  begin
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      Sta.Dir.InvSet[p] := false;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_542"
    ((((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadPtr = src)) & (Sta.Dir.HomeHeadPtr = false)) & (Sta.Dir.HomeShrSet = false)) & (forall p : NODE do ((!(p = src)) -> (Sta.Dir.ShrSet[p] = false)) endforall)) & (Sta.Dir.Local = true)) & (!(Sta.HomeProc.ProcCmd = NODE_Get))) ==>
  begin
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      Sta.Dir.InvSet[p] := false;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_443"
    ((((((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadPtr = src)) & (Sta.Dir.HomeHeadPtr = false)) & (Sta.Dir.HomeShrSet = false)) & (forall p : NODE do ((!(p = src)) -> (Sta.Dir.ShrSet[p] = false)) endforall)) & (Sta.Dir.Local = true)) & (Sta.HomeProc.ProcCmd = NODE_Get)) ==>
  begin
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      Sta.Dir.InvSet[p] := false;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
    Sta.HomeProc.InvMarked := true;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_344"
    ((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = false)) & (Sta.Dir.Local = false)) ==>
  begin
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      Sta.Dir.InvSet[p] := false;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_245"
    (((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = false)) & (Sta.Dir.Local = true)) & (!(Sta.HomeProc.ProcCmd = NODE_Get))) ==>
  begin
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      Sta.Dir.InvSet[p] := false;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_146"
    (((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = false)) & (Sta.Dir.Local = true)) & (Sta.HomeProc.ProcCmd = NODE_Get)) ==>
  begin
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      Sta.Dir.InvSet[p] := false;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
    Sta.HomeProc.InvMarked := true;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_GetX47"
    ((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = true)) & (Sta.Dir.Local = false)) & (!(Sta.Dir.HeadPtr = src))) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.UniMsg[src].Cmd := UNI_GetX;
    Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
    Sta.UniMsg[src].HomeProc := Sta.Dir.HomeHeadPtr;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_GetX48"
    ((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = true)) & (Sta.Dir.Local = false)) & (Sta.Dir.HomeHeadPtr = true)) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.UniMsg[src].Cmd := UNI_GetX;
    Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
    Sta.UniMsg[src].HomeProc := Sta.Dir.HomeHeadPtr;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_Nak49"
    (((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Pending = true)) ==>
  begin
    Sta.UniMsg[src].Cmd := UNI_Nak;
    Sta.UniMsg[src].HomeProc := true;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_Nak50"
    (((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Dirty = true)) & (Sta.Dir.Local = true)) & (!(Sta.HomeProc.CacheState = CACHE_E))) ==>
  begin
    Sta.UniMsg[src].Cmd := UNI_Nak;
    Sta.UniMsg[src].HomeProc := true;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_Nak51"
    ((((((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true)) & (Sta.Dir.Dirty = true)) & (Sta.Dir.Local = false)) & (Sta.Dir.HeadPtr = src)) & (Sta.Dir.HomeHeadPtr = false)) ==>
  begin
    Sta.UniMsg[src].Cmd := UNI_Nak;
    Sta.UniMsg[src].HomeProc := true;
  endrule;
endruleset;


ruleset dst : NODE do
  rule "n_NI_Remote_Get_Put_Home52"
    ((((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.HomeUniMsg.Proc = dst)) & (Sta.HomeUniMsg.HomeProc = false)) & (Sta.Proc[dst].CacheState = CACHE_E)) ==>
  begin
    Sta.Proc[dst].CacheState := CACHE_S;
    Sta.HomeUniMsg.Cmd := UNI_Put;
    Sta.HomeUniMsg.Data := Sta.Proc[dst].CacheData;
  endrule;
endruleset;


ruleset dst : NODE; src : NODE do
  rule "n_NI_Remote_Get_Put53"
    (((((!(src = dst)) & (Sta.UniMsg[src].Cmd = UNI_Get)) & (Sta.UniMsg[src].Proc = dst)) & (Sta.UniMsg[src].HomeProc = false)) & (Sta.Proc[dst].CacheState = CACHE_E)) ==>
  begin
    Sta.Proc[dst].CacheState := CACHE_S;
    Sta.UniMsg[src].Cmd := UNI_Put;
    Sta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
    Sta.ShWbMsg.Cmd := SHWB_ShWb;
    Sta.ShWbMsg.Proc := src;
    Sta.ShWbMsg.HomeProc := false;
    Sta.ShWbMsg.Data := Sta.Proc[dst].CacheData;
  endrule;
endruleset;


ruleset dst : NODE do
  rule "n_NI_Remote_Get_Nak_Home54"
    ((((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.HomeUniMsg.Proc = dst)) & (Sta.HomeUniMsg.HomeProc = false)) & (!(Sta.Proc[dst].CacheState = CACHE_E))) ==>
  begin
    Sta.HomeUniMsg.Cmd := UNI_Nak;
    Sta.NakcMsg.Cmd := NAKC_Nakc;
  endrule;
endruleset;


ruleset dst : NODE; src : NODE do
  rule "n_NI_Remote_Get_Nak55"
    (((((!(src = dst)) & (Sta.UniMsg[src].Cmd = UNI_Get)) & (Sta.UniMsg[src].Proc = dst)) & (Sta.UniMsg[src].HomeProc = false)) & (!(Sta.Proc[dst].CacheState = CACHE_E))) ==>
  begin
    Sta.UniMsg[src].Cmd := UNI_Nak;
    Sta.UniMsg[src].Proc := dst;
    Sta.UniMsg[src].HomeProc := false;
    Sta.NakcMsg.Cmd := NAKC_Nakc;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_Get_Put_Dirty56"
    (((((((Sta.UniMsg[src].Cmd = UNI_Get) & (Sta.UniMsg[src].HomeProc = true)) & (!(Sta.RpMsg[src].Cmd = RP_Replace))) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = true)) & (Sta.Dir.Local = true)) & (Sta.HomeProc.CacheState = CACHE_E)) ==>
  begin
    Sta.Dir.Dirty := false;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.MemData := Sta.HomeProc.CacheData;
    Sta.HomeProc.CacheState := CACHE_S;
    Sta.UniMsg[src].Cmd := UNI_Put;
    Sta.UniMsg[src].Data := Sta.HomeProc.CacheData;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_Get_Put57"
    ((((((Sta.UniMsg[src].Cmd = UNI_Get) & (Sta.UniMsg[src].HomeProc = true)) & (!(Sta.RpMsg[src].Cmd = RP_Replace))) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = false)) ==>
  begin
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.UniMsg[src].Cmd := UNI_Put;
    Sta.UniMsg[src].Data := Sta.MemData;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_Get_Put_Head58"
    ((((((Sta.UniMsg[src].Cmd = UNI_Get) & (Sta.UniMsg[src].HomeProc = true)) & (!(Sta.RpMsg[src].Cmd = RP_Replace))) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) ==>
  begin
    Sta.Dir.ShrVld := true;
    Sta.Dir.ShrSet[src] := true;
    for p : NODE do
      if (p = src) then
        Sta.Dir.InvSet[p] := true;
else
        Sta.Dir.InvSet[p] := Sta.Dir.ShrSet[p];
      endif;
    endfor;
    Sta.Dir.HomeInvSet := Sta.Dir.HomeShrSet;
    Sta.UniMsg[src].Cmd := UNI_Put;
    Sta.UniMsg[src].Data := Sta.MemData;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_Get_Get59"
    (((((((Sta.UniMsg[src].Cmd = UNI_Get) & (Sta.UniMsg[src].HomeProc = true)) & (!(Sta.RpMsg[src].Cmd = RP_Replace))) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = true)) & (Sta.Dir.Local = false)) & (!(Sta.Dir.HeadPtr = src))) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.UniMsg[src].Cmd := UNI_Get;
    Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
    Sta.UniMsg[src].HomeProc := Sta.Dir.HomeHeadPtr;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_Get_Get60"
    (((((((Sta.UniMsg[src].Cmd = UNI_Get) & (Sta.UniMsg[src].HomeProc = true)) & (!(Sta.RpMsg[src].Cmd = RP_Replace))) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = true)) & (Sta.Dir.Local = false)) & (Sta.Dir.HomeHeadPtr = true)) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.UniMsg[src].Cmd := UNI_Get;
    Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
    Sta.UniMsg[src].HomeProc := Sta.Dir.HomeHeadPtr;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_Get_Nak61"
    ((((Sta.UniMsg[src].Cmd = UNI_Get) & (Sta.UniMsg[src].HomeProc = true)) & (!(Sta.RpMsg[src].Cmd = RP_Replace))) & (Sta.Dir.Pending = true)) ==>
  begin
    Sta.UniMsg[src].Cmd := UNI_Nak;
    Sta.UniMsg[src].HomeProc := true;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_Get_Nak62"
    ((((((Sta.UniMsg[src].Cmd = UNI_Get) & (Sta.UniMsg[src].HomeProc = true)) & (!(Sta.RpMsg[src].Cmd = RP_Replace))) & (Sta.Dir.Dirty = true)) & (Sta.Dir.Local = true)) & (!(Sta.HomeProc.CacheState = CACHE_E))) ==>
  begin
    Sta.UniMsg[src].Cmd := UNI_Nak;
    Sta.UniMsg[src].HomeProc := true;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_Get_Nak63"
    (((((((Sta.UniMsg[src].Cmd = UNI_Get) & (Sta.UniMsg[src].HomeProc = true)) & (!(Sta.RpMsg[src].Cmd = RP_Replace))) & (Sta.Dir.Dirty = true)) & (Sta.Dir.Local = false)) & (Sta.Dir.HeadPtr = src)) & (Sta.Dir.HomeHeadPtr = false)) ==>
  begin
    Sta.UniMsg[src].Cmd := UNI_Nak;
    Sta.UniMsg[src].HomeProc := true;
  endrule;
endruleset;


ruleset dst : NODE do
  rule "n_NI_Nak66"
    (Sta.UniMsg[dst].Cmd = UNI_Nak) ==>
  begin
    Sta.UniMsg[dst].Cmd := UNI_None;
    Sta.UniMsg[dst].HomeProc := false;
    Sta.Proc[dst].ProcCmd := NODE_None;
    Sta.Proc[dst].InvMarked := false;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_PI_Remote_Replace68"
    ((Sta.Proc[src].ProcCmd = NODE_None) & (Sta.Proc[src].CacheState = CACHE_S)) ==>
  begin
    Sta.Proc[src].CacheState := CACHE_I;
    Sta.RpMsg[src].Cmd := RP_Replace;
  endrule;
endruleset;


ruleset dst : NODE do
  rule "n_PI_Remote_PutX71"
    ((Sta.Proc[dst].ProcCmd = NODE_None) & (Sta.Proc[dst].CacheState = CACHE_E)) ==>
  begin
    Sta.Proc[dst].CacheState := CACHE_I;
    Sta.WbMsg.Cmd := WB_Wb;
    Sta.WbMsg.Proc := dst;
    Sta.WbMsg.HomeProc := false;
    Sta.WbMsg.Data := Sta.Proc[dst].CacheData;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_PI_Remote_GetX80"
    ((Sta.Proc[src].ProcCmd = NODE_None) & (Sta.Proc[src].CacheState = CACHE_I)) ==>
  begin
    Sta.Proc[src].ProcCmd := NODE_GetX;
    Sta.UniMsg[src].Cmd := UNI_GetX;
    Sta.UniMsg[src].HomeProc := true;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_PI_Remote_Get84"
    ((Sta.Proc[src].ProcCmd = NODE_None) & (Sta.Proc[src].CacheState = CACHE_I)) ==>
  begin
    Sta.Proc[src].ProcCmd := NODE_Get;
    Sta.UniMsg[src].Cmd := UNI_Get;
    Sta.UniMsg[src].HomeProc := true;
  endrule;
endruleset;


ruleset data : DATA do
  rule "n_Store_Home85"
    (Sta.HomeProc.CacheState = CACHE_E) ==>
  begin
    Sta.HomeProc.CacheData := data;
    Sta.CurrData := data;
  endrule;
endruleset;


ruleset data : DATA; src : NODE do
  rule "n_Store86"
    (Sta.Proc[src].CacheState = CACHE_E) ==>
  begin
    Sta.Proc[src].CacheData := data;
    Sta.CurrData := data;
  endrule;
endruleset;


rule "n_NI_Replace_Home1"
  ((Sta.HomeRpMsg.Cmd = RP_Replace) & (Sta.Dir.ShrVld = true)) ==>
begin
  Sta.HomeRpMsg.Cmd := RP_None;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
endrule;


rule "n_NI_Replace_Home2"
  ((Sta.HomeRpMsg.Cmd = RP_Replace) & (Sta.Dir.ShrVld = false)) ==>
begin
  Sta.HomeRpMsg.Cmd := RP_None;
endrule;


rule "n_NI_ShWb5"
  ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.ShWbMsg.HomeProc = true)) ==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.ShWbMsg.HomeProc := false;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.ShrVld := true;
  for p : NODE do
    if (((p = Sta.ShWbMsg.Proc) & (Sta.ShWbMsg.HomeProc = false)) | (Sta.Dir.ShrSet[p] = true)) then
      Sta.Dir.ShrSet[p] := true;
      Sta.Dir.InvSet[p] := true;
else
      Sta.Dir.ShrSet[p] := false;
      Sta.Dir.InvSet[p] := false;
    endif;
  endfor;
  Sta.Dir.HomeShrSet := true;
  Sta.Dir.HomeInvSet := true;
  Sta.MemData := Sta.ShWbMsg.Data;
endrule;


rule "n_NI_ShWb6"
  ((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.Dir.HomeShrSet = true)) ==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.ShWbMsg.HomeProc := false;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.ShrVld := true;
  for p : NODE do
    if (((p = Sta.ShWbMsg.Proc) & (Sta.ShWbMsg.HomeProc = false)) | (Sta.Dir.ShrSet[p] = true)) then
      Sta.Dir.ShrSet[p] := true;
      Sta.Dir.InvSet[p] := true;
else
      Sta.Dir.ShrSet[p] := false;
      Sta.Dir.InvSet[p] := false;
    endif;
  endfor;
  Sta.Dir.HomeShrSet := true;
  Sta.Dir.HomeInvSet := true;
  Sta.MemData := Sta.ShWbMsg.Data;
endrule;


rule "n_NI_ShWb7"
  (((Sta.ShWbMsg.Cmd = SHWB_ShWb) & (Sta.ShWbMsg.HomeProc = false)) & (Sta.Dir.HomeShrSet = false)) ==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.ShWbMsg.HomeProc := false;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.ShrVld := true;
  for p : NODE do
    if (((p = Sta.ShWbMsg.Proc) & (Sta.ShWbMsg.HomeProc = false)) | (Sta.Dir.ShrSet[p] = true)) then
      Sta.Dir.ShrSet[p] := true;
      Sta.Dir.InvSet[p] := true;
else
      Sta.Dir.ShrSet[p] := false;
      Sta.Dir.InvSet[p] := false;
    endif;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.MemData := Sta.ShWbMsg.Data;
endrule;


rule "n_NI_FAck8"
  ((Sta.ShWbMsg.Cmd = SHWB_FAck) & (Sta.Dir.Dirty = true)) ==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  Sta.ShWbMsg.HomeProc := false;
  Sta.Dir.HeadPtr := Sta.ShWbMsg.Proc;
  Sta.Dir.HomeHeadPtr := Sta.ShWbMsg.HomeProc;
endrule;


rule "n_NI_FAck9"
  ((Sta.ShWbMsg.Cmd = SHWB_FAck) & (!(Sta.Dir.Dirty = true))) ==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  Sta.ShWbMsg.HomeProc := false;
endrule;


rule "n_NI_Wb10"
  (Sta.WbMsg.Cmd = WB_Wb) ==>
begin
  Sta.WbMsg.Cmd := WB_None;
  Sta.WbMsg.HomeProc := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  Sta.MemData := Sta.WbMsg.Data;
endrule;


rule "n_NI_Local_PutXAcksDone19"
  (Sta.HomeUniMsg.Cmd = UNI_PutX) ==>
begin
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.HomeUniMsg.HomeProc := false;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := true;
  Sta.Dir.HeadVld := false;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
  Sta.HomeProc.CacheData := Sta.HomeUniMsg.Data;
endrule;


rule "n_NI_Local_Put22"
  ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.HomeProc.InvMarked = true)) ==>
begin
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.HomeUniMsg.HomeProc := false;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.Local := true;
  Sta.MemData := Sta.HomeUniMsg.Data;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;


rule "n_NI_Local_Put23"
  ((Sta.HomeUniMsg.Cmd = UNI_Put) & (Sta.HomeProc.InvMarked = false)) ==>
begin
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.HomeUniMsg.HomeProc := false;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.Local := true;
  Sta.MemData := Sta.HomeUniMsg.Data;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.CacheState := CACHE_S;
  Sta.HomeProc.CacheData := Sta.HomeUniMsg.Data;
endrule;


rule "n_NI_Nak_Clear64"
  (Sta.NakcMsg.Cmd = NAKC_Nakc) ==>
begin
  Sta.NakcMsg.Cmd := NAKC_None;
  Sta.Dir.Pending := false;
endrule;


rule "n_NI_Nak_Home65"
  (Sta.HomeUniMsg.Cmd = UNI_Nak) ==>
begin
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.HomeUniMsg.HomeProc := false;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
endrule;


rule "n_PI_Local_Replace67"
  ((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_S)) ==>
begin
  Sta.Dir.Local := false;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;


rule "n_PI_Local_PutX69"
  (((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_E)) & (Sta.Dir.Pending = true)) ==>
begin
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.Dir.Dirty := false;
  Sta.MemData := Sta.HomeProc.CacheData;
endrule;


rule "n_PI_Local_PutX70"
  (((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_E)) & (!(Sta.Dir.Pending = true))) ==>
begin
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := false;
  Sta.MemData := Sta.HomeProc.CacheData;
endrule;


rule "n_PI_Local_GetX_PutX_HeadVld7572"
  (((((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_S)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) ==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  Sta.Dir.Pending := true;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | ((Sta.Dir.HeadPtr = p) & (Sta.Dir.HomeHeadPtr = false))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
  Sta.HomeProc.CacheData := Sta.MemData;
endrule;


rule "n_PI_Local_GetX_PutX_HeadVld7473"
  (((((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_I)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) ==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  Sta.Dir.Pending := true;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | ((Sta.Dir.HeadPtr = p) & (Sta.Dir.HomeHeadPtr = false))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
  Sta.HomeProc.CacheData := Sta.MemData;
endrule;


rule "n_PI_Local_GetX_PutX7374"
  (((((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_S)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = false)) ==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
  Sta.HomeProc.CacheData := Sta.MemData;
endrule;


rule "n_PI_Local_GetX_PutX7275"
  (((((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_I)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = false)) ==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
  Sta.HomeProc.CacheData := Sta.MemData;
endrule;


rule "n_PI_Local_GetX_PutX_HeadVld76"
  (((((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_I)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) ==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  Sta.Dir.Pending := true;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | ((Sta.Dir.HeadPtr = p) & (Sta.Dir.HomeHeadPtr = false))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
  Sta.HomeProc.CacheData := Sta.MemData;
endrule;


rule "n_PI_Local_GetX_PutX_HeadVld77"
  (((((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_S)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.Dir.HeadVld = true)) ==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  Sta.Dir.Pending := true;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | ((Sta.Dir.HeadPtr = p) & (Sta.Dir.HomeHeadPtr = false))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
  Sta.HomeProc.CacheData := Sta.MemData;
endrule;


rule "n_PI_Local_GetX_GetX78"
  ((((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_I)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = true)) ==>
begin
  Sta.HomeProc.ProcCmd := NODE_GetX;
  Sta.Dir.Pending := true;
  Sta.HomeUniMsg.Cmd := UNI_GetX;
  Sta.HomeUniMsg.Proc := Sta.Dir.HeadPtr;
  Sta.HomeUniMsg.HomeProc := Sta.Dir.HomeHeadPtr;
endrule;


rule "n_PI_Local_GetX_GetX79"
  ((((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_S)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = true)) ==>
begin
  Sta.HomeProc.ProcCmd := NODE_GetX;
  Sta.Dir.Pending := true;
  Sta.HomeUniMsg.Cmd := UNI_GetX;
  Sta.HomeUniMsg.Proc := Sta.Dir.HeadPtr;
  Sta.HomeUniMsg.HomeProc := Sta.Dir.HomeHeadPtr;
endrule;


rule "n_PI_Local_Get_Put81"
  (((((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_I)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.HomeProc.InvMarked = true)) ==>
begin
  Sta.Dir.Local := true;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;


rule "n_PI_Local_Get_Put82"
  (((((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_I)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = false)) & (Sta.HomeProc.InvMarked = false)) ==>
begin
  Sta.Dir.Local := true;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.CacheState := CACHE_S;
  Sta.HomeProc.CacheData := Sta.MemData;
endrule;


rule "n_PI_Local_Get_Get83"
  ((((Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_I)) & (Sta.Dir.Pending = false)) & (Sta.Dir.Dirty = true)) ==>
begin
  Sta.HomeProc.ProcCmd := NODE_Get;
  Sta.Dir.Pending := true;
  Sta.HomeUniMsg.Cmd := UNI_Get;
  Sta.HomeUniMsg.Proc := Sta.Dir.HeadPtr;
  Sta.HomeUniMsg.HomeProc := Sta.Dir.HomeHeadPtr;
endrule;


rule "n_NI_InvAck_311_src_3"
  ((Sta.Dir.Pending = true) & (Sta.Dir.Dirty = true) & (Sta.Dir.HomeInvSet = false) & (forall p : NODE do ((p = other) | (Sta.Dir.InvSet[p] = false)) endforall) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.Dir.Pending = false)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall)) ==>
begin
  Sta.Dir.Pending := false;
endrule;


rule "n_NI_InvAck_212_src_3"
  ((Sta.Dir.Pending = true) & (Sta.Dir.Local = false) & (Sta.Dir.HomeInvSet = false) & (forall p : NODE do ((p = other) | (Sta.Dir.InvSet[p] = false)) endforall) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get))) ==>
begin
  Sta.Dir.Pending := false;
endrule;


rule "n_NI_InvAck_113_src_3"
  ((Sta.Dir.Pending = true) & (Sta.Dir.Local = true) & (Sta.Dir.Dirty = false) & (Sta.Dir.HomeInvSet = false) & (forall p : NODE do ((p = other) | (Sta.Dir.InvSet[p] = false)) endforall) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(!(Sta.HomeProc.CacheData = Sta.CurrData))) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData))) & (!(Sta.Dir.Dirty = true))) ==>
begin
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
endrule;


ruleset src : NODE do
  rule "n_NI_InvAck_exists14_dst_3_src_22"
    ((Sta.InvMsg[src].Cmd = INV_InvAck) & (Sta.Dir.Pending = true) & (Sta.Dir.InvSet[src] = true) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get))) ==>
  begin
    Sta.InvMsg[src].Cmd := INV_None;
    Sta.Dir.InvSet[src] := false;
  endrule;
endruleset;


rule "n_NI_Remote_GetX_PutX_Home24_dst_3"
  ((Sta.HomeUniMsg.Cmd = UNI_GetX) & (Sta.HomeUniMsg.Proc = other) & (Sta.HomeUniMsg.HomeProc = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = false)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.Pending = false)) & (!(Sta.Dir.Local = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.Local = true))) ==>
begin
  Sta.HomeUniMsg.Cmd := UNI_PutX;
  Sta.HomeUniMsg.Data := Sta.CurrData;
endrule;


rule "n_NI_Remote_GetX_PutX25_dst_4_src_3"
  ((!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.Dir.Pending = false)) & (forall p__Inv3 : NODE do (!(Sta.Dir.InvSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.HeadPtr = other)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.Local = true)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = false)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.Local = true))) ==>
begin
  Sta.ShWbMsg.Cmd := SHWB_FAck;
  Sta.ShWbMsg.Proc := other;
  Sta.ShWbMsg.HomeProc := false;
endrule;


ruleset src : NODE do
  rule "n_NI_Remote_GetX_PutX25_dst_3_src_22"
    ((!(src = other)) & (Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].Proc = other) & (Sta.UniMsg[src].HomeProc = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.Dir.Pending = false)) & (forall p__Inv3 : NODE do (!(Sta.Dir.InvSet[p__Inv3] = true)) endforall) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.Local = true)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = false)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.Local = true))) ==>
  begin
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.CurrData;
    Sta.ShWbMsg.Cmd := SHWB_FAck;
    Sta.ShWbMsg.Proc := src;
    Sta.ShWbMsg.HomeProc := false;
  endrule;
endruleset;


rule "n_NI_Remote_GetX_Nak_Home26_dst_3"
  ((Sta.HomeUniMsg.Cmd = UNI_GetX) & (Sta.HomeUniMsg.Proc = other) & (Sta.HomeUniMsg.HomeProc = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.Pending = false)) & (!(Sta.Dir.Local = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (!(Sta.HomeProc.CacheState = CACHE_S))) ==>
begin
  Sta.HomeUniMsg.Cmd := UNI_Nak;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
endrule;


rule "n_NI_Remote_GetX_Nak27_dst_4_src_3"
  ((!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.Pending = false)) & (!(Sta.Dir.Local = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.InvSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.HeadPtr = other)) & (!(Sta.HomeProc.CacheState = CACHE_S))) ==>
begin
  Sta.NakcMsg.Cmd := NAKC_Nakc;
endrule;


ruleset dst : NODE do
  rule "n_NI_Remote_GetX_Nak27_dst_2_src_32"
    ((!(Sta.Proc[dst].CacheState = CACHE_E)) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.Pending = false)) & (!(Sta.Dir.Local = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.InvSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.HeadPtr = other)) & (!(Sta.HomeProc.CacheState = CACHE_S))) ==>
  begin
    Sta.NakcMsg.Cmd := NAKC_Nakc;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Remote_GetX_Nak27_dst_3_src_22"
    ((!(src = other)) & (Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].Proc = other) & (Sta.UniMsg[src].HomeProc = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.Pending = false)) & (!(Sta.Dir.Local = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.InvSet[p__Inv3] = true)) endforall) & (!(Sta.HomeProc.CacheState = CACHE_S))) ==>
  begin
    Sta.UniMsg[src].Cmd := UNI_Nak;
    Sta.UniMsg[src].Proc := other;
    Sta.UniMsg[src].HomeProc := false;
    Sta.NakcMsg.Cmd := NAKC_Nakc;
  endrule;
endruleset;


rule "n_NI_Local_GetX_PutX_1128_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = true) & (Sta.Dir.Local = true) & (Sta.HomeProc.CacheState = CACHE_E) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.Dir.Dirty = false)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(!(Sta.HomeProc.CacheData = Sta.CurrData))) & (!(Sta.HomeProc.CacheState = CACHE_I)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall)) ==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := other;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;


rule "n_NI_Local_GetX_PutX_1029_dst_4_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = other) & (Sta.Dir.HomeHeadPtr = false) & (Sta.Dir.Local = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := other;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ((((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
endrule;


ruleset dst : NODE do
  rule "n_NI_Local_GetX_PutX_1029_dst_2_src_32"
    ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = other) & (Sta.Dir.HomeHeadPtr = false) & (Sta.Dir.ShrSet[dst] = true) & (Sta.Dir.Local = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := other;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_1029_dst_3_src_22"
    ((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true) & (Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = src) & (Sta.Dir.HomeHeadPtr = false) & (Sta.Dir.Local = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
  endrule;
endruleset;


rule "n_NI_Local_GetX_PutX_931_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = true) & (!(Sta.Dir.HeadPtr = other)) & (Sta.Dir.Local = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := other;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ((((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
endrule;


rule "n_NI_Local_GetX_PutX_834_dst_4_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = other) & (Sta.Dir.HomeHeadPtr = false) & (Sta.Dir.Local = true) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(!(Sta.HomeProc.CacheData = Sta.CurrData))) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := other;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ((((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;


ruleset dst : NODE do
  rule "n_NI_Local_GetX_PutX_834_dst_2_src_32"
    ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = other) & (Sta.Dir.HomeHeadPtr = false) & (Sta.Dir.ShrSet[dst] = true) & (Sta.Dir.Local = true) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(!(Sta.HomeProc.CacheData = Sta.CurrData))) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := other;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.HomeProc.CacheState := CACHE_I;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Local_GetX_PutX_834_dst_3_src_22"
    ((Sta.UniMsg[src].Cmd = UNI_GetX) & (Sta.UniMsg[src].HomeProc = true) & (Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = src) & (Sta.Dir.HomeHeadPtr = false) & (Sta.Dir.Local = true) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(!(Sta.HomeProc.CacheData = Sta.CurrData))) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
  begin
    Sta.Dir.Pending := true;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := true;
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ((!(p = src)) & (((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      endif;
    endfor;
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
    Sta.HomeInvMsg.Cmd := INV_None;
    Sta.UniMsg[src].Cmd := UNI_PutX;
    Sta.UniMsg[src].Data := Sta.MemData;
    Sta.HomeProc.CacheState := CACHE_I;
  endrule;
endruleset;


rule "n_NI_Local_GetX_PutX_739_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = true) & (!(Sta.Dir.HeadPtr = other)) & (Sta.Dir.Local = true) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(!(Sta.HomeProc.CacheData = Sta.CurrData))) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := other;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ((((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;


rule "n_NI_Local_GetX_PutX_740_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = true) & (Sta.Dir.HomeHeadPtr = false) & (Sta.Dir.Local = true) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(!(Sta.HomeProc.CacheData = Sta.CurrData))) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := other;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ((((Sta.Dir.ShrVld = true) & (Sta.Dir.ShrSet[p] = true)) | (((Sta.Dir.HeadVld = true) & (Sta.Dir.HeadPtr = p)) & (Sta.Dir.HomeHeadPtr = false)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;


rule "n_NI_Local_GetX_PutX_641_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadPtr = other) & (Sta.Dir.HomeHeadPtr = false) & (Sta.Dir.HomeShrSet = false) & (forall p : NODE do ((!(p = other)) -> (Sta.Dir.ShrSet[p] = false)) endforall) & (Sta.Dir.Local = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := other;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;


rule "n_NI_Local_GetX_PutX_542_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadPtr = other) & (Sta.Dir.HomeHeadPtr = false) & (Sta.Dir.HomeShrSet = false) & (forall p : NODE do ((!(p = other)) -> (Sta.Dir.ShrSet[p] = false)) endforall) & (Sta.Dir.Local = true) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(!(Sta.HomeProc.CacheData = Sta.CurrData))) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := other;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;


rule "n_NI_Local_GetX_PutX_344_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = false) & (Sta.Dir.Local = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := other;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;


rule "n_NI_Local_GetX_PutX_245_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = false) & (Sta.Dir.Local = true) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(!(Sta.HomeProc.CacheData = Sta.CurrData))) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := other;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;


rule "n_NI_Local_GetX_GetX47_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = true) & (Sta.Dir.Local = false) & (!(Sta.Dir.HeadPtr = other)) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall)) ==>
begin
  Sta.Dir.Pending := true;
endrule;


rule "n_NI_Local_GetX_GetX48_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = true) & (Sta.Dir.Local = false) & (Sta.Dir.HomeHeadPtr = true) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.Dir.HeadVld = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall)) ==>
begin
  Sta.Dir.Pending := true;
endrule;


rule "n_NI_Remote_Get_Put_Home52_dst_3"
  ((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.HomeUniMsg.Proc = other) & (Sta.HomeUniMsg.HomeProc = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = false)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.Pending = false)) & (!(Sta.Dir.Local = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.Local = true))) ==>
begin
  Sta.HomeUniMsg.Cmd := UNI_Put;
  Sta.HomeUniMsg.Data := Sta.CurrData;
endrule;


rule "n_NI_Remote_Get_Put53_dst_4_src_3"
  ((!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.Dir.Pending = false)) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.HeadPtr = other)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.Local = true)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = false)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.Local = true))) ==>
begin
  Sta.ShWbMsg.Cmd := SHWB_ShWb;
  Sta.ShWbMsg.Proc := other;
  Sta.ShWbMsg.HomeProc := false;
  Sta.ShWbMsg.Data := Sta.CurrData;
endrule;


ruleset src : NODE do
  rule "n_NI_Remote_Get_Put53_dst_3_src_22"
    ((!(src = other)) & (Sta.UniMsg[src].Cmd = UNI_Get) & (Sta.UniMsg[src].Proc = other) & (Sta.UniMsg[src].HomeProc = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.Dir.Pending = false)) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.Local = true)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = false)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.Local = true))) ==>
  begin
    Sta.UniMsg[src].Cmd := UNI_Put;
    Sta.UniMsg[src].Data := Sta.CurrData;
    Sta.ShWbMsg.Cmd := SHWB_ShWb;
    Sta.ShWbMsg.Proc := src;
    Sta.ShWbMsg.HomeProc := false;
    Sta.ShWbMsg.Data := Sta.CurrData;
  endrule;
endruleset;


rule "n_NI_Remote_Get_Nak_Home54_dst_3"
  ((Sta.HomeUniMsg.Cmd = UNI_Get) & (Sta.HomeUniMsg.Proc = other) & (Sta.HomeUniMsg.HomeProc = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.Pending = false)) & (!(Sta.Dir.Local = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (!(Sta.HomeProc.CacheState = CACHE_S))) ==>
begin
  Sta.HomeUniMsg.Cmd := UNI_Nak;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
endrule;


rule "n_NI_Remote_Get_Nak55_dst_4_src_3"
  ((!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.Pending = false)) & (!(Sta.Dir.Local = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.HeadPtr = other)) & (!(Sta.HomeProc.CacheState = CACHE_S))) ==>
begin
  Sta.NakcMsg.Cmd := NAKC_Nakc;
endrule;


ruleset dst : NODE do
  rule "n_NI_Remote_Get_Nak55_dst_2_src_32"
    ((!(Sta.Proc[dst].CacheState = CACHE_E)) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.Pending = false)) & (!(Sta.Dir.Local = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.HeadPtr = other)) & (!(Sta.HomeProc.CacheState = CACHE_S))) ==>
  begin
    Sta.NakcMsg.Cmd := NAKC_Nakc;
  endrule;
endruleset;


ruleset src : NODE do
  rule "n_NI_Remote_Get_Nak55_dst_3_src_22"
    ((!(src = other)) & (Sta.UniMsg[src].Cmd = UNI_Get) & (Sta.UniMsg[src].Proc = other) & (Sta.UniMsg[src].HomeProc = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.Pending = false)) & (!(Sta.Dir.Local = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (!(Sta.HomeProc.CacheState = CACHE_S))) ==>
  begin
    Sta.UniMsg[src].Cmd := UNI_Nak;
    Sta.UniMsg[src].Proc := other;
    Sta.UniMsg[src].HomeProc := false;
    Sta.NakcMsg.Cmd := NAKC_Nakc;
  endrule;
endruleset;


rule "n_NI_Local_Get_Put_Dirty56_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = true) & (Sta.Dir.Local = true) & (Sta.HomeProc.CacheState = CACHE_E) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.Dir.Dirty = false)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(!(Sta.HomeProc.CacheData = Sta.CurrData))) & (!(Sta.HomeProc.CacheState = CACHE_I)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall)) ==>
begin
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := other;
  Sta.Dir.HomeHeadPtr := false;
  Sta.MemData := Sta.HomeProc.CacheData;
  Sta.HomeProc.CacheState := CACHE_S;
endrule;


rule "n_NI_Local_Get_Put57_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = false) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
begin
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := other;
  Sta.Dir.HomeHeadPtr := false;
endrule;


rule "n_NI_Local_Get_Put_Head58_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = true) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(!(Sta.MemData = Sta.CurrData)))) ==>
begin
  Sta.Dir.ShrVld := true;
  for p : NODE do
    if false then
      Sta.Dir.InvSet[p] := true;
else
      Sta.Dir.InvSet[p] := Sta.Dir.ShrSet[p];
    endif;
  endfor;
  Sta.Dir.HomeInvSet := Sta.Dir.HomeShrSet;
endrule;


rule "n_NI_Local_Get_Get59_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = true) & (Sta.Dir.Local = false) & (!(Sta.Dir.HeadPtr = other)) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall)) ==>
begin
  Sta.Dir.Pending := true;
endrule;


rule "n_NI_Local_Get_Get60_src_3"
  ((Sta.Dir.Pending = false) & (Sta.Dir.Dirty = true) & (Sta.Dir.Local = false) & (Sta.Dir.HomeHeadPtr = true) & (!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.NakcMsg.Cmd = NAKC_Nakc)) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeUniMsg.Cmd = UNI_GetX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Get)) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.Dir.HeadVld = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (forall p__Inv4 : NODE do (!(Sta.Dir.InvSet[p__Inv4] = true)) endforall) & (forall p__Inv4 : NODE do (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall)) ==>
begin
  Sta.Dir.Pending := true;
endrule;


rule "n_PI_Remote_PutX71_dst_3"
  ((!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.Local = true)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = false)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.Local = true))) ==>
begin
  Sta.WbMsg.Cmd := WB_Wb;
  Sta.WbMsg.Proc := other;
  Sta.WbMsg.HomeProc := false;
  Sta.WbMsg.Data := Sta.CurrData;
endrule;


ruleset data : DATA do
  rule "n_Store86_src_3"
    ((!(Sta.HomeProc.InvMarked = true)) & (!(Sta.Dir.HomeShrSet = true)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall p__Inv3 : NODE do (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall p__Inv4 : NODE do (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv3 : NODE do (!(Sta.Dir.ShrSet[p__Inv3] = true)) endforall) & (!(Sta.Dir.Local = true)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.Dir.HeadVld = false)) & (!(Sta.Dir.Dirty = false)) & (!(Sta.Dir.HomeHeadPtr = true)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.Dir.ShrVld = true)) & (forall p__Inv4 : NODE do (!(Sta.Dir.ShrSet[p__Inv4] = true)) endforall) & (!(Sta.Dir.Local = true))) ==>
  begin
    Sta.CurrData := data;
  endrule;
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__1622"
    (((Sta.Dir.HeadVld = false)) -> (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__15911"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.Dir.HeadPtr = p__Inv4)) -> (!(Sta.UniMsg[p__Inv4].HomeProc = false)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__15912"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.HeadPtr = p__Inv4)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__15813"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.Local = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__15815"
    (((Sta.Dir.Local = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX)) -> (!(Sta.UniMsg[p__Inv4].HomeProc = false)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__15716"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.ShrVld = true)));
endruleset;


ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv_inv__15619"
    ((!(p__Inv3 = p__Inv4)) -> (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.ShrSet[p__Inv3] = true))));
endruleset;


ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv_inv__15621"
    ((!(p__Inv3 = p__Inv4)) -> (((Sta.Dir.ShrSet[p__Inv3] = true) & (Sta.UniMsg[p__Inv4].Cmd = UNI_GetX)) -> (!(Sta.UniMsg[p__Inv4].HomeProc = false))));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__15522"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.ShrSet[p__Inv4] = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__15425"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.Dir.HeadVld = false)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__15426"
    (((Sta.Dir.HeadVld = false)) -> (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__15133"
    (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.WbMsg.Cmd = WB_Wb)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__15035"
    (((Sta.Dir.HomeHeadPtr = true)) -> (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__14839"
    (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)));
endruleset;


ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv_inv__14741"
    ((!(p__Inv3 = p__Inv4)) -> (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX))));
endruleset;


invariant "inv_inv__14643"
  (((Sta.Dir.HomeHeadPtr = true)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__14546"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.ShWbMsg.Cmd = SHWB_FAck)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__14449"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.NakcMsg.Cmd = NAKC_Nakc)));
endruleset;


invariant "inv_inv__14350"
  (((Sta.Dir.Local = true)) -> (!(Sta.ShWbMsg.Cmd = SHWB_FAck)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__14155"
    (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.ShWbMsg.Cmd = SHWB_FAck)));
endruleset;


ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv_inv__14056"
    ((!(p__Inv3 = p__Inv4)) -> (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.InvSet[p__Inv3] = true))));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__13959"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.InvSet[p__Inv4] = true)));
endruleset;


invariant "inv_inv__13862"
  (((Sta.Dir.Local = true)) -> (!(Sta.NakcMsg.Cmd = NAKC_Nakc)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__13667"
    (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.NakcMsg.Cmd = NAKC_Nakc)));
endruleset;


invariant "inv_inv__13569"
  (((Sta.Dir.HeadVld = false)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));


invariant "inv_inv__13373"
  (((Sta.Dir.HeadVld = false)) -> (!(Sta.Dir.ShrVld = true)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__13275"
    (((Sta.Dir.HeadVld = false)) -> (!(Sta.Dir.ShrSet[p__Inv4] = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__13276"
    (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.Dir.HeadVld = false)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__13177"
    (((Sta.Dir.HomeHeadPtr = true)) -> (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__13178"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.Dir.HomeHeadPtr = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__13080"
    (((Sta.Dir.InvSet[p__Inv4] = true)) -> (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__12982"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.Dir.ShrVld = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__12883"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.Dir.ShrSet[p__Inv4] = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__12884"
    (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)));
endruleset;


ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv_inv__12785"
    ((!(p__Inv3 = p__Inv4)) -> (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.Dir.ShrSet[p__Inv3] = true))));
endruleset;


ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv_inv__12786"
    ((!(p__Inv3 = p__Inv4)) -> (((Sta.Dir.ShrSet[p__Inv3] = true)) -> (!(Sta.Proc[p__Inv4].CacheState = CACHE_E))));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__12688"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.Dir.Local = true)) -> (!(Sta.UniMsg[p__Inv4].HomeProc = false)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__12689"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.Local = true)));
endruleset;


ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv_inv__12592"
    ((!(p__Inv3 = p__Inv4)) -> (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.ShrSet[p__Inv3] = true))));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__12495"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.HeadPtr = p__Inv4)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__12398"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.ShrVld = true)));
endruleset;


invariant "inv_inv__12299"
  (((Sta.Dir.HomeHeadPtr = true)) -> (!(Sta.Dir.ShrVld = true)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__121103"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.ShrSet[p__Inv4] = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__117115"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.Dir.Pending = false)) -> (!(Sta.UniMsg[p__Inv4].HomeProc = false)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__117116"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.Pending = false)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__116118"
    (((Sta.Dir.InvSet[p__Inv4] = true)) -> (!(Sta.ShWbMsg.Cmd = SHWB_FAck)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__115120"
    (((Sta.Dir.InvSet[p__Inv4] = true)) -> (!(Sta.NakcMsg.Cmd = NAKC_Nakc)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__114121"
    (((Sta.Dir.Pending = false) & (Sta.Dir.HeadVld = false)) -> (!(Sta.Dir.InvSet[p__Inv4] = true)));
endruleset;


invariant "inv_inv__113124"
  (((Sta.Dir.Dirty = true)) -> (!(Sta.Dir.ShrVld = true)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__112126"
    (((Sta.Dir.Dirty = true)) -> (!(Sta.Dir.ShrSet[p__Inv4] = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__112127"
    (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.Dir.Dirty = true)));
endruleset;


invariant "inv_inv__111128"
  (((Sta.Dir.Pending = true)) -> (!(Sta.HomeProc.CacheState = CACHE_S)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__110130"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.UniMsg[p__Inv4].Cmd = UNI_GetX)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__110131"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX)) -> (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__109132"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.UniMsg[p__Inv4].Cmd = UNI_Get)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__109133"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get)) -> (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__108134"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_GetX)));
endruleset;


invariant "inv_inv__107138"
  (((Sta.HomeUniMsg.Cmd = UNI_GetX)) -> (!(Sta.Dir.ShrVld = true)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__106139"
    (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.HomeUniMsg.Cmd = UNI_GetX)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__106140"
    (((Sta.HomeUniMsg.Cmd = UNI_GetX)) -> (!(Sta.Dir.ShrSet[p__Inv4] = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__105141"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__103146"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.Dir.InvSet[p__Inv4] = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__103147"
    (((Sta.Dir.InvSet[p__Inv4] = true)) -> (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__102148"
    (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__101152"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__100155"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.ShWbMsg.Cmd = SHWB_FAck)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__99158"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.NakcMsg.Cmd = NAKC_Nakc)));
endruleset;


ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv_inv__98161"
    ((!(p__Inv3 = p__Inv4)) -> (((Sta.UniMsg[p__Inv3].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv3].HomeProc = false)) -> (!(Sta.Dir.InvSet[p__Inv4] = true))));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__97164"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.InvSet[p__Inv4] = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__96165"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__95168"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__93173"
    (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));
endruleset;


invariant "inv_inv__92175"
  (((Sta.Dir.Pending = false)) -> (!(Sta.ShWbMsg.Cmd = SHWB_FAck)));


invariant "inv_inv__91177"
  (((Sta.Dir.Pending = false)) -> (!(Sta.NakcMsg.Cmd = NAKC_Nakc)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__90179"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Get)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__89182"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Get)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__88185"
    (((Sta.Dir.Dirty = true) & (Sta.Dir.Pending = false)) -> (!(Sta.Dir.InvSet[p__Inv4] = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__88187"
    (((Sta.Dir.InvSet[p__Inv4] = true) & (Sta.Dir.Dirty = true)) -> (!(Sta.Dir.Pending = false)));
endruleset;


invariant "inv_inv__87189"
  (((Sta.HomeUniMsg.Cmd = UNI_Get)) -> (!(Sta.Dir.ShrVld = true)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__86190"
    (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Get)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__86191"
    (((Sta.HomeUniMsg.Cmd = UNI_Get)) -> (!(Sta.Dir.ShrSet[p__Inv4] = true)));
endruleset;


invariant "inv_inv__85192"
  (((Sta.Dir.Local = false)) -> (!(Sta.HomeProc.CacheState = CACHE_S)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__84194"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_GetX) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__83197"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__81202"
    (((Sta.Dir.ShrSet[p__Inv4] = true)) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));
endruleset;


invariant "inv_inv__80205"
  (((Sta.HomeUniMsg.Cmd = UNI_GetX)) -> (!(Sta.ShWbMsg.Cmd = SHWB_FAck)));


invariant "inv_inv__79207"
  (((Sta.HomeUniMsg.Cmd = UNI_GetX)) -> (!(Sta.NakcMsg.Cmd = NAKC_Nakc)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__78208"
    (((Sta.Dir.InvSet[p__Inv4] = true)) -> (!(Sta.HomeUniMsg.Cmd = UNI_GetX)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__78209"
    (((Sta.HomeUniMsg.Cmd = UNI_GetX)) -> (!(Sta.Dir.InvSet[p__Inv4] = true)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__77210"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_GetX)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__75215"
    (((Sta.Dir.InvSet[p__Inv4] = true)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__74217"
    (((Sta.UniMsg[p__Inv4].Cmd = UNI_Get) & (Sta.UniMsg[p__Inv4].HomeProc = false)) -> (!(Sta.Dir.Pending = false)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__74219"
    (((Sta.Dir.Pending = false) & (Sta.UniMsg[p__Inv4].Cmd = UNI_Get)) -> (!(Sta.UniMsg[p__Inv4].HomeProc = false)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__71224"
    (((Sta.Dir.InvSet[p__Inv4] = true)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));
endruleset;


invariant "inv_inv__70227"
  (((Sta.HomeUniMsg.Cmd = UNI_Get)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));


invariant "inv_inv__69229"
  (((Sta.HomeUniMsg.Cmd = UNI_Get)) -> (!(Sta.ShWbMsg.Cmd = SHWB_FAck)));


invariant "inv_inv__68231"
  (((Sta.HomeUniMsg.Cmd = UNI_Get)) -> (!(Sta.NakcMsg.Cmd = NAKC_Nakc)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__67232"
    (((Sta.Dir.InvSet[p__Inv4] = true)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Get)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__67233"
    (((Sta.HomeUniMsg.Cmd = UNI_Get)) -> (!(Sta.Dir.InvSet[p__Inv4] = true)));
endruleset;


invariant "inv_inv__66235"
  (((Sta.Dir.Dirty = true)) -> (!(Sta.HomeProc.CacheState = CACHE_S)));


invariant "inv_inv__65236"
  (((Sta.HomeUniMsg.Cmd = UNI_Get)) -> (!(Sta.Dir.Local = true)));


invariant "inv_inv__65237"
  (((Sta.Dir.Local = true)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Get)));


invariant "inv_inv__63240"
  (((Sta.Dir.Dirty = true) & (Sta.HomeProc.CacheState = CACHE_I)) -> (!(Sta.Dir.Local = true)));


invariant "inv_inv__63241"
  (((Sta.Dir.Local = true) & (Sta.HomeProc.CacheState = CACHE_I)) -> (!(Sta.Dir.Dirty = true)));


invariant "inv_inv__63242"
  (((Sta.Dir.Local = true) & (Sta.Dir.Dirty = true)) -> (!(Sta.HomeProc.CacheState = CACHE_I)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__60247"
    (((Sta.Dir.InvSet[p__Inv4] = true)) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));
endruleset;


invariant "inv_inv__59249"
  (((Sta.HomeUniMsg.Cmd = UNI_GetX)) -> (!(Sta.Dir.Pending = false)));


invariant "inv_inv__59250"
  (((Sta.Dir.Pending = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_GetX)));


invariant "inv_inv__58251"
  (((Sta.HomeUniMsg.Cmd = UNI_GetX)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));


invariant "inv_inv__57253"
  (((Sta.Dir.Pending = false)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));


invariant "inv_inv__53261"
  (((Sta.Dir.Pending = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));


invariant "inv_inv__52263"
  (((Sta.Dir.Pending = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Get)));


invariant "inv_inv__52264"
  (((Sta.HomeUniMsg.Cmd = UNI_Get)) -> (!(Sta.Dir.Pending = false)));


invariant "inv_inv__51265"
  (((Sta.HomeUniMsg.Cmd = UNI_GetX)) -> (!(Sta.HomeProc.CacheState = CACHE_E)));


invariant "inv_inv__51266"
  (((Sta.HomeProc.CacheState = CACHE_E)) -> (!(Sta.HomeUniMsg.Cmd = UNI_GetX)));


invariant "inv_inv__50267"
  (((Sta.HomeUniMsg.Cmd = UNI_GetX)) -> (!(Sta.Dir.Local = true)));


invariant "inv_inv__50268"
  (((Sta.Dir.Local = true)) -> (!(Sta.HomeUniMsg.Cmd = UNI_GetX)));


invariant "inv_inv__49269"
  (((Sta.Dir.Local = true)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));


invariant "inv_inv__48271"
  (((Sta.Dir.Local = true)) -> (!(Sta.WbMsg.Cmd = WB_Wb)));


invariant "inv_inv__47273"
  (((Sta.Dir.Local = true)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));


invariant "inv_inv__46275"
  (((Sta.Dir.HomeHeadPtr = true)) -> (!(Sta.Dir.HeadVld = true)));


invariant "inv_inv__46276"
  (((Sta.Dir.HeadVld = true)) -> (!(Sta.Dir.HomeHeadPtr = true)));


invariant "inv_inv__45278"
  (((Sta.Dir.Local = true)) -> (!(Sta.HomeProc.ProcCmd = NODE_Get)));


invariant "inv_inv__44279"
  (((Sta.Dir.Pending = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));


invariant "inv_inv__42283"
  (((Sta.Dir.Dirty = false)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));


invariant "inv_inv__40287"
  (((Sta.Dir.Dirty = false)) -> (!(Sta.WbMsg.Cmd = WB_Wb)));


invariant "inv_inv__38291"
  (((Sta.Dir.Dirty = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));


invariant "inv_inv__37293"
  (((Sta.HomeUniMsg.Cmd = UNI_Get)) -> (!(Sta.HomeProc.CacheState = CACHE_E)));


invariant "inv_inv__37294"
  (((Sta.HomeProc.CacheState = CACHE_E)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Get)));


invariant "inv_inv__36295"
  (((Sta.HomeProc.CacheState = CACHE_E)) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));


invariant "inv_inv__35297"
  (((Sta.Dir.Local = true)) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__31305"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__30308"
    (((Sta.Dir.Local = true)) -> (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)));
endruleset;


invariant "inv_inv__28"
  (true -> (!(Sta.HomeProc.InvMarked = true)));


invariant "inv_inv__27312"
  (((Sta.Dir.Dirty = false)) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));


invariant "inv_inv__26313"
  (((Sta.HomeProc.CacheState = CACHE_E)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));


invariant "inv_inv__25315"
  (((Sta.HomeProc.CacheState = CACHE_E)) -> (!(Sta.WbMsg.Cmd = WB_Wb)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__24317"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(!(Sta.Proc[p__Inv4].CacheData = Sta.CurrData))));
endruleset;


invariant "inv_inv__23319"
  (((Sta.HomeProc.CacheState = CACHE_E)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__21324"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__20326"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.WbMsg.Cmd = WB_Wb)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__19328"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__17331"
    (((Sta.Dir.Dirty = false)) -> (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__15335"
    (((Sta.Dir.Local = true)) -> (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__15336"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.Dir.Local = true)));
endruleset;


invariant "inv_inv__14"
  (true -> (!(Sta.Dir.HomeShrSet = true)));


invariant "inv_inv__10343"
  (((Sta.HomeProc.CacheState = CACHE_E)) -> (!(!(Sta.HomeProc.CacheData = Sta.CurrData))));


invariant "inv_inv__9345"
  (((Sta.Dir.Local = true)) -> (!(!(Sta.HomeProc.CacheData = Sta.CurrData))));


invariant "inv_inv__8347"
  (((Sta.HomeProc.CacheState = CACHE_E)) -> (!(Sta.Dir.Dirty = false)));


invariant "inv_inv__8348"
  (((Sta.Dir.Dirty = false)) -> (!(Sta.HomeProc.CacheState = CACHE_E)));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__7350"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__6351"
    (((Sta.Dir.Dirty = false)) -> (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__6352"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.Dir.Dirty = false)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__5354"
    (((Sta.HomeProc.CacheState = CACHE_E)) -> (!(Sta.UniMsg[p__Inv4].Cmd = UNI_PutX)));
endruleset;


ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv_inv__4356"
    ((!(p__Inv3 = p__Inv4)) -> (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.UniMsg[p__Inv3].Cmd = UNI_PutX))));
endruleset;


invariant "inv_inv__3358"
  (((Sta.Dir.Dirty = false)) -> (!(!(Sta.MemData = Sta.CurrData))));


ruleset p__Inv4 : NODE do
  invariant "inv_inv__2359"
    (((Sta.HomeProc.CacheState = CACHE_E)) -> (!(Sta.Proc[p__Inv4].CacheState = CACHE_E)));
endruleset;


ruleset p__Inv4 : NODE do
  invariant "inv_inv__2360"
    (((Sta.Proc[p__Inv4].CacheState = CACHE_E)) -> (!(Sta.HomeProc.CacheState = CACHE_E)));
endruleset;


ruleset p__Inv3 : NODE; p__Inv4 : NODE do
  invariant "inv_inv__1361"
    ((!(p__Inv3 = p__Inv4)) -> (((Sta.Proc[p__Inv3].CacheState = CACHE_E)) -> (!(Sta.Proc[p__Inv4].CacheState = CACHE_E))));
endruleset;