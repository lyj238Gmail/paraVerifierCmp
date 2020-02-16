type
  
  NODE : scalarset(2);
  DATA : scalarset(2);


  CACHE_STATE : enum {CACHE_I, CACHE_S, CACHE_E};

  NODE_CMD : enum {NODE_None, NODE_Get, NODE_GetX};

  NODE_STATE : record
    ProcCmd : NODE_CMD;
    InvMarked : boolean;
    CacheState : CACHE_STATE;
    CacheData : DATA;
  end;

  DIR_STATE : record
    Pending : boolean;
    Local : boolean;
    Dirty : boolean;
    HeadVld : boolean;
    HeadPtr : NODE;
    HomeHeadPtr : boolean;
    ShrVld : boolean;
    ShrSet : array [NODE] of boolean;
    HomeShrSet : boolean;
    InvSet : array [NODE] of boolean;
    HomeInvSet : boolean;
  end;

  UNI_CMD : enum {UNI_None, UNI_Get, UNI_GetX, UNI_Put, UNI_PutX, UNI_Nak};

  UNI_MSG : record
    Cmd : UNI_CMD;
    Proc : NODE;
    HomeProc : boolean;
    Data : DATA;
  end;

  INV_CMD : enum {INV_None, INV_Inv, INV_InvAck};

  INV_MSG : record
    Cmd : INV_CMD;
  end;

  RP_CMD : enum {RP_None, RP_Replace};

  RP_MSG : record
    Cmd : RP_CMD;
  end;

  WB_CMD : enum {WB_None, WB_Wb};

  WB_MSG : record
    Cmd : WB_CMD;
    Proc : NODE;
    HomeProc : boolean;
    Data : DATA;
  end;

  SHWB_CMD : enum {SHWB_None, SHWB_ShWb, SHWB_FAck};

  SHWB_MSG : record
    Cmd : SHWB_CMD;
    Proc : NODE;
    HomeProc : boolean;
    Data : DATA;
  end;

  NAKC_CMD : enum {NAKC_None, NAKC_Nakc};

  NAKC_MSG : record
    Cmd : NAKC_CMD;
  end;

  STATE : record
    Proc : array [NODE] of NODE_STATE;
    HomeProc : NODE_STATE;
    Dir : DIR_STATE;
    MemData : DATA;
    UniMsg : array [NODE] of UNI_MSG;
    HomeUniMsg : UNI_MSG;
    InvMsg : array [NODE] of INV_MSG;
    HomeInvMsg : INV_MSG;
    RpMsg : array [NODE] of RP_MSG;
    HomeRpMsg : RP_MSG;
    WbMsg : WB_MSG;
    ShWbMsg : SHWB_MSG;
    NakcMsg : NAKC_MSG;
    CurrData : DATA;
  end;

var

  Sta : STATE;

ruleset src : NODE; d:DATA do
startstate
begin
  Sta.MemData := d;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := true;
  Sta.Dir.ShrVld := false;
  Sta.WbMsg.Cmd := WB_None;
  Sta.WbMsg.Proc := src;
  Sta.WbMsg.HomeProc := true;
  Sta.WbMsg.Data := d;
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.ShWbMsg.Proc := src;
  Sta.ShWbMsg.HomeProc := true;
  Sta.ShWbMsg.Data := d;
  Sta.NakcMsg.Cmd := NAKC_None;
  for p : NODE do
    Sta.Proc[p].ProcCmd := NODE_None;
    Sta.Proc[p].InvMarked := false;
    Sta.Proc[p].CacheState := CACHE_I;
    Sta.Proc[p].CacheData := d;
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
    Sta.UniMsg[p].Cmd := UNI_None;
   -- Sta.UniMsg[p].Proc := src;
    Sta.UniMsg[p].HomeProc := true;
    Sta.UniMsg[p].Data := d;
    Sta.InvMsg[p].Cmd := INV_None;
    Sta.RpMsg[p].Cmd := RP_None;
  endfor;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.HomeProc.CacheData := d;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.HomeUniMsg.Proc := src;
  Sta.HomeUniMsg.HomeProc := true;
  Sta.HomeUniMsg.Data := d;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.HomeRpMsg.Cmd := RP_None;
  Sta.CurrData := d;
endstartstate;
endruleset;

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
  ((Sta.Dir.Pending = true) & (Sta.Dir.Dirty = true) & (Sta.Dir.HomeInvSet = false) & (Sta.Dir.HomeHeadPtr = false) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall i : NODE do (!(Sta.Proc[i].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (Sta.HomeProc.InvMarked = false) & (Sta.Dir.ShrVld = false) & (forall i : NODE do (Sta.Dir.ShrSet[i] = false) endforall) & (Sta.Dir.HomeShrSet = false) & (Sta.Dir.HomeInvSet = false) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall i : NODE do (!(Sta.UniMsg[i].Cmd = UNI_PutX)) endforall) & (Sta.HomeProc.ProcCmd = NODE_None) & (Sta.HomeProc.CacheState = CACHE_E) & (Sta.HomeProc.CacheData = Sta.CurrData) & (Sta.Dir.Local = true) & (forall i : NODE do (Sta.Dir.InvSet[i] = false) endforall) & (Sta.Dir.HeadVld = false) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (!(Sta.HomeProc.CacheState = CACHE_I))) ==>
begin
  Sta.Dir.Pending := false;
endrule;


rule "n_NI_InvAck_113_src_3"
  ((Sta.Dir.Pending = true) & (Sta.Dir.Local = true) & (Sta.Dir.Dirty = false) & (Sta.Dir.HomeInvSet = false) & (Sta.Dir.ShrVld = false) & (forall i : NODE do (Sta.Dir.ShrSet[i] = false) endforall) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (Sta.Dir.HomeHeadPtr = false) & (forall i : NODE do (!(Sta.Proc[i].CacheState = CACHE_E)) endforall) & (Sta.MemData = Sta.CurrData) & (Sta.HomeProc.InvMarked = false) & (Sta.Dir.HomeShrSet = false) & (Sta.Dir.HomeInvSet = false) & (forall j : NODE do (!(Sta.UniMsg[j].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall j : NODE do (!(Sta.Proc[j].CacheState = CACHE_E)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_E)) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall i : NODE do (!(Sta.UniMsg[i].Cmd = UNI_PutX)) endforall) & (Sta.Dir.Local = true) & (forall i : NODE do (Sta.Dir.InvSet[i] = false) endforall) & (Sta.HomeProc.ProcCmd = NODE_None) & (!(Sta.ShWbMsg.Cmd = SHWB_FAck)) & (!(Sta.HomeProc.ProcCmd = NODE_Get)) & (Sta.HomeProc.CacheState = CACHE_I) & (Sta.Dir.HeadVld = false)) ==>
begin
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
endrule;


rule "n_NI_Remote_GetX_PutX_Home24_dst_3"
  ((Sta.HomeUniMsg.Cmd = UNI_GetX) & (Sta.HomeUniMsg.HomeProc = false) & (Sta.HomeProc.InvMarked = false) & (Sta.HomeProc.CacheState = CACHE_I) & (Sta.Dir.ShrVld = false) & (forall i : NODE do (Sta.Dir.ShrSet[i] = false) endforall) & (Sta.Dir.Local = false) & (forall j : NODE do (Sta.Dir.InvSet[j] = false) endforall) & (Sta.Dir.HomeShrSet = false) & (Sta.Dir.HomeInvSet = false) & (Sta.Dir.HomeHeadPtr = false) & (Sta.Dir.HeadVld = true) & (Sta.Dir.Dirty = true) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall i : NODE do (!(Sta.UniMsg[i].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall i : NODE do (!(Sta.Proc[i].CacheState = CACHE_E)) endforall) & (forall j : NODE do (!(Sta.InvMsg[j].Cmd = INV_InvAck)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.HomeProc.CacheState = CACHE_E))) ==>
begin
  Sta.HomeUniMsg.Cmd := UNI_PutX;
  Sta.HomeUniMsg.Data := Sta.CurrData;
endrule;


rule "n_NI_Remote_GetX_PutX25_dst_4_src_3"
  ((Sta.HomeProc.InvMarked = false) & (Sta.HomeProc.CacheState = CACHE_I) & (Sta.Dir.ShrVld = false) & (forall i : NODE do (Sta.Dir.ShrSet[i] = false) endforall) & (Sta.Dir.Local = false) & (forall j : NODE do (Sta.Dir.InvSet[j] = false) endforall) & (Sta.Dir.HomeShrSet = false) & (Sta.Dir.HomeInvSet = false) & (Sta.Dir.HomeHeadPtr = false) & (Sta.Dir.HeadVld = true) & (Sta.Dir.Dirty = true) & (!(Sta.WbMsg.Cmd = WB_Wb)) & (forall i : NODE do (!(Sta.UniMsg[i].Cmd = UNI_PutX)) endforall) & (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)) & (forall i : NODE do (!(Sta.Proc[i].CacheState = CACHE_E)) endforall) & (forall j : NODE do (!(Sta.InvMsg[j].Cmd = INV_InvAck)) endforall) & (!(Sta.HomeUniMsg.Cmd = UNI_PutX)) & (!(Sta.HomeUniMsg.Cmd = UNI_Put)) & (!(Sta.HomeProc.CacheState = CACHE_S)) & (!(Sta.HomeProc.CacheState = CACHE_E))) ==>
begin
  Sta.ShWbMsg.Cmd := SHWB_FAck;
  ---Sta.ShWbMsg.Proc := 3;
  Sta.ShWbMsg.HomeProc := false;
endrule;


ruleset j : NODE do
  invariant "inv_543"
    ((Sta.Dir.ShrSet[j] = true) -> (!(Sta.UniMsg[j].Cmd = UNI_PutX)));
endruleset;


ruleset i : NODE do
  invariant "inv_542"
    ((Sta.UniMsg[i].Cmd = UNI_GetX) -> (!(Sta.Proc[i].CacheState = CACHE_E)));
endruleset;


ruleset i : NODE do
  invariant "inv_541"
    (((Sta.Dir.Dirty = false) & (Sta.InvMsg[i].Cmd = INV_InvAck)) -> (!(Sta.HomeProc.ProcCmd = NODE_Get)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_540"
    ((Sta.InvMsg[j].Cmd = INV_InvAck) -> (Sta.Dir.ShrSet[i] = false));
endruleset;


ruleset i : NODE do
  invariant "inv_539"
    (((Sta.UniMsg[i].Cmd = UNI_Get) & (Sta.Dir.HeadVld = true)) -> (!(Sta.InvMsg[i].Cmd = INV_Inv)));
endruleset;


ruleset j : NODE do
  invariant "inv_538"
    ((Sta.Dir.ShrSet[j] = true) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_537"
    ((Sta.InvMsg[j].Cmd = INV_InvAck) -> (Sta.Dir.InvSet[i] = false));
endruleset;


invariant "inv_536"
  ((Sta.Dir.Local = true) -> (Sta.Dir.HomeInvSet = false));


ruleset j : NODE do
  invariant "inv_535"
    (((Sta.Dir.Pending = true) & (Sta.InvMsg[j].Cmd = INV_InvAck)) -> (Sta.Dir.HeadPtr = j));
endruleset;


ruleset j : NODE do
  invariant "inv_534"
    ((Sta.Dir.ShrSet[j] = true) -> (Sta.Dir.HomeShrSet = false));
endruleset;


ruleset i : NODE do
  invariant "inv_533"
    ((Sta.UniMsg[i].Cmd = UNI_GetX) -> (Sta.Proc[i].InvMarked = false));
endruleset;


ruleset j : NODE do
  invariant "inv_531"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (!(Sta.HomeProc.CacheState = CACHE_E)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_530"
    (((Sta.UniMsg[j].Cmd = UNI_Get) & (Sta.Proc[i].CacheState = CACHE_E)) -> (!(Sta.InvMsg[j].Cmd = INV_Inv)));
endruleset;


ruleset i : NODE do
  invariant "inv_529"
    ((Sta.UniMsg[i].Cmd = UNI_GetX) -> (!(Sta.Proc[i].CacheState = CACHE_S)));
endruleset;


invariant "inv_528"
  ((Sta.Dir.Local = false) -> (!(Sta.HomeProc.CacheState = CACHE_S)));


ruleset j : NODE do
  invariant "inv_527"
    (((Sta.Dir.Pending = true) & (Sta.Dir.InvSet[j] = true)) -> (!(Sta.HomeProc.ProcCmd = NODE_Get)));
endruleset;


invariant "inv_526"
  ((Sta.Dir.Dirty = false) -> (Sta.Dir.HomeShrSet = false));


ruleset j : NODE do
  invariant "inv_525"
    ((Sta.UniMsg[j].Cmd = UNI_Get) -> (Sta.Dir.HomeInvSet = false));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_522"
    (((Sta.Dir.Pending = true) & (Sta.InvMsg[j].Cmd = INV_InvAck)) -> (!(Sta.UniMsg[i].Cmd = UNI_PutX)));
endruleset;


ruleset i : NODE do
  invariant "inv_521"
    (((Sta.Dir.HeadVld = true) & (Sta.UniMsg[i].Cmd = UNI_GetX)) -> (!(Sta.InvMsg[i].Cmd = INV_InvAck)));
endruleset;


ruleset j : NODE do
  invariant "inv_520"
    ((Sta.UniMsg[j].Cmd = UNI_GetX) -> (Sta.Dir.HomeShrSet = false));
endruleset;


ruleset j : NODE do
  invariant "inv_517"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (Sta.Dir.InvSet[j] = false));
endruleset;


ruleset j : NODE do
  invariant "inv_516"
    ((Sta.UniMsg[j].Cmd = UNI_Get) -> (!(Sta.Proc[j].ProcCmd = NODE_GetX)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_515"
    ((Sta.Dir.ShrSet[j] = true) -> (!(Sta.InvMsg[i].Cmd = INV_InvAck)));
endruleset;


ruleset i : NODE do
  invariant "inv_514"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (!(Sta.Proc[i].ProcCmd = NODE_GetX)));
endruleset;


ruleset i : NODE do
  invariant "inv_513"
    ((Sta.Dir.InvSet[i] = true) -> (Sta.HomeProc.InvMarked = false));
endruleset;


ruleset i : NODE do
  invariant "inv_512"
    (((Sta.Dir.InvSet[i] = true) & (Sta.Dir.Dirty = true)) -> (Sta.HomeProc.ProcCmd = NODE_None));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_509"
    ((Sta.UniMsg[i].Proc = j) -> (Sta.Dir.HomeShrSet = false));
endruleset;


invariant "inv_508"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));


ruleset i : NODE do
  invariant "inv_507"
    ((Sta.Dir.ShrSet[i] = true) -> (Sta.Dir.HomeHeadPtr = false));
endruleset;


ruleset i : NODE do
  invariant "inv_505"
    ((Sta.Dir.HeadVld = false) -> (Sta.Dir.ShrSet[i] = false));
endruleset;


ruleset j : NODE do
  invariant "inv_503"
    ((Sta.InvMsg[j].Cmd = INV_InvAck) -> (Sta.Dir.ShrVld = false));
endruleset;


ruleset j : NODE do
  invariant "inv_502"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (!(Sta.UniMsg[j].Cmd = UNI_Get)));
endruleset;


ruleset i : NODE do
  invariant "inv_501"
    (((Sta.Dir.Pending = true) & (Sta.Dir.InvSet[i] = true)) -> (Sta.Dir.HeadVld = false));
endruleset;


ruleset i : NODE do
  invariant "inv_500"
    ((!(Sta.Proc[i].CacheState = CACHE_E)) -> (Sta.Dir.HomeShrSet = false));
endruleset;


ruleset i : NODE do
  invariant "inv_498"
    ((Sta.InvMsg[i].Cmd = INV_InvAck) -> (Sta.Dir.HomeInvSet = false));
endruleset;


invariant "inv_497"
  ((Sta.Dir.Pending = true) -> (Sta.HomeProc.InvMarked = false));


ruleset i : NODE; j : NODE do
  invariant "inv_496"
    ((Sta.Dir.ShrSet[i] = true) -> (!(Sta.InvMsg[j].Cmd = INV_Inv)));
endruleset;


ruleset j : NODE do
  invariant "inv_494"
    (((Sta.Dir.InvSet[j] = true) & (Sta.InvMsg[j].Cmd = INV_InvAck)) -> (Sta.HomeProc.ProcCmd = NODE_None));
endruleset;


ruleset j : NODE do
  invariant "inv_491"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (!(Sta.Proc[j].ProcCmd = NODE_Get)));
endruleset;


invariant "inv_490"
  ((Sta.Dir.HeadVld = true) -> (!(Sta.HomeProc.CacheState = CACHE_E)));


ruleset i : NODE do
  invariant "inv_489"
    ((Sta.Dir.ShrSet[i] = true) -> (!(Sta.HomeProc.CacheState = CACHE_E)));
endruleset;


ruleset j : NODE do
  invariant "inv_488"
    (((Sta.Dir.Pending = true) & (Sta.Dir.InvSet[j] = true)) -> (Sta.Dir.Local = true));
endruleset;


invariant "inv_487"
  ((!(Sta.HomeProc.ProcCmd = NODE_Get)) -> (Sta.Dir.HomeInvSet = false));


ruleset i : NODE do
  invariant "inv_486"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (Sta.Dir.HomeHeadPtr = false));
endruleset;


invariant "inv_485"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (!(Sta.HomeProc.ProcCmd = NODE_Get)));


ruleset j : NODE do
  invariant "inv_484"
    (((Sta.Dir.InvSet[j] = true) & (Sta.Dir.Dirty = true)) -> (Sta.Dir.Local = true));
endruleset;


invariant "inv_483"
  ((Sta.Dir.Local = true) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));


ruleset i : NODE do
  invariant "inv_482"
    ((Sta.UniMsg[i].HomeProc = false) -> (Sta.Dir.HomeInvSet = false));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_481"
    (((Sta.Dir.Pending = true) & (Sta.Dir.InvSet[j] = true)) -> (Sta.Dir.InvSet[i] = false));
endruleset;


invariant "inv_480"
  ((Sta.Dir.Pending = true) -> (Sta.Dir.ShrVld = false));


ruleset j : NODE do
  invariant "inv_479"
    ((Sta.Proc[j].ProcCmd = NODE_None) -> (Sta.Dir.HomeShrSet = false));
endruleset;


ruleset i : NODE do
  invariant "inv_478"
    (((Sta.Dir.Dirty = false) & (Sta.InvMsg[i].Cmd = INV_InvAck)) -> (Sta.Dir.HeadPtr = i));
endruleset;


ruleset i : NODE do
  invariant "inv_477"
    (((Sta.InvMsg[i].Cmd = INV_InvAck) & (Sta.Dir.Local = true)) -> (Sta.Dir.InvSet[i] = true));
endruleset;


ruleset j : NODE do
  invariant "inv_475"
    ((Sta.UniMsg[j].Cmd = UNI_GetX) -> (Sta.HomeProc.InvMarked = false));
endruleset;


ruleset i : NODE do
  invariant "inv_474"
    ((Sta.UniMsg[i].Cmd = UNI_Get) -> (!(Sta.Proc[i].CacheState = CACHE_S)));
endruleset;


invariant "inv_473"
  ((Sta.Dir.Dirty = false) -> (Sta.MemData = Sta.CurrData));


ruleset j : NODE do
  invariant "inv_472"
    ((Sta.Proc[j].ProcCmd = NODE_None) -> (!(Sta.UniMsg[j].Cmd = UNI_PutX)));
endruleset;


ruleset i : NODE do
  invariant "inv_471"
    (((Sta.Dir.InvSet[i] = true) & (Sta.Dir.Dirty = true)) -> (Sta.HomeProc.CacheState = CACHE_E));
endruleset;


ruleset i : NODE do
  invariant "inv_469"
    ((Sta.UniMsg[i].Cmd = UNI_GetX) -> (Sta.Dir.HomeInvSet = false));
endruleset;


ruleset j : NODE do
  invariant "inv_468"
    (((Sta.Dir.Pending = true) & (Sta.InvMsg[j].Cmd = INV_InvAck)) -> (!(Sta.WbMsg.Cmd = WB_Wb)));
endruleset;


ruleset j : NODE do
  invariant "inv_467"
    ((Sta.Dir.InvSet[j] = true) -> (Sta.Dir.HomeInvSet = false));
endruleset;


invariant "inv_466"
  (((Sta.Dir.HeadVld = true) & (Sta.Dir.Local = true)) -> (Sta.HomeProc.CacheData = Sta.CurrData));


ruleset i : NODE; j : NODE do
  invariant "inv_465"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (!(Sta.InvMsg[j].Cmd = INV_InvAck)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_464"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (Sta.Dir.ShrSet[i] = false));
endruleset;


ruleset j : NODE do
  invariant "inv_463"
    (((Sta.Dir.Pending = true) & (Sta.Dir.InvSet[j] = true)) -> (Sta.Dir.HeadPtr = j));
endruleset;


invariant "inv_462"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (Sta.Dir.HomeInvSet = false));


ruleset j : NODE do
  invariant "inv_459"
    ((Sta.InvMsg[j].Cmd = INV_InvAck) -> (Sta.Dir.HomeHeadPtr = false));
endruleset;


invariant "inv_456"
  (((Sta.Dir.HeadVld = true) & (Sta.Dir.Local = true)) -> (Sta.Dir.Dirty = false));


ruleset i : NODE do
  invariant "inv_455"
    ((Sta.Proc[i].ProcCmd = NODE_None) -> (!(Sta.UniMsg[i].Cmd = UNI_Nak)));
endruleset;


ruleset j : NODE do
  invariant "inv_453"
    ((Sta.Dir.ShrSet[j] = true) -> (Sta.Dir.Dirty = false));
endruleset;


ruleset i : NODE do
  invariant "inv_451"
    (((Sta.Dir.InvSet[i] = true) & (Sta.Dir.Dirty = true)) -> (!(Sta.HomeProc.ProcCmd = NODE_Get)));
endruleset;


invariant "inv_450"
  (((Sta.Dir.Local = true) & (Sta.Dir.Dirty = true)) -> (!(Sta.HomeProc.CacheState = CACHE_I)));


ruleset i : NODE do
  invariant "inv_448"
    ((Sta.UniMsg[i].HomeProc = true) -> (Sta.Dir.HomeInvSet = false));
endruleset;


ruleset j : NODE do
  invariant "inv_447"
    (((Sta.Dir.Pending = true) & (Sta.Dir.InvSet[j] = true)) -> (Sta.HomeProc.ProcCmd = NODE_None));
endruleset;


invariant "inv_446"
  (((Sta.Dir.Dirty = false) & (Sta.Dir.Pending = true)) -> (Sta.HomeProc.CacheState = CACHE_I));


ruleset j : NODE do
  invariant "inv_444"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (!(Sta.HomeProc.CacheState = CACHE_S)));
endruleset;


ruleset j : NODE do
  invariant "inv_443"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (Sta.Dir.Local = false));
endruleset;


ruleset i : NODE do
  invariant "inv_442"
    ((Sta.Dir.InvSet[i] = true) -> (!(Sta.UniMsg[i].Cmd = UNI_PutX)));
endruleset;


ruleset i : NODE do
  invariant "inv_441"
    ((Sta.Dir.InvSet[i] = true) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));
endruleset;


ruleset j : NODE do
  invariant "inv_440"
    ((Sta.Dir.ShrSet[j] = true) -> (Sta.Dir.Pending = false));
endruleset;


ruleset j : NODE do
  invariant "inv_438"
    (((Sta.Dir.InvSet[j] = true) & (Sta.Dir.Dirty = true)) -> (!(Sta.HomeProc.CacheState = CACHE_I)));
endruleset;


ruleset i : NODE do
  invariant "inv_436"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (!(Sta.UniMsg[i].Cmd = UNI_PutX)));
endruleset;


invariant "inv_434"
  (((Sta.Dir.HeadVld = false) & (Sta.Dir.Local = false)) -> (Sta.Dir.Dirty = false));


ruleset i : NODE do
  invariant "inv_433"
    ((Sta.UniMsg[i].Cmd = UNI_GetX) -> (Sta.Proc[i].CacheState = CACHE_I));
endruleset;


ruleset j : NODE do
  invariant "inv_432"
    ((Sta.Dir.ShrSet[j] = true) -> (Sta.Dir.HeadVld = true));
endruleset;


ruleset j : NODE do
  invariant "inv_431"
    ((Sta.Proc[j].ProcCmd = NODE_None) -> (Sta.Proc[j].InvMarked = false));
endruleset;


invariant "inv_430"
  ((Sta.Dir.HeadVld = true) -> (Sta.Dir.HomeHeadPtr = false));


ruleset i : NODE do
  invariant "inv_429"
    ((Sta.Dir.ShrSet[i] = true) -> (Sta.HomeProc.InvMarked = false));
endruleset;


ruleset j : NODE do
  invariant "inv_427"
    ((Sta.UniMsg[j].Cmd = UNI_Get) -> (!(Sta.Proc[j].ProcCmd = NODE_None)));
endruleset;


ruleset i : NODE do
  invariant "inv_424"
    (((Sta.InvMsg[i].Cmd = INV_InvAck) & (Sta.Dir.Local = true)) -> (Sta.Dir.HeadPtr = i));
endruleset;


ruleset i : NODE do
  invariant "inv_423"
    (((Sta.Dir.ShrSet[i] = true) & (Sta.Dir.Local = true)) -> (Sta.HomeProc.CacheData = Sta.CurrData));
endruleset;


ruleset j : NODE do
  invariant "inv_422"
    ((Sta.Dir.ShrSet[j] = true) -> (Sta.Dir.HomeInvSet = false));
endruleset;


invariant "inv_421"
  (((Sta.Dir.Pending = true) & (Sta.Dir.Local = true)) -> (Sta.Dir.HeadVld = false));


ruleset j : NODE do
  invariant "inv_420"
    ((Sta.Dir.HeadVld = false) -> (!(Sta.UniMsg[j].Cmd = UNI_PutX)));
endruleset;


invariant "inv_418"
  ((Sta.Dir.Dirty = true) -> (Sta.Dir.ShrVld = false));


ruleset i : NODE do
  invariant "inv_414"
    (((Sta.Dir.Dirty = false) & (Sta.InvMsg[i].Cmd = INV_InvAck)) -> (!(Sta.ShWbMsg.Cmd = SHWB_FAck)));
endruleset;


ruleset i : NODE do
  invariant "inv_413"
    (((Sta.Dir.ShrSet[i] = true) & (Sta.Dir.Local = true)) -> (!(Sta.ShWbMsg.Cmd = SHWB_FAck)));
endruleset;


ruleset j : NODE do
  invariant "inv_411"
    ((Sta.Dir.InvSet[j] = true) -> (Sta.Dir.HomeShrSet = false));
endruleset;


invariant "inv_410"
  ((Sta.Dir.Dirty = true) -> (Sta.Dir.HomeInvSet = false));


ruleset j : NODE do
  invariant "inv_406"
    ((Sta.UniMsg[j].Cmd = UNI_GetX) -> (!(Sta.Proc[j].ProcCmd = NODE_None)));
endruleset;


invariant "inv_405"
  (((Sta.Dir.Local = true) & (Sta.Dir.Dirty = true)) -> (Sta.Dir.HeadVld = false));


ruleset i : NODE do
  invariant "inv_404"
    ((Sta.Dir.InvSet[i] = true) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));
endruleset;


ruleset j : NODE do
  invariant "inv_403"
    ((!(Sta.RpMsg[j].Cmd = RP_Replace)) -> (Sta.Dir.HomeInvSet = false));
endruleset;


ruleset i : NODE do
  invariant "inv_402"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (!(Sta.UniMsg[i].Cmd = UNI_Put)));
endruleset;


invariant "inv_400"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (Sta.HomeProc.InvMarked = false));


invariant "inv_398"
  (((Sta.Dir.HeadVld = true) & (Sta.Dir.Local = true)) -> (Sta.MemData = Sta.CurrData));


invariant "inv_395"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (!(Sta.WbMsg.Cmd = WB_Wb)));


invariant "inv_394"
  ((Sta.Dir.HomeInvSet = false) -> (Sta.HomeProc.InvMarked = false));


ruleset i : NODE do
  invariant "inv_393"
    ((Sta.HomeProc.CacheState = CACHE_E) -> (Sta.Dir.ShrSet[i] = false));
endruleset;


ruleset i : NODE do
  invariant "inv_392"
    ((Sta.InvMsg[i].Cmd = INV_InvAck) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));
endruleset;


ruleset i : NODE do
  invariant "inv_391"
    ((Sta.Dir.HeadPtr = i) -> (Sta.Dir.HomeShrSet = false));
endruleset;


ruleset j : NODE do
  invariant "inv_390"
    ((Sta.Dir.ShrSet[j] = true) -> (Sta.Dir.ShrVld = true));
endruleset;


ruleset j : NODE do
  invariant "inv_389"
    ((Sta.Dir.Local = true) -> (!(Sta.UniMsg[j].Cmd = UNI_PutX)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_387"
    (((Sta.Dir.InvSet[j] = true) & (Sta.Dir.Dirty = true)) -> (Sta.Dir.InvSet[i] = false));
endruleset;


ruleset j : NODE do
  invariant "inv_386"
    ((Sta.Dir.InvSet[j] = true) -> (!(Sta.Proc[j].CacheState = CACHE_E)));
endruleset;


invariant "inv_385"
  ((Sta.Dir.Pending = true) -> (!(Sta.HomeProc.CacheState = CACHE_S)));


ruleset i : NODE do
  invariant "inv_384"
    ((Sta.InvMsg[i].Cmd = INV_InvAck) -> (Sta.Dir.ShrSet[i] = false));
endruleset;


invariant "inv_382"
  ((Sta.Dir.Dirty = false) -> (!(Sta.HomeProc.CacheState = CACHE_E)));


ruleset i : NODE; j : NODE do
  invariant "inv_381"
    (((Sta.UniMsg[j].Cmd = UNI_GetX) & (Sta.Dir.ShrSet[i] = true)) -> (!(Sta.ShWbMsg.Cmd = SHWB_FAck)));
endruleset;


invariant "inv_380"
  ((Sta.Dir.HomeHeadPtr = false) -> (Sta.Dir.HomeShrSet = false));


invariant "inv_377"
  ((Sta.Dir.Dirty = true) -> (Sta.Dir.HomeShrSet = false));


ruleset j : NODE do
  invariant "inv_376"
    (((Sta.Dir.InvSet[j] = true) & (Sta.Dir.Dirty = true)) -> (Sta.HomeProc.CacheData = Sta.CurrData));
endruleset;


ruleset i : NODE do
  invariant "inv_375"
    ((Sta.InvMsg[i].Cmd = INV_InvAck) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));
endruleset;


invariant "inv_374"
  ((Sta.Dir.HeadVld = false) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));


ruleset i : NODE; j : NODE do
  invariant "inv_373"
    ((Sta.Dir.InvSet[j] = true) -> (!(Sta.UniMsg[i].Cmd = UNI_PutX)));
endruleset;


invariant "inv_371"
  (((Sta.Dir.Local = true) & (Sta.Dir.Dirty = true)) -> (Sta.HomeProc.CacheData = Sta.CurrData));


ruleset i : NODE do
  invariant "inv_370"
    (((Sta.InvMsg[i].Cmd = INV_InvAck) & (Sta.Dir.InvSet[i] = true)) -> (Sta.Dir.HeadPtr = i));
endruleset;


ruleset i : NODE do
  invariant "inv_367"
    ((Sta.UniMsg[i].HomeProc = true) -> (!(Sta.Proc[i].CacheState = CACHE_E)));
endruleset;


invariant "inv_366"
  (((Sta.Dir.Local = false) & (Sta.Dir.Dirty = true)) -> (Sta.Dir.HomeHeadPtr = false));


ruleset j : NODE do
  invariant "inv_365"
    ((Sta.Dir.HeadPtr = j) -> (Sta.Dir.HomeInvSet = false));
endruleset;


ruleset j : NODE do
  invariant "inv_364"
    ((Sta.Dir.Dirty = false) -> (!(Sta.Proc[j].CacheState = CACHE_E)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_363"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (!(Sta.Proc[i].CacheState = CACHE_E)));
endruleset;


invariant "inv_362"
  ((!(Sta.HomeProc.ProcCmd = NODE_Get)) -> (Sta.HomeProc.InvMarked = false));


ruleset i : NODE do
  invariant "inv_361"
    ((!(Sta.RpMsg[i].Cmd = RP_Replace)) -> (Sta.Dir.HomeShrSet = false));
endruleset;


ruleset i : NODE do
  invariant "inv_360"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (Sta.Dir.HeadVld = true));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_357"
    ((Sta.Dir.InvSet[j] = true) -> (!(Sta.Proc[i].CacheState = CACHE_E)));
endruleset;


ruleset i : NODE do
  invariant "inv_356"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (Sta.UniMsg[i].HomeProc = false));
endruleset;


ruleset j : NODE do
  invariant "inv_352"
    (((Sta.Dir.HeadVld = true) & (Sta.UniMsg[j].Cmd = UNI_Get)) -> (!(Sta.InvMsg[j].Cmd = INV_Inv)));
endruleset;


ruleset j : NODE do
  invariant "inv_350"
    (((Sta.Dir.Local = true) & (Sta.InvMsg[j].Cmd = INV_InvAck)) -> (Sta.Dir.HeadPtr = j));
endruleset;


ruleset j : NODE do
  invariant "inv_349"
    (((Sta.UniMsg[j].Cmd = UNI_GetX) & (Sta.Dir.HeadVld = true)) -> (!(Sta.InvMsg[j].Cmd = INV_InvAck)));
endruleset;


ruleset i : NODE do
  invariant "inv_346"
    ((Sta.InvMsg[i].Cmd = INV_InvAck) -> (Sta.Dir.HomeShrSet = false));
endruleset;


invariant "inv_345"
  (((Sta.Dir.Local = false) & (Sta.Dir.Dirty = true)) -> (Sta.Dir.HeadVld = true));


ruleset j : NODE do
  invariant "inv_344"
    (((Sta.Dir.Local = true) & (Sta.Dir.ShrSet[j] = true)) -> (Sta.HomeProc.CacheState = CACHE_S));
endruleset;


ruleset i : NODE do
  invariant "inv_343"
    ((Sta.UniMsg[i].HomeProc = true) -> (Sta.Dir.HomeShrSet = false));
endruleset;


ruleset j : NODE do
  invariant "inv_342"
    ((Sta.Dir.HeadVld = false) -> (!(Sta.Proc[j].CacheState = CACHE_E)));
endruleset;


ruleset j : NODE do
  invariant "inv_341"
    ((!(Sta.Proc[j].CacheState = CACHE_E)) -> (Sta.Dir.HomeInvSet = false));
endruleset;


ruleset j : NODE do
  invariant "inv_340"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (!(Sta.UniMsg[j].Cmd = UNI_GetX)));
endruleset;


ruleset j : NODE do
  invariant "inv_339"
    ((Sta.UniMsg[j].HomeProc = true) -> (!(Sta.Proc[j].CacheState = CACHE_S)));
endruleset;


ruleset j : NODE do
  invariant "inv_336"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (!(Sta.UniMsg[j].Cmd = UNI_Nak)));
endruleset;


ruleset i : NODE do
  invariant "inv_334"
    ((Sta.UniMsg[i].Cmd = UNI_GetX) -> (!(Sta.Proc[i].ProcCmd = NODE_Get)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_333"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (!(Sta.UniMsg[i].Cmd = UNI_PutX)));
endruleset;


invariant "inv_331"
  ((Sta.Dir.Dirty = false) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));


ruleset j : NODE do
  invariant "inv_329"
    ((Sta.Dir.ShrSet[j] = true) -> (!(Sta.Proc[j].CacheState = CACHE_E)));
endruleset;


invariant "inv_328"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (Sta.HomeProc.ProcCmd = NODE_None));


ruleset i : NODE do
  invariant "inv_327"
    ((Sta.Proc[i].ProcCmd = NODE_None) -> (Sta.HomeProc.InvMarked = false));
endruleset;


invariant "inv_324"
  ((Sta.Dir.HomeShrSet = false) -> (Sta.Dir.HomeInvSet = false));


invariant "inv_323"
  ((Sta.Dir.Local = true) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));


ruleset j : NODE do
  invariant "inv_322"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));
endruleset;


ruleset i : NODE do
  invariant "inv_320"
    ((Sta.Proc[i].ProcCmd = NODE_None) -> (!(Sta.UniMsg[i].Cmd = UNI_GetX)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_317"
    ((Sta.UniMsg[j].Proc = i) -> (Sta.Dir.HomeInvSet = false));
endruleset;


ruleset i : NODE do
  invariant "inv_316"
    ((Sta.UniMsg[i].HomeProc = true) -> (Sta.Proc[i].CacheState = CACHE_I));
endruleset;


ruleset j : NODE do
  invariant "inv_315"
    ((Sta.UniMsg[j].HomeProc = false) -> (Sta.Dir.HomeHeadPtr = false));
endruleset;


invariant "inv_313"
  ((Sta.Dir.HeadVld = true) -> (Sta.HomeProc.InvMarked = false));


ruleset i : NODE; j : NODE do
  invariant "inv_312"
    ((Sta.InvMsg[j].Cmd = INV_InvAck) -> (!(Sta.Proc[i].CacheState = CACHE_E)));
endruleset;


ruleset i : NODE do
  invariant "inv_310"
    ((Sta.UniMsg[i].Cmd = UNI_GetX) -> (Sta.Proc[i].ProcCmd = NODE_GetX));
endruleset;


ruleset i : NODE do
  invariant "inv_308"
    (((Sta.Dir.ShrSet[i] = true) & (Sta.Dir.Local = true)) -> (Sta.HomeProc.CacheState = CACHE_S));
endruleset;


ruleset j : NODE do
  invariant "inv_306"
    (((Sta.Dir.Local = true) & (Sta.InvMsg[j].Cmd = INV_InvAck)) -> (Sta.Dir.InvSet[j] = true));
endruleset;


ruleset i : NODE do
  invariant "inv_304"
    ((Sta.Proc[i].ProcCmd = NODE_None) -> (Sta.Dir.HomeInvSet = false));
endruleset;


ruleset j : NODE do
  invariant "inv_302"
    (((Sta.Dir.InvSet[j] = true) & (Sta.Dir.Dirty = true)) -> (Sta.Dir.HeadVld = false));
endruleset;


ruleset j : NODE do
  invariant "inv_299"
    ((!(Sta.RpMsg[j].Cmd = RP_Replace)) -> (Sta.HomeProc.InvMarked = false));
endruleset;


invariant "inv_293"
  ((Sta.Dir.Dirty = false) -> (Sta.Dir.HomeInvSet = false));


invariant "inv_292"
  ((Sta.Dir.Pending = true) -> (Sta.Dir.HomeHeadPtr = false));


ruleset j : NODE do
  invariant "inv_290"
    (((Sta.Dir.Dirty = false) & (Sta.InvMsg[j].Cmd = INV_InvAck)) -> (Sta.HomeProc.ProcCmd = NODE_None));
endruleset;


ruleset j : NODE do
  invariant "inv_289"
    ((Sta.UniMsg[j].HomeProc = true) -> (Sta.HomeProc.InvMarked = false));
endruleset;


ruleset j : NODE do
  invariant "inv_286"
    (((Sta.Dir.Local = true) & (Sta.Dir.ShrSet[j] = true)) -> (Sta.HomeProc.CacheData = Sta.CurrData));
endruleset;


ruleset i : NODE do
  invariant "inv_285"
    ((Sta.UniMsg[i].Cmd = UNI_Get) -> (!(Sta.Proc[i].CacheState = CACHE_E)));
endruleset;


ruleset j : NODE do
  invariant "inv_284"
    ((Sta.UniMsg[j].HomeProc = false) -> (Sta.HomeProc.InvMarked = false));
endruleset;


ruleset j : NODE do
  invariant "inv_281"
    ((Sta.UniMsg[j].HomeProc = false) -> (Sta.Dir.HomeShrSet = false));
endruleset;


ruleset j : NODE do
  invariant "inv_280"
    ((Sta.Dir.InvSet[j] = true) -> (Sta.Dir.HomeHeadPtr = false));
endruleset;


invariant "inv_279"
  (((Sta.Dir.Dirty = false) & (Sta.Dir.Pending = true)) -> (Sta.Dir.HeadVld = false));


invariant "inv_276"
  ((Sta.Dir.Local = false) -> (Sta.HomeProc.InvMarked = false));


invariant "inv_275"
  ((Sta.Dir.Local = false) -> (!(Sta.HomeProc.CacheState = CACHE_E)));


ruleset i : NODE do
  invariant "inv_274"
    (((Sta.Dir.Local = false) & (Sta.Dir.Dirty = true)) -> (Sta.Dir.InvSet[i] = false));
endruleset;


ruleset j : NODE do
  invariant "inv_273"
    ((Sta.UniMsg[j].Cmd = UNI_Get) -> (Sta.Proc[j].ProcCmd = NODE_Get));
endruleset;


ruleset i : NODE do
  invariant "inv_272"
    (((Sta.InvMsg[i].Cmd = INV_InvAck) & (Sta.Dir.Dirty = true)) -> (!(Sta.Proc[i].CacheState = CACHE_S)));
endruleset;


ruleset i : NODE do
  invariant "inv_269"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (Sta.Dir.HomeInvSet = false));
endruleset;


invariant "inv_268"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (Sta.Dir.ShrVld = false));


ruleset j : NODE do
  invariant "inv_267"
    (((Sta.Dir.Local = true) & (Sta.Dir.ShrSet[j] = true)) -> (!(Sta.ShWbMsg.Cmd = SHWB_FAck)));
endruleset;


ruleset j : NODE do
  invariant "inv_263"
    ((Sta.UniMsg[j].Cmd = UNI_Get) -> (Sta.Proc[j].CacheState = CACHE_I));
endruleset;


invariant "inv_262"
  ((Sta.Dir.HomeHeadPtr = false) -> (Sta.HomeProc.InvMarked = false));


ruleset i : NODE do
  invariant "inv_261"
    ((Sta.Dir.ShrSet[i] = true) -> (Sta.Dir.InvSet[i] = true));
endruleset;


invariant "inv_252"
  ((Sta.Dir.HeadVld = false) -> (Sta.Dir.HomeShrSet = false));


ruleset j : NODE do
  invariant "inv_251"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (Sta.HomeProc.CacheState = CACHE_I));
endruleset;


invariant "inv_250"
  ((Sta.Dir.Dirty = true) -> (Sta.HomeProc.InvMarked = false));


ruleset i : NODE do
  invariant "inv_249"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (Sta.Dir.ShrSet[i] = false));
endruleset;


ruleset i : NODE do
  invariant "inv_248"
    (((Sta.Dir.Dirty = false) & (Sta.InvMsg[i].Cmd = INV_InvAck)) -> (Sta.Dir.InvSet[i] = true));
endruleset;


invariant "inv_247"
  ((Sta.Dir.Pending = true) -> (Sta.Dir.HomeShrSet = false));


ruleset i : NODE do
  invariant "inv_245"
    (((Sta.InvMsg[i].Cmd = INV_InvAck) & (Sta.Dir.InvSet[i] = true)) -> (Sta.HomeProc.ProcCmd = NODE_None));
endruleset;


invariant "inv_240"
  ((Sta.Dir.HeadVld = false) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));


ruleset i : NODE do
  invariant "inv_239"
    (((Sta.Dir.ShrSet[i] = true) & (Sta.Dir.Local = true)) -> (!(Sta.HomeProc.CacheState = CACHE_I)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_236"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (Sta.Dir.InvSet[j] = false));
endruleset;


ruleset i : NODE do
  invariant "inv_234"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (Sta.Dir.HomeShrSet = false));
endruleset;


invariant "inv_230"
  ((Sta.Dir.Dirty = false) -> (!(Sta.WbMsg.Cmd = WB_Wb)));


invariant "inv_228"
  ((!(Sta.HomeProc.ProcCmd = NODE_Get)) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));


ruleset i : NODE; j : NODE do
  invariant "inv_223"
    ((Sta.UniMsg[i].Proc = j) -> (Sta.HomeProc.InvMarked = false));
endruleset;


ruleset i : NODE do
  invariant "inv_222"
    ((Sta.Proc[i].ProcCmd = NODE_None) -> (!(Sta.UniMsg[i].Cmd = UNI_Put)));
endruleset;


invariant "inv_220"
  ((Sta.Dir.HeadVld = false) -> (Sta.HomeProc.InvMarked = false));


invariant "inv_219"
  ((Sta.Dir.Pending = false) -> (Sta.Dir.HomeShrSet = false));


ruleset i : NODE; j : NODE do
  invariant "inv_216"
    (((Sta.Proc[j].CacheState = CACHE_E) & (Sta.UniMsg[i].Cmd = UNI_GetX)) -> (!(Sta.InvMsg[i].Cmd = INV_Inv)));
endruleset;


ruleset j : NODE do
  invariant "inv_215"
    ((Sta.InvMsg[j].Cmd = INV_InvAck) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));
endruleset;


ruleset i : NODE do
  invariant "inv_208"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));
endruleset;


ruleset j : NODE do
  invariant "inv_205"
    ((Sta.Dir.Local = true) -> (!(Sta.Proc[j].CacheState = CACHE_E)));
endruleset;


ruleset j : NODE do
  invariant "inv_200"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (Sta.Dir.Dirty = true));
endruleset;


invariant "inv_199"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (Sta.HomeProc.CacheData = Sta.CurrData));


ruleset i : NODE; j : NODE do
  invariant "inv_198"
    ((Sta.Dir.ShrSet[j] = true) -> (!(Sta.UniMsg[i].Cmd = UNI_PutX)));
endruleset;


invariant "inv_197"
  ((Sta.Dir.Pending = true) -> (Sta.Dir.HomeInvSet = false));


ruleset i : NODE do
  invariant "inv_196"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));
endruleset;


invariant "inv_195"
  ((Sta.Dir.Local = true) -> (!(Sta.HomeProc.ProcCmd = NODE_Get)));


ruleset j : NODE do
  invariant "inv_194"
    ((Sta.Dir.Dirty = false) -> (!(Sta.UniMsg[j].Cmd = UNI_PutX)));
endruleset;


ruleset i : NODE do
  invariant "inv_193"
    (((Sta.Dir.HeadVld = true) & (Sta.UniMsg[i].Cmd = UNI_GetX)) -> (!(Sta.InvMsg[i].Cmd = INV_Inv)));
endruleset;


ruleset i : NODE do
  invariant "inv_191"
    ((Sta.Dir.ShrSet[i] = true) -> (Sta.MemData = Sta.CurrData));
endruleset;


ruleset j : NODE do
  invariant "inv_188"
    ((Sta.Dir.InvSet[j] = true) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));
endruleset;


ruleset j : NODE do
  invariant "inv_186"
    (((Sta.Dir.Dirty = true) & (Sta.InvMsg[j].Cmd = INV_InvAck)) -> (!(Sta.Proc[j].CacheState = CACHE_S)));
endruleset;


invariant "inv_185"
  ((Sta.Dir.Local = true) -> (Sta.Dir.HomeShrSet = false));


invariant "inv_183"
  ((Sta.Dir.Pending = false) -> (Sta.HomeProc.InvMarked = false));


invariant "inv_181"
  ((Sta.Dir.Pending = false) -> (Sta.Dir.HomeInvSet = false));


invariant "inv_180"
  ((Sta.Dir.Local = false) -> (Sta.Dir.HomeShrSet = false));


ruleset j : NODE do
  invariant "inv_176"
    (((Sta.UniMsg[j].Cmd = UNI_GetX) & (Sta.Dir.HeadVld = true)) -> (!(Sta.InvMsg[j].Cmd = INV_Inv)));
endruleset;


ruleset i : NODE do
  invariant "inv_174"
    (((Sta.UniMsg[i].Cmd = UNI_Get) & (Sta.Dir.HeadVld = true)) -> (!(Sta.InvMsg[i].Cmd = INV_InvAck)));
endruleset;


ruleset j : NODE do
  invariant "inv_172"
    (((Sta.Dir.InvSet[j] = true) & (Sta.InvMsg[j].Cmd = INV_InvAck)) -> (Sta.Dir.HeadPtr = j));
endruleset;


ruleset i : NODE do
  invariant "inv_171"
    ((Sta.Proc[i].ProcCmd = NODE_None) -> (!(Sta.UniMsg[i].Cmd = UNI_Get)));
endruleset;


ruleset j : NODE do
  invariant "inv_170"
    ((Sta.InvMsg[j].Cmd = INV_InvAck) -> (Sta.HomeProc.InvMarked = false));
endruleset;


ruleset i : NODE do
  invariant "inv_168"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (!(Sta.WbMsg.Cmd = WB_Wb)));
endruleset;


ruleset j : NODE do
  invariant "inv_167"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (Sta.Proc[j].CacheData = Sta.CurrData));
endruleset;


ruleset i : NODE do
  invariant "inv_165"
    ((Sta.UniMsg[i].Cmd = UNI_Get) -> (Sta.Dir.HomeShrSet = false));
endruleset;


ruleset j : NODE do
  invariant "inv_162"
    ((!(Sta.Proc[j].CacheState = CACHE_E)) -> (Sta.HomeProc.InvMarked = false));
endruleset;


invariant "inv_160"
  ((Sta.Dir.HomeShrSet = false) -> (Sta.HomeProc.InvMarked = false));


ruleset i : NODE; j : NODE do
  invariant "inv_156"
    ((Sta.Dir.ShrSet[j] = true) -> (!(Sta.Proc[i].CacheState = CACHE_E)));
endruleset;


ruleset i : NODE do
  invariant "inv_151"
    ((Sta.Dir.ShrSet[i] = true) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));
endruleset;


ruleset i : NODE do
  invariant "inv_147"
    ((Sta.Dir.ShrSet[i] = true) -> (!(Sta.WbMsg.Cmd = WB_Wb)));
endruleset;


ruleset i : NODE do
  invariant "inv_146"
    ((Sta.Dir.Dirty = true) -> (Sta.Dir.ShrSet[i] = false));
endruleset;


invariant "inv_141"
  ((Sta.Dir.HeadVld = true) -> (Sta.Dir.HomeShrSet = false));


invariant "inv_137"
  (((Sta.Dir.HeadVld = false) & (Sta.Dir.Local = false)) -> (Sta.MemData = Sta.CurrData));


invariant "inv_130"
  ((Sta.Dir.HeadVld = false) -> (Sta.Dir.HomeInvSet = false));


invariant "inv_129"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (Sta.Dir.HomeShrSet = false));


invariant "inv_128"
  ((Sta.Dir.Local = true) -> (Sta.HomeProc.InvMarked = false));


invariant "inv_127"
  ((Sta.Dir.Local = false) -> (Sta.Dir.HomeInvSet = false));


invariant "inv_126"
  ((Sta.Dir.Dirty = true) -> (!(Sta.HomeProc.CacheState = CACHE_S)));


ruleset j : NODE do
  invariant "inv_123"
    (((Sta.Dir.Pending = true) & (Sta.InvMsg[j].Cmd = INV_InvAck)) -> (!(Sta.Proc[j].CacheState = CACHE_S)));
endruleset;


invariant "inv_121"
  ((Sta.Dir.Dirty = false) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));


ruleset i : NODE do
  invariant "inv_120"
    ((Sta.Dir.InvSet[i] = true) -> (!(Sta.WbMsg.Cmd = WB_Wb)));
endruleset;


ruleset i : NODE do
  invariant "inv_119"
    ((Sta.Dir.ShrSet[i] = true) -> (!(Sta.HomeUniMsg.Cmd = UNI_PutX)));
endruleset;


invariant "inv_118"
  ((Sta.Dir.HeadVld = true) -> (Sta.Dir.HomeInvSet = false));


invariant "inv_117"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));


ruleset i : NODE do
  invariant "inv_116"
    ((Sta.HomeProc.CacheState = CACHE_E) -> (!(Sta.Proc[i].CacheState = CACHE_E)));
endruleset;


ruleset i : NODE do
  invariant "inv_115"
    ((Sta.Dir.HeadPtr = i) -> (Sta.HomeProc.InvMarked = false));
endruleset;


ruleset j : NODE do
  invariant "inv_112"
    (((Sta.Dir.InvSet[j] = true) & (Sta.InvMsg[j].Cmd = INV_InvAck)) -> (!(Sta.HomeProc.ProcCmd = NODE_Get)));
endruleset;


ruleset j : NODE do
  invariant "inv_110"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (Sta.Dir.ShrVld = false));
endruleset;


invariant "inv_107"
  ((Sta.Dir.Dirty = false) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));


invariant "inv_105"
  ((Sta.Dir.Dirty = false) -> (Sta.HomeProc.InvMarked = false));


ruleset i : NODE do
  invariant "inv_104"
    ((Sta.Dir.Pending = true) -> (Sta.Dir.ShrSet[i] = false));
endruleset;


ruleset i : NODE do
  invariant "inv_103"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (Sta.Proc[i].ProcCmd = NODE_None));
endruleset;


ruleset j : NODE do
  invariant "inv_102"
    ((Sta.Proc[j].CacheState = CACHE_E) -> (Sta.Proc[j].InvMarked = false));
endruleset;


invariant "inv_98"
  ((Sta.Dir.HeadVld = false) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));


invariant "inv_93"
  ((Sta.Dir.Local = true) -> (!(Sta.ShWbMsg.Cmd = SHWB_ShWb)));


ruleset i : NODE do
  invariant "inv_92"
    ((Sta.HomeProc.CacheState = CACHE_E) -> (!(Sta.UniMsg[i].Cmd = UNI_PutX)));
endruleset;


ruleset j : NODE do
  invariant "inv_91"
    ((Sta.UniMsg[j].Cmd = UNI_Get) -> (Sta.HomeProc.InvMarked = false));
endruleset;


invariant "inv_90"
  ((Sta.Dir.Local = true) -> (Sta.HomeProc.ProcCmd = NODE_None));


invariant "inv_88"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (Sta.Dir.Dirty = true));


invariant "inv_84"
  ((Sta.Dir.HomeHeadPtr = false) -> (Sta.Dir.HomeInvSet = false));


invariant "inv_79"
  (((Sta.Dir.Local = true) & (Sta.Dir.Dirty = true)) -> (Sta.HomeProc.CacheState = CACHE_E));


ruleset j : NODE do
  invariant "inv_73"
    (((Sta.Dir.Local = true) & (Sta.Dir.ShrSet[j] = true)) -> (!(Sta.HomeProc.CacheState = CACHE_I)));
endruleset;


invariant "inv_62"
  ((Sta.Dir.HeadVld = false) -> (!(Sta.WbMsg.Cmd = WB_Wb)));


ruleset i : NODE do
  invariant "inv_57"
    (((Sta.InvMsg[i].Cmd = INV_InvAck) & (Sta.Dir.InvSet[i] = true)) -> (!(Sta.HomeProc.ProcCmd = NODE_Get)));
endruleset;


ruleset j : NODE do
  invariant "inv_52"
    (((Sta.Dir.HeadVld = true) & (Sta.UniMsg[j].Cmd = UNI_Get)) -> (!(Sta.InvMsg[j].Cmd = INV_InvAck)));
endruleset;


invariant "inv_47"
  (((Sta.Dir.Pending = false) & (Sta.Dir.Local = true)) -> (Sta.HomeProc.CacheData = Sta.CurrData));


ruleset i : NODE; j : NODE do
  invariant "inv_44"
    (((Sta.UniMsg[j].Cmd = UNI_GetX) & (Sta.Proc[i].CacheState = CACHE_E)) -> (!(Sta.InvMsg[j].Cmd = INV_Inv)));
endruleset;


invariant "inv_41"
  ((!(Sta.HomeProc.ProcCmd = NODE_Get)) -> (Sta.Dir.HomeShrSet = false));


invariant "inv_39"
  (((Sta.Dir.HeadVld = true) & (Sta.Dir.Local = true)) -> (Sta.Dir.Pending = false));


ruleset i : NODE do
  invariant "inv_38"
    ((Sta.Proc[i].CacheState = CACHE_E) -> (Sta.HomeProc.InvMarked = false));
endruleset;


invariant "inv_33"
  (((Sta.Dir.Dirty = false) & (Sta.Dir.HeadVld = true)) -> (Sta.Dir.Pending = false));


invariant "inv_31"
  ((Sta.Dir.Local = true) -> (!(Sta.WbMsg.Cmd = WB_Wb)));


invariant "inv_25"
  ((Sta.Dir.HeadVld = false) -> (Sta.Dir.ShrVld = false));


invariant "inv_21"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (!(Sta.HomeUniMsg.Cmd = UNI_Put)));


invariant "inv_9"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (Sta.Dir.HeadVld = false));


invariant "inv_7"
  ((Sta.Dir.HomeInvSet = false) -> (Sta.Dir.HomeShrSet = false));


invariant "inv_5"
  ((Sta.HomeProc.CacheState = CACHE_E) -> (Sta.Dir.Local = true));


invariant "inv_4"
  ((Sta.Dir.Local = false) -> (Sta.HomeProc.CacheState = CACHE_I));
