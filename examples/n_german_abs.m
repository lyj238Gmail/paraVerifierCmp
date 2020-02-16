type
  CACHE_STATE : enum{I, S, E};
  MSG_CMD : enum{Empty, ReqS, ReqE, Inv, InvAck, GntS, GntE};
  NODE : scalarset(2);
  DATA : scalarset(1);



record_0 : record
Data :  DATA;
Cmd :  MSG_CMD;
end;


record_1 : record
Data :  DATA;
State :  CACHE_STATE;
end;


var
AuxData :  DATA;
MemData :  DATA;
CurPtr :  NODE;
CurCmd :  MSG_CMD;
ExGntd :  boolean;
ShrSet : array [NODE] of boolean;
InvSet : array [NODE] of boolean;
Chan3 : array [NODE] of record_0;
Chan2 : array [NODE] of record_0;
Chan1 : array [NODE] of record_0;
Cache : array [NODE] of record_1;


startstate
begin
  for i : NODE do
    Chan1[i].Cmd := Empty;
    Chan2[i].Cmd := Empty;
    Chan3[i].Cmd := Empty;
    Cache[i].State := I;
    InvSet[i] := false;
    ShrSet[i] := false;
  endfor;
  ExGntd := false;
  CurCmd := Empty;
  MemData := 1;
  AuxData := 1;
endstartstate;


ruleset i : NODE do
  rule "n_RecvGntE1"
    (Chan2[i].Cmd = GntE) ==>
  begin
    Cache[i].State := E;
    Cache[i].Data := Chan2[i].Data;
    Chan2[i].Cmd := Empty;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_RecvGntS2"
    (Chan2[i].Cmd = GntS) ==>
  begin
    Cache[i].State := S;
    Cache[i].Data := Chan2[i].Data;
    Chan2[i].Cmd := Empty;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_SendGntE3"
    (((((CurCmd = ReqE) & (CurPtr = i)) & (Chan2[i].Cmd = Empty)) & (ExGntd = false)) & (forall j : NODE do (ShrSet[j] = false) endforall)) ==>
  begin
    Chan2[i].Cmd := GntE;
    Chan2[i].Data := MemData;
    ShrSet[i] := true;
    ExGntd := true;
    CurCmd := Empty;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_SendGntS4"
    ((((CurCmd = ReqS) & (CurPtr = i)) & (Chan2[i].Cmd = Empty)) & (ExGntd = false)) ==>
  begin
    Chan2[i].Cmd := GntS;
    Chan2[i].Data := MemData;
    ShrSet[i] := true;
    CurCmd := Empty;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_RecvInvAck5"
    ((Chan3[i].Cmd = InvAck) & (ExGntd = true)) ==>
  begin
    Chan3[i].Cmd := Empty;
    ShrSet[i] := false;
    ExGntd := false;
    MemData := Chan3[i].Data;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_RecvInvAck6"
    ((Chan3[i].Cmd = InvAck) & (!(ExGntd = true))) ==>
  begin
    Chan3[i].Cmd := Empty;
    ShrSet[i] := false;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_SendInvAck7"
    (((Chan2[i].Cmd = Inv) & (Chan3[i].Cmd = Empty)) & (Cache[i].State = E)) ==>
  begin
    Chan2[i].Cmd := Empty;
    Chan3[i].Cmd := InvAck;
    Chan3[i].Data := Cache[i].Data;
    Cache[i].State := I;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_SendInvAck8"
    (((Chan2[i].Cmd = Inv) & (Chan3[i].Cmd = Empty)) & (!(Cache[i].State = E))) ==>
  begin
    Chan2[i].Cmd := Empty;
    Chan3[i].Cmd := InvAck;
    Cache[i].State := I;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_SendInv9"
    (((Chan2[i].Cmd = Empty) & (InvSet[i] = true)) & (CurCmd = ReqE)) ==>
  begin
    Chan2[i].Cmd := Inv;
    InvSet[i] := false;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_SendInv10"
    ((((Chan2[i].Cmd = Empty) & (InvSet[i] = true)) & (CurCmd = ReqS)) & (ExGntd = true)) ==>
  begin
    Chan2[i].Cmd := Inv;
    InvSet[i] := false;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_RecvReqE11"
    ((CurCmd = Empty) & (Chan1[i].Cmd = ReqE)) ==>
  begin
    CurCmd := ReqE;
    CurPtr := i;
    Chan1[i].Cmd := Empty;
    for j : NODE do
      InvSet[j] := ShrSet[j];
    endfor;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_RecvReqS12"
    ((CurCmd = Empty) & (Chan1[i].Cmd = ReqS)) ==>
  begin
    CurCmd := ReqS;
    CurPtr := i;
    Chan1[i].Cmd := Empty;
    for j : NODE do
      InvSet[j] := ShrSet[j];
    endfor;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_SendReqE13"
    ((Chan1[i].Cmd = Empty) & (Cache[i].State = I)) ==>
  begin
    Chan1[i].Cmd := ReqE;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_SendReqE14"
    ((Chan1[i].Cmd = Empty) & (Cache[i].State = S)) ==>
  begin
    Chan1[i].Cmd := ReqE;
  endrule;
endruleset;


ruleset i : NODE do
  rule "n_SendReqS15"
    ((Chan1[i].Cmd = Empty) & (Cache[i].State = I)) ==>
  begin
    Chan1[i].Cmd := ReqS;
  endrule;
endruleset;


ruleset i : NODE; d : DATA do
  rule "n_Store"
    (Cache[i].State = E) ==>
  begin
    Cache[i].Data := d;
    AuxData := d;
  endrule;
endruleset;


rule "n_SendGntE3_i_3"
  ((CurCmd = ReqE) & (ExGntd = false) & (forall j : NODE do (ShrSet[j] = false) endforall) & (MemData = AuxData) & (forall i : NODE do (!(Chan2[i].Cmd = GntE)) endforall) & (forall j : NODE do (!(Cache[j].State = E)) endforall)) ==>
begin
  ExGntd := true;
  CurCmd := Empty;
endrule;


rule "n_SendGntS4_i_3"
  ((CurCmd = ReqS) & (ExGntd = false) & (MemData = AuxData) & (forall i : NODE do (!(Chan2[i].Cmd = GntE)) endforall) & (forall j : NODE do (!(Cache[j].State = E)) endforall) & (forall j : NODE do (Chan3[j].Cmd = Empty) endforall) & (forall i : NODE do (!(Chan3[i].Cmd = InvAck)) endforall) & (forall i : NODE do (!(Chan2[i].Cmd = Inv)) endforall)) ==>
begin
  CurCmd := Empty;
endrule;


rule "n_RecvInvAck5_i_3"
  ((ExGntd = true) & (forall i : NODE do (!(Chan2[i].Cmd = GntS)) endforall) & (forall j : NODE do (!(Cache[j].State = S)) endforall) & (!(CurCmd = Empty)) & (forall j : NODE do (!(Chan2[j].Cmd = GntE)) endforall) & (forall j : NODE do (!(Cache[j].State = E)) endforall) & (forall j : NODE do (ShrSet[j] = false) endforall) & (forall j : NODE do (InvSet[j] = false) endforall) & (forall j : NODE do (Chan3[j].Cmd = Empty) endforall) & (forall j : NODE do (Chan2[j].Cmd = Empty) endforall) & (forall j : NODE do (Cache[j].State = I) endforall) & (forall j : NODE do (!(Chan3[j].Cmd = InvAck)) endforall) & (forall j : NODE do (!(Chan2[j].Cmd = Inv)) endforall) & (forall i : NODE do (ShrSet[i] = false) endforall) & (forall i : NODE do (InvSet[i] = false) endforall) & (forall i : NODE do (Chan3[i].Cmd = Empty) endforall) & (forall i : NODE do (Chan2[i].Cmd = Empty) endforall) & (forall i : NODE do (Cache[i].State = I) endforall) & (forall i : NODE do (!(Chan3[i].Cmd = InvAck)) endforall) & (forall i : NODE do (!(Chan2[i].Cmd = Inv)) endforall)) ==>
begin
  ExGntd := false;
  MemData := AuxData;
endrule;


rule "n_RecvReqE11_i_3"
  ((CurCmd = Empty) & (forall i : NODE do (Chan3[i].Cmd = Empty) endforall) & (forall i : NODE do (!(Chan3[i].Cmd = InvAck)) endforall) & (forall i : NODE do (!(Chan2[i].Cmd = Inv)) endforall)) ==>
begin
  CurCmd := ReqE;
  CurPtr := 3;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  endfor;
endrule;


rule "n_RecvReqS12_i_3"
  ((CurCmd = Empty) & (forall i : NODE do (Chan3[i].Cmd = Empty) endforall) & (forall i : NODE do (!(Chan3[i].Cmd = InvAck)) endforall) & (forall i : NODE do (!(Chan2[i].Cmd = Inv)) endforall)) ==>
begin
  CurCmd := ReqS;
  CurPtr := 3;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  endfor;
endrule;


ruleset d : DATA do
  rule "n_Store_i_3"
    ((forall j : NODE do (ShrSet[j] = false) endforall) & (forall i : NODE do (InvSet[i] = false) endforall) & (ExGntd = true) & (forall j : NODE do (Chan3[j].Cmd = Empty) endforall) & (forall j : NODE do (Chan2[j].Cmd = Empty) endforall) & (forall i : NODE do (Cache[i].State = I) endforall) & (forall j : NODE do (!(Chan3[j].Cmd = InvAck)) endforall) & (forall j : NODE do (!(Chan2[j].Cmd = Inv)) endforall) & (forall i : NODE do (!(Chan2[i].Cmd = GntS)) endforall) & (forall j : NODE do (!(Chan2[j].Cmd = GntE)) endforall) & (forall i : NODE do (!(Cache[i].State = S)) endforall) & (forall i : NODE do (!(Cache[i].State = E)) endforall)) ==>
  begin
    AuxData := d;
  endrule;
endruleset;


ruleset j : NODE do
  invariant "inv_239"
    ((ExGntd = false) -> (!(Cache[j].State = E)));
endruleset;


ruleset i : NODE do
  invariant "inv_236"
    ((Cache[i].State = E) -> (!(Chan2[i].Cmd = GntS)));
endruleset;


ruleset j : NODE do
  invariant "inv_234"
    ((Cache[j].State = E) -> (!(Chan3[j].Cmd = InvAck)));
endruleset;


ruleset j : NODE do
  invariant "inv_233"
    ((Chan3[j].Cmd = InvAck) -> (!(CurCmd = Empty)));
endruleset;


ruleset i : NODE do
  invariant "inv_232"
    ((ExGntd = false) -> (!(Chan2[i].Cmd = GntE)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_231"
    ((Cache[i].State = E) -> (ShrSet[j] = false));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_226"
    ((Cache[j].State = E) -> (InvSet[i] = false));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_224"
    ((Cache[i].State = E) -> (!(Chan3[j].Cmd = InvAck)));
endruleset;


ruleset i : NODE do
  invariant "inv_223"
    ((Chan3[i].Cmd = InvAck) -> (InvSet[i] = false));
endruleset;


ruleset j : NODE do
  invariant "inv_219"
    ((Chan3[j].Cmd = InvAck) -> (Chan2[j].Cmd = Empty));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_218"
    (((ExGntd = true) & (Chan3[i].Cmd = InvAck)) -> (!(Chan2[j].Cmd = Inv)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_217"
    ((Cache[i].State = E) -> (!(Chan2[j].Cmd = GntE)));
endruleset;


ruleset j : NODE do
  invariant "inv_214"
    ((Chan3[j].Cmd = InvAck) -> (Cache[j].State = I));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_213"
    (((ExGntd = true) & (Chan3[i].Cmd = InvAck)) -> (!(Chan3[j].Cmd = InvAck)));
endruleset;


ruleset i : NODE do
  invariant "inv_212"
    (((ExGntd = false) & (CurCmd = ReqS)) -> (!(Chan3[i].Cmd = InvAck)));
endruleset;


ruleset i : NODE do
  invariant "inv_211"
    (((ExGntd = false) & (CurCmd = ReqS)) -> (!(Chan2[i].Cmd = Inv)));
endruleset;


ruleset j : NODE do
  invariant "inv_210"
    (((ExGntd = false) & (CurCmd = ReqS)) -> (Chan3[j].Cmd = Empty));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_209"
    ((Cache[i].State = E) -> (Chan2[j].Cmd = Empty));
endruleset;


ruleset i : NODE do
  invariant "inv_194"
    ((ExGntd = true) -> (!(Chan2[i].Cmd = GntS)));
endruleset;


ruleset i : NODE do
  invariant "inv_192"
    ((CurCmd = Empty) -> (!(Chan2[i].Cmd = Inv)));
endruleset;


ruleset i : NODE do
  invariant "inv_191"
    ((Cache[i].State = E) -> (!(Chan2[i].Cmd = GntE)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_190"
    ((Cache[j].State = E) -> (Cache[i].State = I));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_189"
    ((Chan3[i].Cmd = InvAck) -> (!(Cache[j].State = E)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_188"
    (((ExGntd = true) & (Chan3[i].Cmd = InvAck)) -> (Cache[j].State = I));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_186"
    (((Chan3[j].Cmd = InvAck) & (ExGntd = true)) -> (Cache[i].State = I));
endruleset;


ruleset j : NODE do
  invariant "inv_181"
    ((Chan3[j].Cmd = InvAck) -> (!(Cache[j].State = E)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_180"
    ((Cache[i].State = E) -> (!(Chan2[j].Cmd = Inv)));
endruleset;


ruleset i : NODE do
  invariant "inv_176"
    ((Chan3[i].Cmd = InvAck) -> (ShrSet[i] = true));
endruleset;


ruleset i : NODE do
  invariant "inv_172"
    ((CurCmd = Empty) -> (Chan3[i].Cmd = Empty));
endruleset;


ruleset j : NODE do
  invariant "inv_166"
    ((Chan3[j].Cmd = InvAck) -> (!(Cache[j].State = S)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_165"
    (((Chan3[j].Cmd = InvAck) & (ExGntd = true)) -> (ShrSet[i] = false));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_164"
    ((Cache[j].State = E) -> (!(Cache[i].State = E)));
endruleset;


ruleset i : NODE do
  invariant "inv_161"
    (((ExGntd = true) & (Chan3[i].Cmd = InvAck)) -> (Chan3[i].Data = AuxData));
endruleset;


ruleset j : NODE do
  invariant "inv_159"
    ((Cache[j].State = E) -> (ShrSet[j] = true));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_153"
    (((ExGntd = true) & (Chan3[i].Cmd = InvAck)) -> (ShrSet[j] = false));
endruleset;


ruleset j : NODE do
  invariant "inv_143"
    ((Chan3[j].Cmd = InvAck) -> (!(Chan2[j].Cmd = Inv)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_138"
    ((Cache[j].State = E) -> (!(Chan2[i].Cmd = GntS)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_136"
    ((Cache[i].State = E) -> (Chan3[j].Cmd = Empty));
endruleset;


ruleset i : NODE do
  invariant "inv_134"
    ((CurCmd = Empty) -> (!(Chan3[i].Cmd = InvAck)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_125"
    (((Chan3[j].Cmd = InvAck) & (ExGntd = true)) -> (!(Chan2[i].Cmd = Inv)));
endruleset;


ruleset j : NODE do
  invariant "inv_113"
    ((Chan3[j].Cmd = InvAck) -> (!(Chan2[j].Cmd = GntS)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_111"
    (((Chan3[j].Cmd = InvAck) & (ExGntd = true)) -> (!(Chan3[i].Cmd = InvAck)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_110"
    (((Chan3[j].Cmd = InvAck) & (ExGntd = true)) -> (Chan2[i].Cmd = Empty));
endruleset;


ruleset j : NODE do
  invariant "inv_108"
    ((Chan3[j].Cmd = InvAck) -> (!(Chan2[j].Cmd = GntE)));
endruleset;


ruleset j : NODE do
  invariant "inv_106"
    ((ExGntd = true) -> (!(Cache[j].State = S)));
endruleset;


ruleset j : NODE do
  invariant "inv_100"
    (((Chan3[j].Cmd = InvAck) & (ExGntd = true)) -> (Chan3[j].Data = AuxData));
endruleset;


ruleset j : NODE do
  invariant "inv_99"
    ((Cache[j].State = E) -> (Cache[j].Data = AuxData));
endruleset;


invariant "inv_91"
  ((ExGntd = false) -> (MemData = AuxData));


ruleset j : NODE do
  invariant "inv_89"
    ((Cache[j].State = E) -> (ExGntd = true));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_66"
    ((Chan3[i].Cmd = InvAck) -> (!(Chan2[j].Cmd = GntE)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_59"
    (((Chan3[j].Cmd = InvAck) & (ExGntd = true)) -> (InvSet[i] = false));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_47"
    (((ExGntd = true) & (Chan3[i].Cmd = InvAck)) -> (InvSet[j] = false));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_44"
    ((Cache[j].State = E) -> (!(Cache[i].State = S)));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_32"
    (((ExGntd = true) & (Chan3[i].Cmd = InvAck)) -> (Chan2[j].Cmd = Empty));
endruleset;


ruleset j : NODE do
  invariant "inv_17"
    ((Cache[j].State = E) -> (Chan3[j].Cmd = Empty));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_15"
    (((Chan3[j].Cmd = InvAck) & (ExGntd = true)) -> (Chan3[i].Cmd = Empty));
endruleset;


ruleset i : NODE; j : NODE do
  invariant "inv_2"
    (((ExGntd = true) & (Chan3[i].Cmd = InvAck)) -> (Chan3[j].Cmd = Empty));
endruleset;