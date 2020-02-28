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
CurPtr :  union{NODE,enum{other}};
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
  ((CurCmd = ReqE) & (CurPtr = 3) & (ExGntd = false) & (forall j : NODE do (ShrSet[j] = false) endforall) & (forall p__Inv2 : NODE do (!(Chan2[p__Inv2].Cmd = GntE)) endforall) & (forall p__Inv2 : NODE do (!(Cache[p__Inv2].State = E)) endforall) & (!(!(MemData = AuxData)))) ==>
begin
  ExGntd := true;
  CurCmd := Empty;
endrule;


rule "n_SendGntS4_i_3"
  ((CurCmd = ReqS) & (CurPtr = 3) & (ExGntd = false) & (forall p__Inv2 : NODE do (!(Chan2[p__Inv2].Cmd = GntE)) endforall) & (forall p__Inv2 : NODE do (!(Cache[p__Inv2].State = E)) endforall) & (!(!(MemData = AuxData))) & (forall p__Inv2 : NODE do (!(Chan3[p__Inv2].Cmd = InvAck)) endforall) & (forall p__Inv2 : NODE do (!(Chan2[p__Inv2].Cmd = Inv)) endforall)) ==>
begin
  CurCmd := Empty;
endrule;


rule "n_RecvInvAck5_i_3"
  ((ExGntd = true) & (forall p__Inv2 : NODE do (!(Chan2[p__Inv2].Cmd = GntS)) endforall) & (!(CurCmd = Empty)) & (forall p__Inv1 : NODE do (!(Chan2[p__Inv1].Cmd = GntE)) endforall) & (forall p__Inv1 : NODE do (!(Cache[p__Inv1].State = E)) endforall) & (forall p__Inv2 : NODE do (!(Chan2[p__Inv2].Cmd = GntE)) endforall) & (forall p__Inv2 : NODE do (!(Cache[p__Inv2].State = E)) endforall) & (forall p__Inv2 : NODE do (!(ShrSet[p__Inv2] = true)) endforall) & (forall p__Inv1 : NODE do (!(ShrSet[p__Inv1] = true)) endforall)) ==>
begin
  ExGntd := false;
  MemData := AuxData;
endrule;


rule "n_RecvReqE11_i_3"
  ((CurCmd = Empty) & (forall p__Inv2 : NODE do (!(Chan3[p__Inv2].Cmd = InvAck)) endforall) & (forall p__Inv2 : NODE do (!(Chan2[p__Inv2].Cmd = Inv)) endforall)) ==>
begin
  CurCmd := ReqE;
  CurPtr := 3;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  endfor;
endrule;


rule "n_RecvReqS12_i_3"
  ((CurCmd = Empty) & (forall p__Inv2 : NODE do (!(Chan3[p__Inv2].Cmd = InvAck)) endforall) & (forall p__Inv2 : NODE do (!(Chan2[p__Inv2].Cmd = Inv)) endforall)) ==>
begin
  CurCmd := ReqS;
  CurPtr := 3;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  endfor;
endrule;


ruleset d : DATA do
  rule "n_Store_i_3"
    ((forall p__Inv1 : NODE do (!(ShrSet[p__Inv1] = true)) endforall) & (forall p__Inv2 : NODE do (!(InvSet[p__Inv2] = true)) endforall) & (!(ExGntd = false)) & (forall p__Inv2 : NODE do (!(Chan3[p__Inv2].Cmd = InvAck)) endforall) & (forall p__Inv1 : NODE do (!(Chan2[p__Inv1].Cmd = Inv)) endforall) & (forall p__Inv2 : NODE do (!(Chan2[p__Inv2].Cmd = GntS)) endforall) & (forall p__Inv2 : NODE do (!(Chan2[p__Inv2].Cmd = GntE)) endforall) & (forall p__Inv1 : NODE do (!(!(Cache[p__Inv1].State = I))) endforall) & (forall p__Inv1 : NODE do (!(Chan2[p__Inv1].Cmd = GntE)) endforall) & (forall p__Inv2 : NODE do (!(Cache[p__Inv2].State = E)) endforall) & (forall p__Inv2 : NODE do (!(Chan2[p__Inv2].Cmd = GntE)) endforall) & (forall p__Inv2 : NODE do (!(Cache[p__Inv2].State = E)) endforall) & (forall p__Inv2 : NODE do (!(ShrSet[p__Inv2] = true)) endforall) & (forall p__Inv2 : NODE do (!(Chan2[p__Inv2].Cmd = GntS)) endforall) & (forall p__Inv1 : NODE do (!(ShrSet[p__Inv1] = true)) endforall)) ==>
  begin
    AuxData := d;
  endrule;
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__511"
    ((!(p__Inv1 = p__Inv2)) -> (((ExGntd = true) & (ShrSet[p__Inv2] = true)) -> (!(ShrSet[p__Inv1] = true))));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__513"
    ((!(p__Inv1 = p__Inv2)) -> (((ShrSet[p__Inv1] = true) & (ExGntd = true)) -> (!(ShrSet[p__Inv2] = true))));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__4422"
    (((CurCmd = ReqS) & (ExGntd = false)) -> (!(Chan3[p__Inv2].Cmd = InvAck)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__4325"
    (((CurCmd = Empty)) -> (!(Chan3[p__Inv2].Cmd = InvAck)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__4326"
    (((Chan3[p__Inv2].Cmd = InvAck)) -> (!(CurCmd = Empty)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__4227"
    (((CurCmd = ReqS) & (ExGntd = false)) -> (!(Chan2[p__Inv2].Cmd = Inv)));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__4130"
    ((!(p__Inv1 = p__Inv2)) -> (((ShrSet[p__Inv1] = true)) -> (!(Chan2[p__Inv2].Cmd = GntE))));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__4032"
    (((Chan3[p__Inv2].Cmd = InvAck)) -> (!(Chan2[p__Inv2].Cmd = GntS)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__3934"
    (((Chan3[p__Inv2].Cmd = InvAck)) -> (!(InvSet[p__Inv2] = true)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__3837"
    (((CurCmd = Empty)) -> (!(Chan2[p__Inv2].Cmd = Inv)));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__3738"
    ((!(p__Inv1 = p__Inv2)) -> (((ShrSet[p__Inv1] = true)) -> (!(Cache[p__Inv2].State = E))));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__3739"
    ((!(p__Inv1 = p__Inv2)) -> (((Cache[p__Inv2].State = E)) -> (!(ShrSet[p__Inv1] = true))));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__3543"
    (((ShrSet[p__Inv2] = false)) -> (!(Chan2[p__Inv2].Cmd = GntE)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__3444"
    (((Chan3[p__Inv2].Cmd = InvAck)) -> (!(!(Cache[p__Inv2].State = I))));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__3445"
    (((!(Cache[p__Inv2].State = I))) -> (!(Chan3[p__Inv2].Cmd = InvAck)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__3346"
    (((ShrSet[p__Inv2] = false)) -> (!(Chan2[p__Inv2].Cmd = GntS)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__3248"
    (((Chan3[p__Inv2].Cmd = InvAck)) -> (!(Chan2[p__Inv2].Cmd = Inv)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__3151"
    (((ExGntd = true)) -> (!(Chan2[p__Inv2].Cmd = GntS)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__3052"
    (((ShrSet[p__Inv2] = false)) -> (!(InvSet[p__Inv2] = true)));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__2762"
    ((!(p__Inv1 = p__Inv2)) -> (((Cache[p__Inv1].State = E)) -> (!(InvSet[p__Inv2] = true))));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__2467"
    (((ShrSet[p__Inv2] = false)) -> (!(!(Cache[p__Inv2].State = I))));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__2468"
    (((!(Cache[p__Inv2].State = I))) -> (!(ShrSet[p__Inv2] = false)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__2271"
    (((ShrSet[p__Inv2] = false)) -> (!(Chan2[p__Inv2].Cmd = Inv)));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__2078"
    ((!(p__Inv1 = p__Inv2)) -> (((Cache[p__Inv2].State = E)) -> (!(Chan2[p__Inv1].Cmd = Inv))));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__1979"
    ((!(p__Inv1 = p__Inv2)) -> (((Chan3[p__Inv2].Cmd = InvAck)) -> (!(Chan2[p__Inv1].Cmd = GntE))));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__1881"
    (((Chan3[p__Inv2].Cmd = InvAck)) -> (!(Chan2[p__Inv2].Cmd = GntE)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__1783"
    (((Cache[p__Inv2].State = E)) -> (!(Chan2[p__Inv2].Cmd = GntE)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__1685"
    (((Cache[p__Inv2].State = E)) -> (!(Chan2[p__Inv2].Cmd = GntS)));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__1588"
    ((!(p__Inv1 = p__Inv2)) -> (((Cache[p__Inv1].State = E)) -> (!(Chan2[p__Inv2].Cmd = GntE))));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__1490"
    ((!(p__Inv1 = p__Inv2)) -> (((!(Cache[p__Inv2].State = I))) -> (!(Chan2[p__Inv1].Cmd = GntE))));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__1392"
    ((!(p__Inv1 = p__Inv2)) -> (((Cache[p__Inv1].State = E)) -> (!(Chan2[p__Inv2].Cmd = GntS))));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__1293"
    (((ShrSet[p__Inv2] = false)) -> (!(Chan3[p__Inv2].Cmd = InvAck)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__1294"
    (((Chan3[p__Inv2].Cmd = InvAck)) -> (!(ShrSet[p__Inv2] = false)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__1197"
    (((ExGntd = true) & (!(Cache[p__Inv2].State = E))) -> (!(Chan2[p__Inv2].Cmd = Inv)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__1099"
    (((ExGntd = false)) -> (!(Chan2[p__Inv2].Cmd = GntE)));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__9100"
    ((!(p__Inv1 = p__Inv2)) -> (((Chan3[p__Inv2].Cmd = InvAck)) -> (!(Cache[p__Inv1].State = E))));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__9101"
    ((!(p__Inv1 = p__Inv2)) -> (((Cache[p__Inv1].State = E)) -> (!(Chan3[p__Inv2].Cmd = InvAck))));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__8102"
    (((Chan3[p__Inv2].Cmd = InvAck)) -> (!(Cache[p__Inv2].State = E)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__8103"
    (((Cache[p__Inv2].State = E)) -> (!(Chan3[p__Inv2].Cmd = InvAck)));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__5108"
    ((!(p__Inv1 = p__Inv2)) -> (((Cache[p__Inv2].State = E)) -> (!(!(Cache[p__Inv1].State = I)))));
endruleset;


ruleset p__Inv1 : NODE; p__Inv2 : NODE do
  invariant "inv_inv__5109"
    ((!(p__Inv1 = p__Inv2)) -> (((!(Cache[p__Inv1].State = I))) -> (!(Cache[p__Inv2].State = E))));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__4110"
    (((ExGntd = true) & (Chan3[p__Inv2].Cmd = InvAck)) -> (!(!(Chan3[p__Inv2].Data = AuxData))));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__3113"
    (((Cache[p__Inv2].State = E)) -> (!(ExGntd = false)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__3114"
    (((ExGntd = false)) -> (!(Cache[p__Inv2].State = E)));
endruleset;


ruleset p__Inv2 : NODE do
  invariant "inv_inv__2116"
    (((!(Cache[p__Inv2].State = I))) -> (!(!(Cache[p__Inv2].Data = AuxData))));
endruleset;


invariant "inv_inv__1118"
  (((ExGntd = false)) -> (!(!(MemData = AuxData))));
