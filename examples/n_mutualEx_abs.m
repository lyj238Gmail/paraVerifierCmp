type
  state : enum{I, T, C, E};
  client : scalarset(2);






var
x :  boolean;
n : array [client] of state;


startstate
begin
  for i : client do
    n[i] := I;
  endfor;
  x := true;
endstartstate;


ruleset i : client do
  rule "n_Try"
    (n[i] = I) ==>
  begin
    n[i] := T;
  endrule;
endruleset;


ruleset i : client do
  rule "n_Crit"
    ((n[i] = T) & (x = true)) ==>
  begin
    n[i] := C;
    x := false;
  endrule;
endruleset;


ruleset i : client do
  rule "n_Exit"
    (n[i] = C) ==>
  begin
    n[i] := E;
  endrule;
endruleset;


ruleset i : client do
  rule "n_Idle"
    (n[i] = E) ==>
  begin
    n[i] := I;
    x := true;
  endrule;
endruleset;


rule "n_Crit_i_3"
  ((x = true)) ==>
begin
  x := false;
endrule;


rule "n_Idle_i_3"
  ((x = false) & (forall j : client do (!(n[j] = E)) endforall) & (forall j : client do (!(n[j] = C)) endforall)) ==>
begin
  x := true;
endrule;


ruleset i : client do
  invariant "inv_27"
    ((n[i] = E) -> (x = false));
endruleset;


ruleset i : client; j : client do
  invariant "inv_7"
    ((!(i = j)) -> ((n[i] = E) -> (!(n[j] = E))));
endruleset;


ruleset i : client; j : client do
  invariant "inv_5"
    ((!(i = j)) -> ((n[i] = E) -> (!(n[j] = C))));
endruleset;