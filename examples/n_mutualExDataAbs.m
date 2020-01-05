const 
      NODENUMS : 2;
	DATANUMS: 2;
			
type 
     state : enum{I, T, C, E};

     DATA:   1..DATANUMS;

     status : record st:state; data: DATA; end;
     
     NODE:  1..NODENUMS;

var n : array [NODE] of status;

    x : boolean; 
    
    auxDATA : DATA;
    
    memDATA: DATA;
    

ruleset i : NODE do
rule "Try" 
      n[i].st = I 
==>
begin
      n[i].st := T;
endrule;endruleset;


ruleset i : NODE do
rule "Crit"
      n[i].st = T & 
      x = true 
==>
begin
      n[i].st := C;
      x := false;
      n[i].data := memDATA; 
endrule;endruleset;


ruleset i : NODE do
rule "Exit"
      n[i].st = C 
==>
begin
      n[i].st := E;
endrule;endruleset;
      
 
ruleset i : NODE do
rule "Idle"
      n[i].st = E 
==>
begin 
      n[i].st := I;
      x := true; 
      memDATA := n[i].data; 
endrule;endruleset;

ruleset i : NODE; data : DATA do rule "Store"
	n[i].st = C
==>
begin
      auxDATA := data;
      n[i].data := data; 
endrule;endruleset;    



 


rule "ABS_Crit_NODE_1"

	x = true
 	& 
	forall NODE_2 : NODE do
		n[NODE_2].st != E &
		n[NODE_2].st != C
	end
==>
begin
	x := false;
endrule;

 


rule "ABS_Idle_NODE_1"

	forall NODE_2 : NODE do
		n[NODE_2].st != E &
		x = false &
		n[NODE_2].st != C
	end
==>
begin
	x := true ;
	memDATA := auxDATA;
endrule;

ruleset DATA_1 : DATA do
rule "ABS_Store_NODE_1"

	forall NODE_2 : NODE do
		n[NODE_2].st != E &
		x = false &
		n[NODE_2].st != C
	end
==>
begin
	auxDATA := DATA_1;
endrule;
endruleset;


startstate
begin
 for i: NODE do
    n[i].st := I; 
    n[i].data:=d;
  endfor;
  x := true;
  auxDATA := d;
  memDATA:=d;
endstartstate; 

 ruleset i:NODE; j: NODE do
invariant "coherence"
  i != j -> (n[i] = C -> n[j] != C);
endruleset;


ruleset NODE_1 : NODE ; NODE_2 : NODE do
Invariant "rule_2"
	(NODE_1 != NODE_2) ->
	(n[NODE_1].st = C -> n[NODE_2].st != C)
endruleset;

ruleset NODE_1 : NODE ; NODE_2 : NODE do
Invariant "rule_3"
	(NODE_1 != NODE_2) ->
	(n[NODE_1].st = E -> n[NODE_2].st != E)
endruleset;

ruleset NODE_1 : NODE ; NODE_2 : NODE do
Invariant "rule_4"

	(NODE_1 != NODE_2) ->
	(n[NODE_1].st = C -> n[NODE_2].st != E)

ruleset NODE_1 : NODE ; NODE_2 : NODE do
Invariant "rule_5"

	(NODE_1 != NODE_2) ->
	(n[NODE_1].st = T & x = true -> n[NODE_2].st != E)

endruleset;

ruleset NODE_1 : NODE ; NODE_2 : NODE do
Invariant "rule_6"

	(NODE_1 != NODE_2) ->
	(n[NODE_1].st = E -> n[NODE_2].st != C)

endruleset;


ruleset NODE_1 : NODE do
Invariant "rule_7"
	(n[NODE_1].st = C -> x = false)

endruleset;


ruleset NODE_1 : NODE ; NODE_2 : NODE do
Invariant "rule_8"
	(NODE_1 != NODE_2) ->
	(n[NODE_1].st = T & x = true -> n[NODE_2].st != C)

endruleset;


ruleset NODE_2 : NODE do
Invariant "rule_9"
	(x = true -> n[NODE_2].st != E)

endruleset;


ruleset NODE_1 : NODE do
Invariant "rule_10"
	(n[NODE_1].st = E -> n[NODE_1].data = auxDATA)
endruleset;


ruleset NODE_1 : NODE do
Invariant "rule_11"
	(n[NODE_1].st = E -> x = false)
end;
