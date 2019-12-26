%token <string> INTEGER
%token <string> ID 
%token  LEFT_MIDBRACE
%token RIGHT_MIDBRACE
%token EQ
%token COMMA
%token SENDTO
%token LEFT_BRACE
%token RIGHT_BRACE
%token ELSE 
%token EOF

%start <(string * string) list> smtModel

%%


(* Try:
NoAbstractRule

Idle:
[i],ABS_Idle_i, [rule_10,rule_6,rule_3,rule_11],[]

*)



ruleAbsList: 
	|item=ruleAbs {[item]}
	|item=ruleAbs  items=ruleAbsList {item::items}

ruleAbs:
	|"NoAbstractRule"
	|identList; COMMA; ID; COMMA; ID; COMMA; identList

identList:
	|

(*funRetEle:
		| varName=ID; EQ; LEFT_MIDBRACE;   vals=retVals; RIGHT_MIDBRACE 
			{let keyFun e=((Core.Std.String.concat ~sep:"" [varName; "["; fst e; "]"]),  snd e) in
			 let keys=Core.Std.List.map ~f:keyFun vals in
						keys}

	  | varName=ID; EQ; oneVal=eleVal {[(varName,oneVal)]}

funList:  
  funLists = separated_list(COMMA, funRetEle)    {let ()=print_endline "fls" in Core.Std.List.concat funLists } ; 

retVals:
	retvals0= separated_list(COMMA, indexEle)    { Core.Std.List.concat retvals0 };

(*funRetEle:
	EFT_MIDBRACE; indexele=indexEle; RIGHT_MIDBRACE {indexele}	*)

indexEle:
	|LEFT_BRACE ; indexes=separated_list(COMMA,index); RIGHT_BRACE; SENDTO; rightVal=eleVal {[(Core.Std.String.concat ~sep:";" indexes, rightVal) ]}

	|indexStr=index; SENDTO; rightVal=eleVal {[(indexStr,rightVal)]}

	|ELSE; SENDTO; eleVal {[]}

index:
	|intVal=INTEGER { intVal} 


eleVal:
	|intVal=INTEGER {intVal}
	|enumVal=ID {enumVal}
*)
			
	
