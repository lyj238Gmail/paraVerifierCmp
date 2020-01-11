%{ let paramStack=ref [] %}
%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> ID 
%token EOF
%token DO
%token DOT
%token EQ
%token END
%token ENDRULE
%token LEFTBRACKET
%token RIGHTBRACKET
%token  LEFTMIDBRACK
%token  RIGHTMIDBRACK
%token AND
%token NOT
%token COLON
%token  SEMICOLON
%token  INVARIANT
%token  NEQ
%token COMMA
%token RULESET
%token  IMPLIES

%left IMPLIES
%left AND 
%left NOT
%start <Loach.prop option > invariant 

%%
(* 
%start <Loach.prop list> invariantList
part 1 
ruleset i:client; j: client do
invariant "coherence"
  i != j -> (n[i] = C -> n[j] != C);
endruleset;
invariantList:
	invs=separated_list(SEMICOLON,invariant) {invs};*)


	(*| invs=invariantList; SEMICOLON; inv=invariant
	   {invs@[inv]};

	| inv=invariant; SEMICOLON
	  {[inv]};
	
	|{[]};*)

invariant:
		| RULESET; pdfs=paramdefs; SEMICOLON; DO;
		INVARIANT; str=STRING; f=form; SEMICOLON; ENDRULE;  SEMICOLON
		{let ()=paramStack:=  [] in Some(Prop(("inv_"^str),pdfs,f))};
		

		| RULESET; pdfs=paramdefs;  DO;
		INVARIANT; str=STRING; f=form; SEMICOLON; ENDRULE;  SEMICOLON
		{let ()=paramStack:= [] in Some(Prop(("inv_"^str),pdfs,f))};
		
		
		|INVARIANT; str=STRING; f=form; SEMICOLON;  
			{let ()=paramStack:= [] in Some(Prop(("inv_"^str),[],f))};
		
		|EOF {None}
		
paramdefs:  (*pdfs= separated_list(SEMICOLON,paramdef) {pdfs}*)
		|pdfs=paramdefs; SEMICOLON; p1=paramdef
			{ p1::pdfs}
		|p=paramdef
			{[p]}
		|{[]} ;
			
paramdef:
		|paraName=ID; COLON; 	typeName=ID
			{	let ()=paramStack:= paraName::(! paramStack) in
			  Paramecium.Paramdef(paraName,typeName)};
			

		
form: 
		
		
				
			
		| e1=exp; EQ; e2=exp
			{
			 Eqn(e1,e2)
			}
		| e1=exp; NEQ; e2=exp
			{
			 Neg(Eqn(e1,e2))
			}
			
		| NOT; f=form
			{
			  Neg(f)
			}	
		
		| LEFTBRACKET; f=form; RIGHTBRACKET
			{ 
			  f
			};
			
		| fl=form; AND; fr=form
			{ 
			  Loach.AndList([fl;fr])
			}	
			
		| fl=form; IMPLIES; fr=form
			{ 
			  Loach.Imply(fl,fr)
			}  	
		
	exp:	
		 intv=INT      {Loach.Param(Paramecium.paramfix "tmp" "NODE" (Paramecium.Intc(intv)))};
		
		 | str=ID
			{ if (List.mem str (! PublicVariables.enumStrings))				
			  then (Loach.const (Paramecium.strc str))
				else if (str="true" )
				then (Loach.const (Paramecium.boolc true))
				else if (str="false" )
				then (Loach.const (Paramecium.boolc false))
				else if (List.mem str (! paramStack))
				then (Loach.param (Paramecium.paramref str))
			  else Loach.Var(Arr([(str,[])]))
			}
		| e1=exp; LEFTMIDBRACK; p=param; RIGHTMIDBRACK
		  /* array reference. */
			{ let Loach.Var(Arr(ls))=e1 in
				let (pair)=(List.nth ls (List.length ls - 1))   in
				let (x,lastls)=pair in
				let lsRemainder=List.rev (List.tl (List.rev ls)) in
				Var(Arr(lsRemainder@[(x, [p])]))
			}
			
		| e1=exp; DOT; str=ID
		  /* record reference. */
			{ 
			 let  Loach.Var(Paramecium.Arr(ls))=e1  in
			  Var(Paramecium.Arr(ls@[(str,[])]))
			}  ;
			
	param:
		 
		| idStr=ID		  {Paramecium.paramref idStr};
		
		| intv=INT      {Paramecium.paramfix "tmp" "NODE" (Paramecium.Intc(intv))};
		
 /*endrule:
	  |ENDRULE {}
	  |END		{};*/
