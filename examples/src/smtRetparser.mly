%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> ID 
%token EOF
open Loach
%start <formula> invariant

%%
(* part 1 
ruleset i:client; j: client do
invariant "coherence"
  i != j -> (n[i] = C -> n[j] != C);
endruleset;*)

invariant:
		| RULESET; pdfs=paramdefs; DO
		INVARIANT; str=STRING; f=form; SEMICOLON; endrule 
		
paramdefs:
		|p1=paramdef; COMMA; pdfs=paramdefs
			{p1::pdfs}
		|p=paramdef
			{[p]}
		|(*empty*)
			{[]}
			
paramdef:
		|paraName=ID; COLON; 	typeName=ID
			{		
			
endrule			
		
form: 
		  
		| fl=form; AND; fr=form
			{ 
			  AndList(fl,fr)
			}
		| NOT; f=form
			{
			  Neg(f)
			}
		
			}
		| e1=exp; EQ; e2=exp
			{
			 Eqn(e1,e2)
			}
		| e1=exp; NEQ; e2=exp
			{
			 Neg(Eqn(e1,e2))
			}
		
		| LEFTBRACKET; f=form; RIGHTBRACKET
			{ 
			  f
			}
		
	exp:	
		
		 | str=ID
			{
			  Arr([(str,[])])
			}
		| e1=exp; LEFTMIDBRACKET; p=param; RIGHTMIDBRACKET
		  /* array reference. */
			{ let Arr(ls)=e1 in
				let Some(lastls)=List.nth ls (List.length ls - 1)  } in
				let lsRemainder=List.rev (List.tl (List.rev ls)) in
				Arr(lsRemainder@[(lastls, [p])])
			}
			
		| e1=exp; DOT; str=ID
		  /* record reference. */
			{ 
			 let Arr(ls)=e1  in
			 Arr(ls@[(str,[])])
			}  
			
	param:
		 
		| idStr=ID		  {paramref idStr}
