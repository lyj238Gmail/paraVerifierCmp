{
open Lexing
open Parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}


(* part 1 *)
(*let int = '-'? ['0'-'9'] ['0'-'9']**)

(* part 2 *)
(*let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?*)

(* part 3 *)
(*let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']**)

(* part 4 ruleset  i : NODE ;j : NODE do
invariant "19"
i != j -> 
  (Chan3[i].Cmd = InvAck & ExGntd = true -> !Chan2[j].Cmd = Inv);

endruleset;*)

let letter=	['a'-'z''A'-'Z']
let digit	=	['0'-'9']

let integer=	(digit+) 
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id=		['a'-'z''A'-'Z'] ['a'-'z''A'-'Z' '0'-'9' '_' ] *(*letter(letter|digit)**)
 
rule read =
  parse
  | white    { read lexbuf }
  | newline  { next_line lexbuf; read lexbuf }
  | integer   { INT (int_of_string (Lexing.lexeme lexbuf)) }
  |"invariant" {(INVARIANT)}
  | "end"        { (END)}
  |"endruleset"   { (ENDRULE)}
  |"ruleset"   { (RULESET)}
  |"do"        { (DO)}
    (*{ID (Lexing.lexeme lexbuf)}*)
  | '!'	   { ( NOT ) }
  | "!="		 { (NEQ) }  
  | "->"		 { ( IMPLIES ) }
  | '&'      { (AND)} 
  | '='      {(EQ)}
  | '('      {(LEFTBRACKET)}
  | ')'      {(RIGHTBRACKET)}
  | '['      {( LEFTMIDBRACK) }  
  | ']'      {( RIGHTMIDBRACK)}
  
  | '.'       { (DOT)}
  | ':'       { (COLON)}
  | ';'       { (SEMICOLON)}
  | ','       { (COMMA)}
  
  | '"'      { read_string (Buffer.create 17) lexbuf }
  | id     as s { ID (s) } 
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }  
  | eof      { EOF }
  
(* part 5 *)
and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }
