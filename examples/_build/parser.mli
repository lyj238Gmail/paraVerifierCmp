exception Error

type token = 
  | STRING of (string)
  | SEMICOLON
  | RULESET
  | RIGHTMIDBRACK
  | RIGHTBRACKET
  | NOT
  | NEQ
  | LEFTMIDBRACK
  | LEFTBRACKET
  | INVARIANT
  | INT of (int)
  | IMPLIES
  | ID of (string)
  | FLOAT of (float)
  | EQ
  | EOF
  | ENDRULE
  | END
  | DOT
  | DO
  | COMMA
  | COLON
  | AND


val invariant: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Loach.prop option )