exception Error

type token = 
  | SENDTO
  | RIGHT_MIDBRACE
  | RIGHT_BRACE
  | NOABS
  | LEFT_MIDBRACE
  | LEFT_BRACE
  | INTEGER of (string)
  | ID of (string)
  | EQ
  | EOF
  | ELSE
  | COMMA
  | COLON


val ruleAbsList: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> ((string*(int * string list * string * string list *string list) list) list)