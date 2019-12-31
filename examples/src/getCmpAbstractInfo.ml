open Core.Std
open RuleAbsLexer
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try RuleAbsParser.ruleAbsList RuleAbsLexer.read lexbuf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    exit (-1)
  | RuleAbsParser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)


(* part 1 
let rec parse_and_print lexbuf =
  match parse_with_error lexbuf with
  | p::ps -> p::ps
    (*let varValPair=dealVal p::ps in
				
    parse_and_print lexbuf ((p::ps)@varValLists)*)

  | [] -> varValLists *)

(*let loop filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf;
  In_channel.close inx*)

let readCmpFromStr str=
	let ()=print_endline str in
	let lexbuf = Lexing.from_string str in
  (*lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };*)

   parse_with_error lexbuf 

let readCmpFromFile fileName=
	(*let filename =   "tmpParsingFile"   in
	let out=Out_channel.create filename    in
  let ()=Out_channel.write_all filename  str in
	let ()=Out_channel.close out in*)
	let inx = In_channel.create fileName in
	let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fileName };
  parse_with_error lexbuf 

(* part 2 *)
(*let () =
  Command.basic ~summary:"Parse and display JSON"
    Command.Spec.(empty +> anon ("filename" %: file))
    loop 
  |> Command.run
*)
