open Core.Std
open Lexer
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.invariant Lexer.read lexbuf with
  | SyntaxError msg ->
    let ()=fprintf stderr "%a: %s\n" print_position lexbuf msg in
    exit(1)
    
  | Parser.Error ->
    let ()=fprintf stderr "%a: syntax error\n" print_position lexbuf in
    exit(1)

(* part 1 *)
let rec parse_and_print  oldInvs lexbuf=
	 let result=parse_with_error lexbuf in
	
   match result with
   |Some(result)->
    let Loach.Prop(name,paradefs,f)=result in
	(*let Some(Loach.Prop(name,paradefs,f))=List.nth result 1 in*)
	 (*let ()=print_endline ("this is"^(ToMurphi.form_act f)) in *)
    parse_and_print (result::oldInvs) lexbuf 
   |None ->oldInvs

let loop filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  let () =
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename } in
  let invs= parse_and_print [] lexbuf in
  let ()=In_channel.close inx in
  invs
   
   

(* part 2 
let loop filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf;
  In_channel.close inx*)
  
(*let a =
   loop "testInv.txt" () in ();*)
 (* let publicVariables=["InvAck","Inv"] in
  Command.basic ~summary:"Parse and display JSON"
    Command.Spec.(empty +> anon ("filename" %: file))
    loop 
  |> Command.run*)
   
