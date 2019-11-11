open Utils
open Core.Std
let b=Utils.list_subtract [1;2;3] [1;2] in
print_endline (sprintf"length%d,hd is%d\n" (List.length b) (let Some(ele)n=List.hd b in ele))
