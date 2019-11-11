open Paramecium
open Core.Std

let enumStrings=ref ["E"]

let extractEnumString c=
	match c with
	|Strc(str)-> [str]
	|Boolc(b)->[]
	|Intc(i)-> []

let extractEnumStringFromEnums cs=
	List.concat (List.map ~f:	extractEnumString cs)
(*let types = [
  enum "state" [_I; _T; _C; _E];
  enum "client" (int_consts [1; 2]);
  enum "boolean" [_True; _False];
]*)
	
let extractTypeItem typeItem=
	match typeItem with
	Enum(name, consts) -> extractEnumStringFromEnums consts
	
let extract types=
	List.concat (List.map ~f:	extractTypeItem types)
