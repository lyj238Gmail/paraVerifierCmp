
open Utils
open Core.Std

open Paramecium
open ToStr



type edge =
	  
	Edge of string * string *string * formula * formula 
with sexp

let edgeTab = Core.Std.Hashtbl.create ~hashable:Core.Std.String.hashable ()

let nodePreTab=Core.Std.Hashtbl.create ~hashable:Core.Std.String.hashable ()

type graph=
	AG of (edge list) * string
	
let edgeNodes2Edge (n,n')=
	Core.Std.find edgeTab ~key:(n^n')

let edgesList2Tab edges=
	List.map ~f:(fun (name,n,n',antf,consf)
		->Core.Std.Hashtbl.replace edgeTab ~key:(n^n') (name,n,n',antf,consf))
	edges
	
let edges2NodePreTab =
	List.map ~f:(fun (name,n,n',antf,consf)
		->match Core.Std.Hashtbl.find nodePreTab ~key:n' with
		|None ->Core.Std.Hashtbl.replace nodePreTab ~key:n' (~data:[(n,n')])
		|Some(L)->Core.Std.Hashtbl.replace nodePreTab ~key:n' (~data:((n,n')::L)))
	edges
	
let sink e=
	let (name,n,n',antf,consf)=e in
	n'
	
let source e=
	let (name,n,n',antf,consf)=e in
	n
	
let ant e =
	let (name,n,n',antf,consf)=e in
	antf

let cons e =
	let (name,n,n',antf,consf)=e in
	consf

let preEdges n'	=
	Core.Std.Hashtbl.find nodePreTab ~key:n'
	
	
let preNodes n'=
	List.map ~f:fst (preEdges n')
	
let edges g=
	let AG(es,ini)=g in
	es
	
let nodes g=
	let es =edges g in
	let ls=List.fold es ~f:(fun xs x=xs@[(sink x),(source x)]) ~init:[] in
	List.dedup ls
	
	
	