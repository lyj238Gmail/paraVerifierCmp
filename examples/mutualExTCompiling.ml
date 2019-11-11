open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _I = strc "I"
let _T = strc "T"
let _C = strc "C"
let _E = strc "E"
let _true = boolc true
let _false = boolc false

let types = [
  enum "state" [_I;_T;_C;_E];
  enum "client" (int_consts [1;2]);
  enum "boolean" [_true; _false];
] 

let vardefs = List.concat[
  [arrdef [("n", [paramdef "i0" "client"])] "state"];
  [arrdef [("x",[])] "boolean"];
] 


let init=
let params=[] in
(parallel [(forStatement (parallel [(assign (record [arr [(n, [paramref i;])];]) (const _I) )])[paramdef "i" "client"]);(assign (global "x") (const _true) )])

let n_Idle=
  let name="Idle" in
  let params=[paramdef "i" "client"] in
  let formula=(eqn (record [arr [(n, [paramref i;])];])(const _E))) in
  let statement=(parallel [(assign (record [arr [(n, [paramref i;])];]) (const _I) );(assign (global "x") (const _true) )]) in
  rule name params formula statement

let n_Exit=
  let name="Exit" in
  let params=[paramdef "i" "client"] in
  let formula=(eqn (record [arr [(n, [paramref i;])];])(const _C))) in
  let statement=(parallel [(assign (record [arr [(n, [paramref i;])];]) (const _E) )]) in
  rule name params formula statement

let n_Crit=
  let name="Crit" in
  let params=[paramdef "i" "client"] in
  let formula=(andList [(eqn (record [arr [(n, [paramref i;])];])(const _T))); (eqn (global "x")(const _true)))]) in
  let statement=(parallel [(assign (record [arr [(n, [paramref i;])];]) (const _C) );(assign (global "x") (const _false) )]) in
  rule name params formula statement

let n_Try=
  let name="Try" in
  let params=[paramdef "i" "client"] in
  let formula=(eqn (record [arr [(n, [paramref i;])];])(const _I))) in
  let statement=(parallel [(assign (record [arr [(n, [paramref i;])];]) (const _T) )]) in
  rule name params formula statement

let rules = [n_Idle; n_Exit; n_Crit; n_Try]

let n_coherence=
  let name="coherence" in
  let params=[paramdef "j" "client"; paramdef "i" "client"] in
  let formula=(imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (record [arr [(n, [paramref i;])];])(const _C))) (neg (eqn (var (record [arr [(n, [paramref j;])];])) (const _C))))) in
  prop name params formula

let properties = [n_coherence]

let protocol = {
  name = "n_mutualEx";
  types;
  vardefs;
  init;
  rules;
  properties;
}

let () = run_with_cmdline (fun () ->
  let protocol = preprocess_rule_guard ~loach:protocol in
  let cinvs_with_varnames, relations = find protocol
  ~murphi:(In_channel.read_all "n_g2k.m") in
  Isabelle.protocol_act protocol cinvs_with_varnames relations ()
)
