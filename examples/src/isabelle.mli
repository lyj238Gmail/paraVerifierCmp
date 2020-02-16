(** Generate Isabelle code
*)

open Core.Std

exception Unsupported of string
val absRules:  (string list) ref
val rule_quant_table: (string,string)   Hashtbl.t
val types_ref: Paramecium.typedef list ref
val get_pd_name_list : Paramecium.paramdef list->string
val analyze_rels_in_pds : ?quant:string ->string ->string->Paramecium.paramdef list->string
val const_act : Paramecium.const -> string option
val type_act : Paramecium.typedef -> string option
val var_act : Paramecium.var -> string
val var_act' : Paramecium.var -> string
val exp_act : Loach.exp -> string
val formula_act : Loach.formula -> string
val rules_act:Loach.rule list-> string

val rules_actCmp:Loach.rule list-> string
val invs_act:InvFinder.concrete_prop list -> string
val file_root':string->unit
val file_sh':string ->unit

val inits_act :Loach.statement   -> string

val invs_act_without_neg:InvFinder.concrete_prop list -> string
val file_pub:string ->string ->string ->string ->string->unit->unit
val protocol_act : Loach.protocol -> (InvFinder.concrete_prop * String.Set.t) list ->
  InvFinder.t list list list list -> unit -> unit
