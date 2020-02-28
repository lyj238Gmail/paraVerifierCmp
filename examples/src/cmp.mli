 open Loach
	exception ParaNumErrors 
	exception OtherException	
	val cmpStrengthRule : ('a * Paramecium.paramref list* Loach.formula) list-> types:Paramecium.typedef list ->  int list -> rule*('a * Paramecium.paramref list*Loach.formula) list -> 
(rule*('a * Paramecium.paramref list * Loach.formula)  list) option
	 
	val cmp: Paramecium.var list->prop list->  types:Paramecium.typedef list -> Paramecium.paramref  -> int list -> ?unAbstractedParas:Paramecium.paramdef list 
 -> exp list ->rule ->
(((Paramecium.paramref list * Loach.rule)* (string * Paramecium.paramref list*Loach.formula) list) option * int list) list * (string * Paramecium.paramref list*Loach.formula)list

	
	val instantiatePr2Rules :	Paramecium.paramref ->  int list -> Paramecium.typedef list -> ?unAbstractedParas:Paramecium.paramdef list -> rule -> (Loach.rule * int list) list

	
	val cmpOnPrs: Paramecium.var list->	prop list->  types:Paramecium.typedef list -> Paramecium.paramref  -> int list -> 
	?unAbstractedReqs:(string * Paramecium.paramdef list) list   -> exp list->rule list
	 ->(Loach.rule *
            (((Paramecium.paramref list * Loach.rule) * (string * Paramecium.paramref list*Loach.formula) list) option * int list) list)
           list  * (string *Paramecium.paramref list*Loach.formula) list

	val cmpAbsProtGen:Paramecium.var list-> prop list->  types:Paramecium.typedef list -> Paramecium.paramref  -> int list -> 
	?unAbstractedReqs:(string * Paramecium.paramdef list) list   -> exp list->rule list
	 -> Loach.protocol -> Paramecium.var list ->Loach.protocol

	val cmpGenChk: Paramecium.var list-> prop list->  types:Paramecium.typedef list -> Paramecium.paramref  -> int list -> 
	?unAbstractedReqs:(string * Paramecium.paramdef list) list   -> exp list->rule list
	 -> Loach.protocol -> string list ->Paramecium.var list -> unit

	(*val get_absRules_of_pair: (Loach.rule *
            ((Loach.rule * (string *Loach.formula) list) option * int list) list)
           list  * (string *Loach.formula) list-> Loach.rule *)

	val properties2invs: Loach.prop list -> types:Paramecium.typedef list -> Paramecium.paramref -> Loach.formula list
	
	val initInvs: Loach.prop list ->  Paramecium.typedef list -> Paramecium.paramref->unit
	
	val setPrules: Loach.rule list -> unit
 
	val notConsiderTypeII:  bool ref
