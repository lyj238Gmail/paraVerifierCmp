 open Loach
	exception ParaNumErrors 
	exception OtherException	
	val cmpStrengthRule : ('a * Loach.formula) list-> types:Paramecium.typedef list ->  int list -> rule*('a * Loach.formula) list -> (rule*('a * Loach.formula)  list) option
	 
	val cmp: prop list->  types:Paramecium.typedef list -> Paramecium.paramref  -> int list -> ?unAbstractedParas:Paramecium.paramdef list 
 -> exp list ->rule ->(((Paramecium.paramref list * Loach.rule)* (string *Loach.formula) list) option * int list) list * (string *Loach.formula)list

	
	val instantiatePr2Rules :	Paramecium.paramref ->  int list -> Paramecium.typedef list -> ?unAbstractedParas:Paramecium.paramdef list -> rule -> (Loach.rule * int list) list

	
	val cmpOnPrs: 	prop list->  types:Paramecium.typedef list -> Paramecium.paramref  -> int list -> 
	?unAbstractedReqs:(string * Paramecium.paramdef list) list   -> exp list->rule list
	 ->(Loach.rule *
            (((Paramecium.paramref list * Loach.rule) * (string *Loach.formula) list) option * int list) list)
           list  * (string *Loach.formula) list

	val cmpAbsProtGen: prop list->  types:Paramecium.typedef list -> Paramecium.paramref  -> int list -> 
	?unAbstractedReqs:(string * Paramecium.paramdef list) list   -> exp list->rule list
	 -> Loach.protocol -> Loach.protocol

	(*val get_absRules_of_pair: (Loach.rule *
            ((Loach.rule * (string *Loach.formula) list) option * int list) list)
           list  * (string *Loach.formula) list-> Loach.rule *)

	val properties2invs: Loach.prop list -> types:Paramecium.typedef list -> Paramecium.paramref -> Loach.formula list
	
	val initInvs: Loach.prop list ->  Paramecium.typedef list -> Paramecium.paramref->unit
	
	val setPrules: Loach.rule list -> unit
 
