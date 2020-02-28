open Utils
open Paramecium



open Loach

open Core.Std
 
(** Convert statement*)
val form_act: generalizedtParas:const list -> ?rename:bool ->formula ->Paramecium.paramdef list ->
Paramecium.paramref list -> Paramecium.paramdef list *Paramecium.paramref list * formula


val statement_act: generalizedtParas:const list -> ?rename:bool ->statement ->Paramecium.paramdef list ->
Paramecium.paramref list -> Paramecium.paramdef list *Paramecium.paramref list * statement

val rule_act :  generalizedtParas:const list -> ?rename:bool ->rule ->rule

val concreteInv2ParamProp: formula -> int ->prop
