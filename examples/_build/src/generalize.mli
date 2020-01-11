(** Generalize a concrete formula based on Paramecium to parameterized format
*)

open Paramecium

open Core.Std

val zero_special: bool ref
(** Convert formula *)
val form_act : ?rename:bool -> formula -> paramdef list * paramref list * formula
