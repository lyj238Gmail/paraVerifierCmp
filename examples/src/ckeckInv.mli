open Core.Std
open Utils
open Paramecium
module CheckInv=sig	
val startServer: 
  ?smv_escape:(string -> string) ->
  ?smv:string -> ?smv_ord:string ->
  ?murphi:string -> 
  string->string->string->string->string->typedef:Paramecium.typedef list->vardefs:Paramecium.vardef list ->
  Loach.protocol -> unit 
  
val checkProps:	Paramecium.typedef list ->prop list-> prop list

(*inv:invStrInMurphi*)
val checkInv:P aramecium.typedef list ->Loach.formula->bool
val checkInvStr: string->bool
end
