open Ast

let debug : string -> unit = fun msg -> print_endline("DEBUG: "^msg)
let info : string -> unit = fun msg -> print_endline ("INFO: "^msg)
let warning : string -> unit = fun msg -> ()
let error : string -> unit = fun msg -> print_endline ("ERROR: "^msg)
let fatal_error : string -> 'a = fun msg -> error msg; exit 1
let critical : string -> unit = fun msg -> ()

let error_t : term -> string -> 'a = fun t -> fun msg -> 
   print_endline( "ERROR: "^msg )

let fatal_error_t : term -> string -> 'a = fun t -> fun msg -> 
   error_t t msg; exit 1
