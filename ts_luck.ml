open Ast

open CharParse
open CharPrim
open CharComb
open CharExpr


class checker : type_system = object
   method parse (st: unit CharParse.CharPrim.state) : (unit, typ) CharParse.CharPrim.rcon = (return "") st
   method check : (int*(typ list)) list -> (int*int*int) list -> (int*typ) list = assert false
   method new_tarr : (typ option * typ option * typ option) -> (typ*typ*typ) = assert false
   method new_tvar : unit -> typ = assert false
end

(*
   + tuples
   + union types (tagged unions built like (T1,...)|(T2,...) using tuples and union)
   + polymorphic types
   + parametric polymorphism
   + universal quantified types 
   + labeled types and optional arguments
   + proof carrying types
*)

