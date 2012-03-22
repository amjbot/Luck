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
