open Misc
open Ast
open Log

module LuckLD : Language.LanguageDef =
struct
  open CharParse.CharPrim
  open CharParse.M

  let commentStart = "(*"
  let commentEnd = "*)"
  let commentLine = "#"
  let nestedComments = true
  let identStart = letter (* of course, a leading prime is used in the
                             case of tyvars, but it's easiest to handle
                             these seperately *)
  let identLetter st = (alphaNum <|> (char '_')) st
  let reservedOpNames = ["[";"]";"{";"}";"(";")";";";":";",";"'"]
  let opStart st = oneOf (explode "!%&$#+-/:<=>>@\\~'^|*") st
  let opLetter st = oneOf (List.filter (fun i -> not (List.mem (String.make 1 i) reservedOpNames)) (explode "!%&$#+-/:<=>>@\\~'^|*")) st
  let reservedNames =
    ["_"; "and"; "as"; "case"; "catch"; "do"; "else";
     "fn"; "for"; "function"; "if"; "import"; "in";
     "let"; "new"; "of"; "or"; "property"; "then"; "throw";
     "type"; "with"; "while"]

  (* cannot be used in user-defined operators *)

  let caseSensitive = true

  let negSign st = (char '-') st
  let posSign = mzero

end

module L = Language.M(LuckLD)
open L
open CharParse
open CharPrim
open CharComb
open CharExpr


type st_type = ST_Ground of string | ST_Arrow of st_type * st_type | ST_Var of int
class checker: type_system = object (this)
   method parse (st: unit CharParse.CharPrim.state) : (unit, typ) CharParse.CharPrim.rcon =
      ( this#parse_internal_type >>= fun tt -> (return (this#pp_type tt)) ) st
   val var_count = ref 0
   val var_cache : (string,int) hash_table = new hashtable
   method private new_st_tvar () = let tvar = ST_Var !var_count in incr var_count; tvar
   method new_tvar () = this#pp_type (this#new_st_tvar())
   method private get_tvar (s: string) = if not (var_cache#has s) then var_cache#set s !var_count; incr var_count; ST_Var (var_cache#get s)
   method private parse_internal_atom (st: unit CharParse.CharPrim.state) : (unit, st_type) CharParse.CharPrim.rcon = (
      ( symbolChar '\'' >> (
         (identifier >>= fun v -> return (this#get_tvar v)) <|>
         (integer >>= fun n -> return (ST_Var n))
      )) <|>
      ( identifier >>= fun v -> return (ST_Ground v) ) <|>
      (parens this#parse_internal_type)
   ) st
   method private parse_internal_type (st: unit CharParse.CharPrim.state) : (unit, st_type) CharParse.CharPrim.rcon = (
      (sepBy1 this#parse_internal_atom (reservedOp "->")) >>= fun ts -> return (
         let ts = List.rev ts in 
         List.fold_left (fun r l -> ST_Arrow(l,r)) (List.hd ts) (List.tl ts)
      )
   ) st
   method private parse_internal (i: int) (tt: string): st_type = (
      var_cache#clear ();
      match parse "type" (LazyList.M.ofString tt)
        (whiteSpace >> this#parse_internal_type >>= fun r -> eof >> return r) with
        Success x -> x
      | Failure err -> raise (TypeError (i, ("In <string> "^(Error.M.errorToString err))))
   )
   method private pp_type (tt: st_type): string = match tt with
   | ST_Var v -> "'"^(string_of_int v)
   | ST_Ground g -> g
   | ST_Arrow (p,b) -> "("^(this#pp_type p)^" -> "^(this#pp_type b)^")"
   method new_tarr : (typ option * typ option * typ option) -> (typ*typ*typ) = fun (mpt,mbt,mtt) -> (
      let pt = this#parse_internal 0 (match mpt with Some tt -> tt | None -> this#new_tvar()) in
      let bt = this#parse_internal 0 (match mbt with Some tt -> tt | None -> this#new_tvar()) in
      let tt = match mtt with Some tt -> assert false | None -> ST_Arrow(pt,bt) in
      ((this#pp_type pt),(this#pp_type bt),(this#pp_type tt))
   )
   method check (objects :(int*(typ list)) list) (arrows :(int*int*int) list): (int*typ) list = (
      let objects : (int*(st_type list)) list = 
      List.map (fun (i,ts) -> i, List.map (fun tt -> this#parse_internal i tt) ts) objects in
      let type_context : (int,st_type) hash_table = new hashtable in
      List.iter( fun (i,ts) -> List.iter( fun tt ->
          if type_context#has i then assert false 
          else type_context#set i tt
      ) ts ) objects;
      let type_lookup (i: int) = if not (type_context#has i) then type_context#set i (this#new_st_tvar()); type_context#get i in
      let rec sub_tvar (i: int) (rt: st_type) = function
      | ST_Arrow (pt,bt) -> ST_Arrow (sub_tvar i rt pt, sub_tvar i rt bt)
      | ST_Var v -> if v=i then rt else ST_Var v
      | tt -> tt in
      let fresh = ref true in
      while !fresh do fresh := false; List.iter( fun (l,r,t) ->
          let lt = type_lookup l in
          let rt = type_lookup r in
          let tt = type_lookup t in
          (match (lt,rt) with
          | (ST_Arrow ((ST_Var ti),_)), _ -> fresh := true; type_context#set l (sub_tvar ti rt lt)
          | (ST_Arrow (pt,_)), _ -> ()
          | _ -> ());
          (match (lt,tt) with
          | (ST_Arrow (_,bt)), (ST_Var ti) -> fresh := true; type_context#set t bt
          | (ST_Arrow(_,bt)), _ -> ()
          | _ -> ())
      ) arrows done;
      let constraints_satisified = ref true in
      let break_constraint s = print_endline s; constraints_satisified := false in
      let ppt = this#pp_type in
      List.iter( fun (l,r,t) ->
          let lt = type_lookup l in
          let rt = type_lookup r in
          let tt = type_lookup t in
          (match (lt,rt) with
          | (ST_Arrow (pt,_)), _ -> if pt!=rt then (break_constraint ("Invalid argument to function: "^(ppt pt)^" "^(ppt rt)))
          | _ -> break_constraint ("Must be function to apply: "^(ppt lt)) );
          (match (lt,tt) with
          | (ST_Arrow (_,bt)), _ -> if bt!=tt then (break_constraint ("Function signature disagrees with returned value: "^(ppt bt)^" "^(ppt tt)))
          | _ -> ())(* already caught by previous match pattern *)
      ) arrows;
      if not (!constraints_satisified) then exit 1;
      List.map (fun (i,tt) -> (i, this#pp_type tt)) (type_context#items())
   )
end
