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


type lt_type = LT_Ground of string * (lt_type list)
             | LT_Sigil of string
             | LT_Arrow of lt_type * lt_type
             | LT_Var of int
             | LT_Poly of lt_type list
             | LT_Tuple of lt_type list
             | LT_Forall of int * lt_type
             | LT_Recursive of int * lt_type
             (* Subtypes can be generalized to union types *)
class checker: type_system = object (this)
   method parse (st: unit CharParse.CharPrim.state) : (unit, typ) CharParse.CharPrim.rcon =
      ( this#parse_internal_type >>= fun tt -> (return (this#pp_type tt)) ) st
   val var_count = ref 0
   val var_cache : (string,int) hash_table = new hashtable
   method private new_st_tvar () = let tvar = !var_count in incr var_count; tvar
   method private new_lt_tvar () = LT_Var (this#new_st_tvar())
   method new_tvar () = this#pp_type (this#new_lt_tvar())
   method private get_tvar (s: string) = if not (var_cache#has s) then var_cache#set s !var_count; incr var_count; (var_cache#get s)
   method private parse_internal_atom (st: unit CharParse.CharPrim.state) : (unit, lt_type) CharParse.CharPrim.rcon = (
      ( symbolChar '\'' >> (
         (identifier >>= fun v -> return (LT_Var (this#get_tvar v))) <|>
         (integer >>= fun n -> return (LT_Var n))
      )) <|>
      ( identifier >>= fun v -> return (LT_Ground (v,[])) ) <|>
      (parens this#parse_internal_type)
   ) st
   method private parse_internal_tuple (st: unit CharParse.CharPrim.state) : (unit, lt_type) CharParse.CharPrim.rcon = (
     sepBy1 this#parse_internal_atom (reservedOp ",") >>= fun ts -> return (if (List.length ts)=1 then (List.nth ts 0) else LT_Tuple ts)
   ) st
   method private parse_internal_type (st: unit CharParse.CharPrim.state) : (unit, lt_type) CharParse.CharPrim.rcon = 
   let table = [
      [Infix (AssocRight, reservedOp "->" >> return (fun t1 t2 -> LT_Arrow(t1,t2) ))];
      [Infix (AssocRight, reservedOp "|" >> return (fun t1 t2 -> match (t1,t2) with 
         | (LT_Poly ts1),(LT_Poly ts2) -> LT_Poly (ts1 @ ts2)
         | (LT_Poly ts1),t2 -> LT_Poly (ts1 @ [t2])
         | t1,(LT_Poly ts2) -> LT_Poly ([t1] @ ts2)
         | t1,t2 -> LT_Poly [t1;t2]
      ))];
      [Prefix (reserved "forall" >> identifier >>= fun p -> reservedOp "." 
               >> return (fun t -> LT_Forall ((this#get_tvar p),t)) )];
      [Prefix (reserved "recursive" >> identifier >>= fun p -> reservedOp "." 
               >> return (fun t -> LT_Recursive ((this#get_tvar p),t)) )];
   ] in
    ( (((buildExpressionParser table this#parse_internal_tuple) <?> "type") st ) : ('a, lt_type) CharParse.CharPrim.rcon)

   method private parse_internal (i: int) (tt: string): lt_type = (
      var_cache#clear ();
      match parse "type" (LazyList.M.ofString tt)
        (whiteSpace >> this#parse_internal_type >>= fun r -> eof >> return r) with
        Success x -> x
      | Failure err -> raise (TypeError (i, ("In <string> "^(Error.M.errorToString err))))
   )
   method private pp_type (tt: lt_type): string = (
      match tt with
      | LT_Var v -> "'"^(string_of_int v)
      | LT_Ground (g,ps) -> g^(if List.length ps=0 then "" else ("["^(string_join "," (List.map this#pp_type ps))^"]"))
      | LT_Arrow (p,b) -> "("^(this#pp_type p)^" -> "^(this#pp_type b)^")"
      | LT_Poly ts -> "("^(string_join " | " (List.map this#pp_type ts))^")"
      | LT_Tuple ts -> "("^(string_join "," (List.map this#pp_type ts))^")"
      | LT_Forall(n,lt) -> "(forall "^(string_of_int n)^". "^(this#pp_type lt)^")"
      | LT_Recursive(n,lt) -> "(recursive "^(string_of_int n)^". "^(this#pp_type lt)^")"
   )
   method new_tarr : (typ option * typ option * typ option) -> (typ*typ*typ) = fun (mpt,mbt,mtt) -> (
      let pt = this#parse_internal 0 (match mpt with Some tt -> tt | None -> this#new_tvar()) in
      let bt = this#parse_internal 0 (match mbt with Some tt -> tt | None -> this#new_tvar()) in
      let tt = match mtt with Some tt -> (this#parse_internal 0 tt) | None -> LT_Arrow(pt,bt) in
      match tt with
      | LT_Arrow(pt,bt) as tt -> ((this#pp_type pt),(this#pp_type bt),(this#pp_type tt))
      | _ -> assert false
   )
   method private type_lookup (type_context: (int,lt_type)hash_table) (i: int) = (
         if not (type_context#has i) then LT_Var i
         else if (type_context#get i)=(LT_Var i) then LT_Var i
         else this#type_realize type_context (type_context#get i)
   )
   method private type_realize (type_context: (int,lt_type)hash_table) (t: lt_type) = (
      match t with
      | LT_Ground(s,ts) -> LT_Ground(s,(List.map (this#type_realize type_context) ts))
      | LT_Sigil(s) -> LT_Sigil(s)
      | LT_Arrow(lt,rt) -> LT_Arrow((this#type_realize type_context) lt,(this#type_realize type_context) rt)
      | LT_Var(vi) -> this#type_lookup type_context vi
      | LT_Poly(ts) -> LT_Poly(List.map (this#type_realize type_context) ts)
      | LT_Tuple(ts) -> LT_Tuple(List.map (this#type_realize type_context) ts)
      | LT_Forall(ti,ts) -> (
         let type_context = type_context#shadow() in
         type_context#set ti (LT_Var ti);
         LT_Forall(ti,(this#type_realize type_context ts))
      )
      | LT_Recursive(ti,t) -> (
         let type_context = type_context#shadow() in
         type_context#set ti (LT_Var ti);
         LT_Recursive(ti,(this#type_realize type_context t))
      )
   )
   method private unify (type_context: (int,lt_type) hash_table) (l: lt_type) (r: lt_type): unit = (
      (* print_endline ("Unify "^(this#pp_type l)^" with "^(this#pp_type r)); *)
      (match l,r with
         | (LT_Var li),(LT_Var ri) -> ()
         | (LT_Var li),r -> type_context#set li r
         | l,(LT_Var ri) -> type_context#set ri l
         | l,r -> (if (this#type_realize type_context l)<>(this#type_realize type_context r) then raise Not_found)
      )
   )
   method check (objects :(int*(typ list)) list) (arrows :(int*int*int) list): (int*typ) list = (
      let objects : (int*(lt_type list)) list = 
      List.map (fun (i,ts) -> i, List.map (fun tt -> this#parse_internal i tt) ts) objects in
      let type_context : (int,lt_type) hash_table = new hashtable in
      List.iter( fun (i,ts) -> List.iter( fun tt ->
          let tt = if type_context#has i then 
          (match tt, (type_context#get i) with 
             | (LT_Poly ts1),(LT_Poly ts2) -> LT_Poly (ts1 @ ts2)
             | (LT_Poly ts1),t2 -> LT_Poly (ts1 @ [t2])
             | t1,(LT_Poly ts2) -> LT_Poly ([t1] @ ts2)
             | t1,t2 -> LT_Poly [t1; t2]
          ) else tt in type_context#set i tt
      ) ts ) objects;
      let rec sub_tvar (i: int) (rt: lt_type) = function
      | LT_Arrow (pt,bt) -> LT_Arrow (sub_tvar i rt pt, sub_tvar i rt bt)
      | LT_Var v -> if v=i then rt else LT_Var v
      | tt -> tt in
      let previous_state = ref [] in 
      (*List.iter (fun (l,r,t) -> 
         let l,r,t = (this#type_lookup type_context l, this#type_lookup type_context r, this#type_lookup type_context t) in
         print_endline ((this#pp_type l)^" $ "^(this#pp_type r)^" => "^(this#pp_type t))
      ) arrows;*)
      while !previous_state <> (type_context#items())
      do previous_state := (type_context#items()); List.iter( fun (l,r,t) ->
          (* how does information flow through the system? 
             what is the shape of the L<: group?
          *)
          let lt = this#type_lookup type_context l in
          let rt = this#type_lookup type_context r in
          let tt = this#type_lookup type_context t in
          (match (lt,rt) with
          | (LT_Var ti),_ -> let lt = (LT_Arrow (this#new_lt_tvar(),this#new_lt_tvar())) 
            in type_context#set ti lt
          | (LT_Arrow (pt,_)),_  -> (try this#unify type_context pt rt with Not_found -> 
            (print_endline("Could not unify function parameter "^(this#pp_type pt)^" with "^(this#pp_type rt)); assert false))
          | (LT_Poly plt),_ -> 
            let flt = List.filter (function
              | LT_Arrow (pt,_) -> (try (this#unify type_context pt rt; true) with Not_found -> false)
              | _ -> false
            ) plt in if (List.length flt)=1 then type_context#set l (List.nth flt 0)
          | _ -> ());
          (match (lt,tt) with
          | (LT_Arrow(_,bt)),_ -> (try this#unify type_context bt tt with Not_found -> assert false)
          | _ -> ())
      ) arrows done;
      let constraints_satisified = ref true in
      let break_constraint s = print_endline s; constraints_satisified := false in
      let ppt = this#pp_type in
      List.iter( fun (l,r,t) ->
          let lt = this#type_lookup type_context l in
          let rt = this#type_lookup type_context r in
          let tt = this#type_lookup type_context t in
          (match (lt,rt) with
          | (LT_Arrow (pt,_)), _ -> if (ppt pt)<>(ppt rt)
          then (break_constraint ("Invalid argument to function. Expected "^(ppt pt)^" but received "^(ppt rt)))
          | _ -> break_constraint ("Must be function to apply: "^(ppt lt)) );
          (match (lt,tt) with
          | (LT_Arrow (_,bt)), _ -> if (ppt bt)<>(ppt tt)
          then (break_constraint ("Function signature disagrees with returned value: function "^(ppt lt)^" returned "^(ppt tt)))
          | _ -> ())(* already caught by previous match pattern *)
      ) arrows;
      if not (!constraints_satisified) then exit 1;
      List.map (fun (i,tt) -> (i, this#pp_type tt)) (type_context#items())
   )
end
