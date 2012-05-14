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


type indexed_type = LT_Ground of int * string * (indexed_type list)
   | LT_Sigil of int * string
   | LT_Arrow of int * indexed_type * indexed_type
   | LT_Var of int
   | LT_Poly of int * indexed_type list
   | LT_Tuple of int * indexed_type list
   | LT_Forall of int * int * indexed_type
   | LT_Recursive of int * int * indexed_type
   (* Subtypes can be generalized to union types *)
let type_n = function
   | LT_Ground(n,_,_) -> n
   | LT_Sigil(n,_) -> n
   | LT_Arrow(n,_,_) -> n
   | LT_Var(n) -> n
   | LT_Poly(n,_) -> n
   | LT_Tuple(n,_) -> n
   | LT_Forall(n,_,_) -> n
   | LT_Recursive(n,_,_) -> n
let global_context: (int,indexed_type)hash_table = new hashtable
let register_type (t: indexed_type): indexed_type = global_context#set (type_n t) t; t
let lt_ground (g: string) (gs: indexed_type list) = register_type (LT_Ground (unique_int(),g,gs))
let lt_sigil (g: string) = register_type (LT_Sigil (unique_int(),g))
let lt_arrow (p: indexed_type) (b: indexed_type) = register_type (LT_Arrow (unique_int(),p,b))
let lt_var () = register_type (LT_Var (unique_int()))
let lt_poly (ts: indexed_type list) = register_type (LT_Poly (unique_int(),ts))
let lt_tuple (ts: indexed_type list) = register_type (LT_Tuple (unique_int(),ts))
let lt_forall (t: int) (tt: indexed_type) = register_type (LT_Forall (unique_int(),t,tt))
let lt_recursive (t: int) (tt: indexed_type) = register_type (LT_Recursive (unique_int(),t,tt))
let rec pp_type (tt: indexed_type): string = (
   match tt with
   | LT_Var v -> "'"^(string_of_int v)
   | LT_Ground(_,g,ps) -> g^(if List.length ps=0 then "" else ("["^(string_join "," (List.map pp_type ps))^"]"))
   | LT_Arrow(_,p,b) -> "("^(pp_type p)^" -> "^(pp_type b)^")"
   | LT_Poly(_,ts) -> "("^(string_join " | " (List.map pp_type ts))^")"
   | LT_Tuple(_,ts) -> "("^(string_join "," (List.map pp_type ts))^")"
   | LT_Forall(_,n,lt) -> "(forall "^(string_of_int n)^". "^(pp_type lt)^")"
   | LT_Recursive(_,n,lt) -> "(recursive "^(string_of_int n)^". "^(pp_type lt)^")"
)
let rec (<:) a b = try (match (a,b) with
   | LT_Ground(_,g1,ps1), LT_Ground(_,g2,ps2) -> g1=g2 && (List.for_all2 (<:) ps1 ps2)
   | LT_Arrow(_,p1,b1),LT_Arrow(_,p2,b2) -> p2 <: p1 && b1 <: b2
   | LT_Poly(_,ts1), LT_Poly(_,ts2) -> List.for_all (fun a -> List.exists (fun b -> a <: b) ts2) ts1
   | a, LT_Poly(_,ts2) -> List.exists (fun b -> a <: b) ts2
   | LT_Tuple(_,ts1), LT_Tuple(_,ts2) -> List.for_all2 (<:) ts1 ts2 
   | _ -> print_endline ("<: is undefined on types "^(pp_type a)^" <: "^(pp_type b)); exit 1
   ) with Invalid_argument _ -> false

let rec arrow_head ?c:(type_context=new hashtable) (t: indexed_type) = (
   match t with
   | LT_Forall(n,ti,tt) -> (
      let type_context = type_context#shadow() in
      type_context#set ti (lt_var());
      arrow_head ~c:type_context tt
   )
   | LT_Recursive(n,ti,tt) -> (
      let type_context = type_context#shadow() in
      type_context#set ti tt;
      arrow_head ~c:type_context tt
   )
   | LT_Arrow(n,pt,bt) -> pt
   | _ -> (print_endline ("Cannot find head of arrow: "^(pp_type t)); assert false)
)
let rec arrow_tail ?c:(type_context=new hashtable) (t: indexed_type) = (
   match t with
   | LT_Forall(n,ti,tt) -> (
      let type_context = type_context#shadow() in
      type_context#set ti (lt_var());
      arrow_head ~c:type_context tt
   )
   | LT_Recursive(n,ti,tt) -> (
      let type_context = type_context#shadow() in
      type_context#set ti tt;
      arrow_head ~c:type_context tt
   )
   | LT_Arrow(n,pt,bt) -> bt
   | _ -> (print_endline ("Cannot find tail of arrow: "^(pp_type t)); assert false)
)
let rec type_realize (type_context: (int,indexed_type)hash_table) (t: indexed_type) = (
   (*
   List.iter (fun (k,v) ->
      print_endline (""^(string_of_int k)^" -> "^(pp_type v))
   ) (type_context#items());
   print_endline ("type_realize "^(pp_type t));
   *)
   if (type_context#has (type_n t)) && (type_context#get(type_n t) <> t)
   then type_lookup type_context (type_n t)
   else match t with
   | LT_Ground(n,s,ts) -> LT_Ground(n,s,(List.map (type_realize type_context) ts))
   | LT_Sigil(n,s) -> LT_Sigil(n,s)
   | LT_Arrow(n,lt,rt) -> LT_Arrow(n,(type_realize type_context) lt,(type_realize type_context) rt)
   | LT_Var(n) -> (
     let type_context = type_context#shadow() in
     type_context#set n (LT_Var n); (* to prevent infinite recursion in recursive types *)
     type_lookup type_context n
   )
   | LT_Poly(n,ts) -> LT_Poly(n,List.map (type_realize type_context) ts)
   | LT_Tuple(n,ts) -> LT_Tuple(n,List.map (type_realize type_context) ts)
   | LT_Forall(n,ti,ts) -> (
      let type_context = type_context#shadow() in
      type_context#set ti (lt_var());
      LT_Forall(n,ti,(type_realize type_context ts))
   )
   | LT_Recursive(n,ti,t) -> (
      let type_context = type_context#shadow() in
      type_context#set ti t;
      LT_Recursive(n,ti,(type_realize type_context t))
   )
)
and type_lookup (type_context: (int,indexed_type)hash_table) (i: int) = (
   (*
   List.iter (fun (k,v) ->
      print_endline (""^(string_of_int k)^" -> "^(pp_type v))
   ) (type_context#items());
   print_endline ("type_lookup #"^(string_of_int i));
   *)
   if not (type_context#has i) then LT_Var i
   else if (type_context#get i)=(LT_Var i) then LT_Var i
   else type_realize type_context (type_context#get i)
)
let rec unify (type_context: (int,indexed_type)hash_table) (l: int) (r: int): unit = (
   (* information flows, left to right -> type variables can be overriden, real types cannot *)
   let lt = type_lookup type_context l in
   let rt = type_lookup type_context r in
   (match lt,rt with
      | (LT_Var li),(LT_Var ri) -> ()
      | l,(LT_Var ri) -> type_context#set ri l
      | (LT_Poly _),(LT_Poly _) -> ()
      | (LT_Poly _),r -> raise Not_found
      | l,(LT_Poly _) -> ()
      | (LT_Forall(_,ti,ts)),r -> (
         let type_context = type_context#shadow() in
         type_context#set ti (lt_var());
         unify type_context (type_n ts) (type_n r)
      )
      | (LT_Ground(_,lg,ls)),(LT_Ground(_,rg,rs)) -> if lg=rg && (List.length ls)=(List.length rs)
        then List.iter2 (fun ll rr -> unify type_context (type_n ll) (type_n rr)) ls rs
        else raise Not_found
      | (LT_Tuple(_,ls)),(LT_Tuple(_,rs)) -> if (List.length ls)=(List.length rs)
        then List.iter2 (fun ll rr -> unify type_context (type_n ll) (type_n rr)) ls rs
        else raise Not_found
      | l,r -> (if l<>r then raise Not_found)
   )
)


class checker: type_system = object (this)

   val var_cache : (string,int) hash_table = new hashtable
   method private get_tvar (s: string) = if not (var_cache#has s) then var_cache#set s (unique_int()); (var_cache#get s)
   method new_tvar () = pp_type (lt_var())
   method new_tarr : (typ option * typ option * typ option) -> (typ*typ*typ) = fun (mpt,mbt,mtt) -> (
      let pt = this#parse_internal 0 (match mpt with Some tt -> tt | None -> this#new_tvar()) in
      let bt = this#parse_internal 0 (match mbt with Some tt -> tt | None -> this#new_tvar()) in
      let tt = match mtt with Some tt -> (this#parse_internal 0 tt) | None -> LT_Arrow(unique_int(),pt,bt) in
      match tt with
      | LT_Arrow(n,pt,bt) as tt -> ((pp_type pt),(pp_type bt),(pp_type tt))
      | _ -> assert false
   )

   method parse (st: unit CharParse.CharPrim.state) : (unit, typ) CharParse.CharPrim.rcon =
      ( this#parse_internal_type >>= fun tt -> (return (pp_type tt)) ) st
   method private parse_internal_atom (st: unit CharParse.CharPrim.state) : (unit, indexed_type) CharParse.CharPrim.rcon = (
      ( symbolChar '\'' >> (
         (identifier >>= fun v -> return (LT_Var (this#get_tvar v))) <|>
         (integer >>= fun n -> return (lt_var ()))
      )) <|>
      ( identifier >>= fun v ->
                  (optionRet (brackets (sepBy1 this#parse_internal_atom (reservedOp ",")) ))
                   >>= fun vs -> return (let ts = (match vs with None -> [] | (Some ss) -> ss) in lt_ground v ts)
      ) <|>
      (parens this#parse_internal_type)
   ) st
   method private parse_internal_tuple (st: unit CharParse.CharPrim.state) : (unit, indexed_type) CharParse.CharPrim.rcon = (
     sepBy1 this#parse_internal_atom (reservedOp ",") >>= fun ts -> return (if (List.length ts)=1 then (List.nth ts 0) else lt_tuple ts)
   ) st
   method private parse_internal_type (st: unit CharParse.CharPrim.state) : (unit, indexed_type) CharParse.CharPrim.rcon = 
   let table = [
      [Infix (AssocRight, reservedOp "->" >> return (fun t1 t2 -> lt_arrow t1 t2 ))];
      [Infix (AssocRight, reservedOp "|" >> return (fun t1 t2 -> match (t1,t2) with 
         | (LT_Poly(_,ts1)),(LT_Poly(_,ts2)) -> lt_poly(ts1 @ ts2)
         | (LT_Poly(_,ts1)),t2 -> lt_poly (ts1 @ [t2])
         | t1,(LT_Poly(_,ts2)) -> lt_poly ([t1] @ ts2)
         | t1,t2 -> lt_poly ([t1;t2])
      ))];
      [Prefix (reserved "forall" >> identifier >>= fun p -> reservedOp "." 
               >> return (fun t -> lt_forall (this#get_tvar p) t) )];
      [Prefix (reserved "recursive" >> identifier >>= fun p -> reservedOp "." 
               >> return (fun t -> lt_recursive (this#get_tvar p) t) )];
   ] in
    ( (((buildExpressionParser table this#parse_internal_tuple) <?> "type") st ) : ('a, indexed_type) CharParse.CharPrim.rcon)
   method private parse_internal (i: int) (tt: string): indexed_type = (
      var_cache#clear ();
      match parse "type" (LazyList.M.ofString tt)
        (whiteSpace >> this#parse_internal_type >>= fun r -> eof >> return r) with
        Success x -> x
      | Failure err -> raise (TypeError (i, ("In <string> "^(Error.M.errorToString err))))
   )

   method check (objects :(int*(typ list)) list) (arrows :(int*int*int) list): (int*typ) list = (
      global_context#clear();
      let tarr_map : (int,int)hash_table = new hashtable in
      let tarr_map_get i = (if not(tarr_map#has i) then tarr_map#set i (unique_int()); tarr_map#get i) in
      let objects : (int*(indexed_type list)) list = List.map (fun (i,ts) -> 
         (tarr_map_get i), List.map (fun tt -> this#parse_internal i tt) ts
      ) objects in
      let arrows : (int*int*int) list = List.map (fun (l,r,t) -> (tarr_map_get l,tarr_map_get r,tarr_map_get t)) arrows in
      let type_context : (int,indexed_type) hash_table = global_context in
      List.iter( fun (i,ts) -> List.iter( fun tt ->
          let tt = if type_context#has i then 
          (match tt, (type_context#get i) with 
             | (LT_Poly(_,ts1)),(LT_Poly(_,ts2)) -> LT_Poly(unique_int(),(ts1 @ ts2))
             | (LT_Poly(_,ts1)),t2 -> LT_Poly(unique_int(),ts1 @ [t2])
             | t1,(LT_Poly(_,ts2)) -> LT_Poly(unique_int(), ([t1] @ ts2))
             | t1,t2 -> LT_Poly(unique_int(), [t1; t2])
          ) else tt in type_context#set i tt
      ) ts) objects;
      
      let previous_state = ref [] in 
      while !previous_state <> (type_context#items())
      do previous_state := (type_context#items()); List.iter( fun (l,r,t) ->
          let lt = type_lookup type_context l in
          let rt = type_lookup type_context r in
          let tt = type_lookup type_context t in
          print_endline ((pp_type lt)^" $ "^(pp_type rt)^" => "^(pp_type tt));
          (match (lt,rt) with
          | (LT_Var n),_ -> type_context#set n (LT_Arrow (n,lt_var(),lt_var()))
          | (LT_Arrow (n,pt,_)),_  -> (try unify type_context (type_n rt) (type_n pt) with Not_found -> 
            (print_endline("Could not unify function parameter "^(pp_type pt)^" with "^(pp_type rt)); exit 1))
          | (LT_Poly (n,plt)),_ -> 
            let flt = List.filter (function
              | LT_Arrow (n,pt,_) -> (try (unify type_context (type_n rt) (type_n pt); true) with Not_found -> false)
              | _ -> false
            ) plt in if (List.length flt)=1 then type_context#set l (List.nth flt 0)
          | _ -> ());
          (match (lt,tt) with
          | (LT_Arrow(n,_,bt)),_ -> (try (unify type_context (type_n bt) (type_n tt); unify type_context (type_n tt) (type_n bt)) with Not_found ->
          (print_endline("Could not unify function body "^(pp_type bt)^" with return type "^(pp_type tt))); exit 1 )
          | _ -> ())
      ) arrows done;

      let constraints_satisified = ref true in
      let break_constraint s = print_endline s; constraints_satisified := false in
      List.iter( fun (l,r,t) ->
          let l = type_lookup type_context l in
          let r = type_lookup type_context r in
          let t = type_lookup type_context t in
          (if not (r <: (arrow_head l))
           then break_constraint ("Invalid argument to function. Expected "^(pp_type (arrow_head l))^" but received "^(pp_type r)));
          (if not ((arrow_tail l) <: t && t <: (arrow_tail l))
           then break_constraint ("Function signature disagrees with returned value: function "^(pp_type l)^" returned "^(pp_type t)))
      ) arrows;
      if not (!constraints_satisified) then exit 1;
      List.map (fun (i,tt) -> (i, pp_type tt)) (type_context#items())
   )
end
