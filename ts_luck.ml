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

class checker: type_system = object (this)

   val id_count = ref 0
   method private new_id() = let d = !id_count in incr id_count; d
   val var_cache : (string,int) hash_table = new hashtable
   method private new_internal_tvar () = LT_Var (this#new_id())
   method new_tvar () = this#pp_type (this#new_internal_tvar())
   method private get_tvar (s: string) = if not (var_cache#has s) then var_cache#set s !id_count; incr id_count; (var_cache#get s)
   method new_tarr : (typ option * typ option * typ option) -> (typ*typ*typ) = fun (mpt,mbt,mtt) -> (
      let pt = this#parse_internal 0 (match mpt with Some tt -> tt | None -> this#new_tvar()) in
      let bt = this#parse_internal 0 (match mbt with Some tt -> tt | None -> this#new_tvar()) in
      let tt = match mtt with Some tt -> (this#parse_internal 0 tt) | None -> LT_Arrow(this#new_id(),pt,bt) in
      match tt with
      | LT_Arrow(n,pt,bt) as tt -> ((this#pp_type pt),(this#pp_type bt),(this#pp_type tt))
      | _ -> assert false
   )

   method parse (st: unit CharParse.CharPrim.state) : (unit, typ) CharParse.CharPrim.rcon =
      ( this#parse_internal_type >>= fun tt -> (return (this#pp_type tt)) ) st
   method private parse_internal_atom (st: unit CharParse.CharPrim.state) : (unit, indexed_type) CharParse.CharPrim.rcon = (
      ( symbolChar '\'' >> (
         (identifier >>= fun v -> return (LT_Var (this#get_tvar v))) <|>
         (integer >>= fun n -> return (LT_Var n))
      )) <|>
      ( identifier >>= fun v -> 
                  (optionRet (brackets (sepBy1 this#parse_internal_atom (reservedOp ",")) ))
                   >>= fun vs -> return (let ts = (match vs with None -> [] | (Some ss) -> ss) in LT_Ground (this#new_id(),v,ts)) 
      ) <|>
      (parens this#parse_internal_type)
   ) st
   method private parse_internal_tuple (st: unit CharParse.CharPrim.state) : (unit, indexed_type) CharParse.CharPrim.rcon = (
     sepBy1 this#parse_internal_atom (reservedOp ",") >>= fun ts -> return (if (List.length ts)=1 then (List.nth ts 0) else LT_Tuple(this#new_id(),ts))
   ) st
   method private parse_internal_type (st: unit CharParse.CharPrim.state) : (unit, indexed_type) CharParse.CharPrim.rcon = 
   let table = [
      [Infix (AssocRight, reservedOp "->" >> return (fun t1 t2 -> LT_Arrow(this#new_id(),t1,t2) ))];
      [Infix (AssocRight, reservedOp "|" >> return (fun t1 t2 -> match (t1,t2) with 
         | (LT_Poly(_,ts1)),(LT_Poly(_,ts2)) -> LT_Poly(this#new_id(), (ts1 @ ts2))
         | (LT_Poly(_,ts1)),t2 -> LT_Poly(this#new_id(), (ts1 @ [t2]))
         | t1,(LT_Poly(_,ts2)) -> LT_Poly(this#new_id(), ([t1] @ ts2))
         | t1,t2 -> LT_Poly(this#new_id(), [t1;t2])
      ))];
      [Prefix (reserved "forall" >> identifier >>= fun p -> reservedOp "." 
               >> return (fun t -> LT_Forall(this#new_id(),(this#get_tvar p),t)) )];
      [Prefix (reserved "recursive" >> identifier >>= fun p -> reservedOp "." 
               >> return (fun t -> LT_Recursive(this#new_id(),(this#get_tvar p),t)) )];
   ] in
    ( (((buildExpressionParser table this#parse_internal_tuple) <?> "type") st ) : ('a, indexed_type) CharParse.CharPrim.rcon)
   method private parse_internal (i: int) (tt: string): indexed_type = (
      var_cache#clear ();
      match parse "type" (LazyList.M.ofString tt)
        (whiteSpace >> this#parse_internal_type >>= fun r -> eof >> return r) with
        Success x -> x
      | Failure err -> raise (TypeError (i, ("In <string> "^(Error.M.errorToString err))))
   )
   method private pp_type (tt: indexed_type): string = (
      match tt with
      | LT_Var v -> "'"^(string_of_int v)
      | LT_Ground(_,g,ps) -> g^(if List.length ps=0 then "" else ("["^(string_join "," (List.map this#pp_type ps))^"]"))
      | LT_Arrow(_,p,b) -> "("^(this#pp_type p)^" -> "^(this#pp_type b)^")"
      | LT_Poly(_,ts) -> "("^(string_join " | " (List.map this#pp_type ts))^")"
      | LT_Tuple(_,ts) -> "("^(string_join "," (List.map this#pp_type ts))^")"
      | LT_Forall(_,n,lt) -> "(forall "^(string_of_int n)^". "^(this#pp_type lt)^")"
      | LT_Recursive(_,n,lt) -> "(recursive "^(string_of_int n)^". "^(this#pp_type lt)^")"
   )

   method private type_lookup (type_context: (int,indexed_type)hash_table) (i: int) = (
      if not (type_context#has i) then LT_Var i
      else if (type_context#get i)=(LT_Var i) then LT_Var i
      else this#type_realize type_context (type_context#get i)
   )
   method private type_realize (type_context: (int,indexed_type)hash_table) (t: indexed_type) = (
      (*
      List.iter (fun (k,v) ->
         print_endline (""^(string_of_int k)^" -> "^(this#pp_type v))
      ) (type_context#items());
      print_endline ("type_realize "^(this#pp_type t));
      *)
      if (type_context#has (type_n t)) && (type_context#get(type_n t) <> t)
      then this#type_lookup type_context (type_n t)
      else match t with
      | LT_Ground(n,s,ts) -> LT_Ground(n,s,(List.map (this#type_realize type_context) ts))
      | LT_Sigil(n,s) -> LT_Sigil(n,s)
      | LT_Arrow(n,lt,rt) -> LT_Arrow(n,(this#type_realize type_context) lt,(this#type_realize type_context) rt)
      | LT_Var(n) -> (
        let type_context = type_context#shadow() in
        type_context#set n (LT_Var n); (* to prevent infinite recursion in recursive types *)
        this#type_lookup type_context n
      )
      | LT_Poly(n,ts) -> LT_Poly(n,List.map (this#type_realize type_context) ts)
      | LT_Tuple(n,ts) -> LT_Tuple(n,List.map (this#type_realize type_context) ts)
      | LT_Forall(n,ti,ts) -> (
         let type_context = type_context#shadow() in
         type_context#set ti (this#new_internal_tvar());
         LT_Forall(n,ti,(this#type_realize type_context ts))
      )
      | LT_Recursive(n,ti,t) -> (
         let type_context = type_context#shadow() in
         type_context#set ti t;
         LT_Recursive(n,ti,(this#type_realize type_context t))
      )
   )
   method private arrow_head (type_context: (int,indexed_type)hash_table) (t: indexed_type) = (
      let t = this#type_realize type_context t in
      match t with
      | LT_Forall(n,ti,tt) -> (
        let type_context = type_context#shadow() in
        type_context#set ti (this#new_internal_tvar());
        this#arrow_head type_context tt
      )
      | LT_Recursive(n,ti,tt) -> (
        let type_context = type_context#shadow() in
        type_context#set ti tt;
        this#arrow_head type_context tt
      )
      | LT_Arrow(n,pt,bt) -> pt
      | _ -> (print_endline ("Cannot find head of arrow: "^(this#pp_type t)); assert false)
   )
   method private arrow_tail (type_context: (int,indexed_type)hash_table) (t: indexed_type) = (
      let t = this#type_realize type_context t in
      match t with
      | LT_Forall(n,ti,tt) -> (
        let type_context = type_context#shadow() in
        type_context#set ti (this#new_internal_tvar());
        this#arrow_head type_context tt
      )
      | LT_Recursive(n,ti,tt) -> (
        let type_context = type_context#shadow() in
        type_context#set ti tt;
        this#arrow_head type_context tt
      )
      | LT_Arrow(n,pt,bt) -> bt
      | _ -> (print_endline ("Cannot find tail of arrow: "^(this#pp_type t)); assert false)
   )
   method private unify (type_context: (int,indexed_type)hash_table) (l: int) (r: int): unit = (
      (* information flows, left to right -> 
         type variables can be overriden, real types cannot *)
      let lt = this#type_lookup type_context l in
      let rt = this#type_lookup type_context r in
      (match lt,rt with
         | (LT_Var li),(LT_Var ri) -> ()
         | l,(LT_Var ri) -> type_context#set ri l
         | (LT_Poly _),(LT_Poly _) -> ()
         | (LT_Poly _),r -> raise Not_found
         | l,(LT_Poly _) -> ()
         | (LT_Forall(_,ti,ts)),r -> (
            let type_context = type_context#shadow() in
            type_context#set ti (this#new_internal_tvar());
            this#unify type_context (type_n ts) (type_n r)
         )
         | (LT_Ground(_,lg,ls)),(LT_Ground(_,rg,rs)) -> if lg=rg && (List.length ls)=(List.length rs)
           then List.iter2 (fun ll rr -> this#unify type_context (type_n ll) (type_n rr)) ls rs
           else raise Not_found
         | (LT_Tuple(_,ls)),(LT_Tuple(_,rs)) -> if (List.length ls)=(List.length rs)
           then List.iter2 (fun ll rr -> this#unify type_context (type_n ll) (type_n rr)) ls rs
           else raise Not_found
         | l,r -> (if (this#type_realize type_context l)<>(this#type_realize type_context r) then raise Not_found)
      )
   )
   method check (objects :(int*(typ list)) list) (arrows :(int*int*int) list): (int*typ) list = (
      let objects : (int*(indexed_type list)) list = 
      List.map (fun (i,ts) -> i, List.map (fun tt -> this#parse_internal i tt) ts) objects in
      let type_context : (int,indexed_type) hash_table = new hashtable in
      List.iter( fun (i,ts) -> List.iter( fun tt ->
          let tt = if type_context#has i then 
          (match tt, (type_context#get i) with 
             | (LT_Poly(_,ts1)),(LT_Poly(_,ts2)) -> LT_Poly(this#new_id(),(ts1 @ ts2))
             | (LT_Poly(_,ts1)),t2 -> LT_Poly(this#new_id(),ts1 @ [t2])
             | t1,(LT_Poly(_,ts2)) -> LT_Poly(this#new_id(), ([t1] @ ts2))
             | t1,t2 -> LT_Poly(this#new_id(), [t1; t2])
          ) else tt in type_context#set i tt
      ) ts ) objects;
      let rec sub_tvar (i: int) (rt: indexed_type) = function
      | LT_Arrow(n,pt,bt) -> LT_Arrow(n, sub_tvar i rt pt, sub_tvar i rt bt)
      | LT_Var v -> if v=i then rt else LT_Var v
      | tt -> tt in
      let previous_state = ref [] in 
      (*List.iter (fun (l,r,t) -> 
         let l,r,t = (this#type_lookup type_context l, this#type_lookup type_context r, this#type_lookup type_context t) in
         print_endline ((this#pp_type l)^" $ "^(this#pp_type r)^" => "^(this#pp_type t))
      ) arrows;*)
      while !previous_state <> (type_context#items())
      do previous_state := (type_context#items()); List.iter( fun (l,r,t) ->
          let lt = this#type_lookup type_context l in
          let rt = this#type_lookup type_context r in
          let tt = this#type_lookup type_context t in
          (match (lt,rt) with
          | (LT_Var n),_ -> let lt = (LT_Arrow (n,this#new_internal_tvar(),this#new_internal_tvar()))
            in type_context#set n lt
          | (LT_Arrow (n,pt,_)),_  -> (try this#unify type_context (type_n rt) (type_n pt) with Not_found -> 
            (print_endline("Could not unify function parameter "^(this#pp_type pt)^" with "^(this#pp_type rt)); exit 1))
          | (LT_Poly (n,plt)),_ -> 
            let flt = List.filter (function
              | LT_Arrow (n,pt,_) -> (try (this#unify type_context (type_n rt) (type_n pt); true) with Not_found -> false)
              | _ -> false
            ) plt in if (List.length flt)=1 then type_context#set l (List.nth flt 0)
          | _ -> ());
          (match (lt,tt) with
          | (LT_Arrow(n,_,bt)),_ -> (try (this#unify type_context (type_n bt) (type_n tt); this#unify type_context (type_n tt) (type_n bt)) with Not_found ->
          (print_endline("Could not unify function body "^(this#pp_type bt)^" with return type "^(this#pp_type tt))); exit 1 )
          | _ -> ())
      ) arrows done;
      let constraints_satisified = ref true in
      let break_constraint s = print_endline s; constraints_satisified := false in
      let ppt = this#pp_type in
      List.iter( fun (l,r,t) ->
          let lt = this#type_lookup type_context l in
          let rt = this#type_lookup type_context r in
          let tt = this#type_lookup type_context t in
          (try this#unify type_context (type_n rt) (type_n (this#arrow_head type_context lt))
          with Not_found -> (break_constraint ("Invalid argument to function. Expected "^(ppt (this#arrow_head type_context lt))^" but received "^(ppt rt))));
          (try (this#unify type_context (type_n (this#arrow_tail type_context lt)) (type_n tt); 
                this#unify type_context (type_n tt) (type_n (this#arrow_tail type_context lt)))
          with Not_found -> (break_constraint ("Function signature disagrees with returned value: function "^(ppt lt)^" returned "^(ppt tt))))
      ) arrows;
      if not (!constraints_satisified) then exit 1;
      List.map (fun (i,tt) -> (i, this#pp_type tt)) (type_context#items())
   )
end
