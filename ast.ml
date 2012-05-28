(* Subtle change is real change. *)
open Misc
open Str

type file_bundle               = filename list
and  resource_bundle           = resource list
and  annotated_namespace       = namespace * ((term * typ) list) 
and  target_executable         = filename list

(* Namespaces are one honking great idea -- let's do more of those! *)
and  symbolic_link             = string * string * (string list) (* uri, prefix, symbols *)
and  hard_link                 = string * namespace * string * (string list) (* uri, namespace, prefix, symbols *)
and  filename                  = string
and  resource                  = string(* URI *) * namespace * (hard_link list)(* dependencies *)
and  namespace                 = namespace_item list
and  namespace_item            = 
   | NS_import of symbolic_link
   | NS_type of typ
   | NS_bind of (string * term)
   | NS_expr of term

(* All total functions are recursively enumerable *)
and term = 
   (* ascription term is not necessary thanks to int identifier on terms
      hack: types can be encoded into expression language as (con "" tt)
      hack: patterns can be encoded with a special pattern creation function
        pi: (a -> c) -> (b -> d) -> (a|b -> c|d)
      hack: use Haskell forced currying of tuples in expression language
   *)
   | Con of string * typ          (* constant *)
   | Var of string                (* variable reference *)
   | Abs of string * term         (* lambda abstraction *)
   | App of term * term           (* function application *)
(* Types are properties that are provable at compile time *)
and typ = 
   | TType of string * (typ list) (* T, T<x>, P<x,y>, ... *)
   | TProp of string * (typ list) (* P, P(x), P(x,y), ... *)
   | TVar of string               (* 'a *)
   | TForall of string * typ      (* forall 'a. 'a *)
   | TExists of string * typ      (* exists 'a. 'a *)
   | TArrow of typ * typ          (* A => B *)
   | TAll of typ list             (* A & B & C *)
   | TAny of typ list             (* A | B | C *)
   | TNot of typ                  (* ~A *)


(* Compiler Options *)
let option_target = ref "sml"
let option_out = ref "a.out"

(* For the convenience *)

let con c t = Con(c,t)
let var v = Var(v)
let abs p b = Abs(p,b)
let app l r = App(l,r)

let tvar() = TVar ("_"^(unique_string()))
let tarr p b tt = 
    let a = match p with Some t -> t | None -> tvar() 
    and b = match b with Some t -> t | None -> tvar()
    in match tt with
    | Some(TArrow(a,b) as c) -> a,b,c
    | _ -> a,b,TArrow(a,b)

let term_count : (term,int) hash_table = new hashtable
let term_n t = if not(term_count#has t)
   then term_count#set t (List.length(term_count#items())); 
   term_count#get t

let rec quantify_type (t: typ): typ = (
   let open_terms = new hashtable in
   let rec search_open_terms closed t = match t with
   | TType(_,_) -> ()
   | TProp(_,_) -> ()
   | TVar(v) -> if not(List.mem v closed) then open_terms#set v v
   | TForall(p,t) -> search_open_terms (p :: closed) t
   | TExists(p,t) -> search_open_terms (p :: closed) t
   | TArrow(l,r) -> List.iter (search_open_terms closed) [l;r]
   | TAll(ts) -> List.iter (search_open_terms closed) ts
   | TAny(ts) -> List.iter (search_open_terms closed) ts
   | TNot(t) -> search_open_terms closed t
   in search_open_terms [] t; let t = ref t in
   List.iter (fun v -> t := TForall(v,!t)) (open_terms#values()); 
   !t
)

let rec normalize_type (t: typ): typ = match t with
   | TType(_,_) as t -> t
   | TProp(_,_) as t -> t
   | TVar(_) as t -> t
   | TForall(p,t) -> TForall(p,normalize_type t)
   | TExists(p,t) -> TExists(p,normalize_type t)
   | TArrow(l,r) -> TArrow(normalize_type l,normalize_type r)
   | TAll(ts) -> if List.length ts=1 then List.nth ts 0 else TAll(List.map normalize_type ts)
   | TAny(ts) -> if List.length ts=1 then List.nth ts 0 else TAny(List.map normalize_type ts)
   | TNot(t) -> TNot(normalize_type t)

let rec pp_type (t: typ): string = match normalize_type t with
   | TType(p,ps) -> p^(if List.length ps=0 then "" else "<"^(string_join "," (List.map pp_type ps))^">")
   | TProp(p,ps) -> "+"^p^(if List.length ps=0 then "" else "("^(string_join "," (List.map pp_type ps))^")")
   | TVar(v) -> "'"^v
   | TForall(x,t) -> "forall "^x^". "^(pp_type t)
   | TExists(x,t) -> "exists "^x^". "^(pp_type t)
   | TArrow(a,b) -> "("^(pp_type a)^" -> "^(pp_type b)^")"
   | TAll(ts) -> "("^(string_join " & " (List.map pp_type ts))^")"
   | TAny(ts) -> "("^(string_join " | " (List.map pp_type ts))^")"
   | TNot t -> "~"^(pp_type t)
let rec pp_term (t: term): string = match t with
   | Con (s,tt) -> "(\""^ s ^"\": "^ (pp_type tt) ^"\")"
   | Var (s) -> s
   | Abs (p,t) -> "\\" ^ p ^ ". " ^ (pp_term t)
   | App (t1,t2) -> "(" ^ (pp_term t1) ^ " " ^ (pp_term t2) ^ ")" 
let rec pp_short_term ?lvl:(lvl=2) (t: term): string = 
   if lvl=0 then "..." else match t with
   | Con (s,tt) -> "(\""^ s ^"\": "^ (pp_type tt) ^"\")"
   | Var (s) -> s
   | Abs (p,t) -> "\\" ^ p ^ ". " ^ (pp_short_term ~lvl:(lvl-1) t)
   | App (t1,t2) -> "(" ^ (pp_short_term ~lvl:(lvl-1) t1) ^ " " ^ (pp_short_term ~lvl:(lvl-1) t2) ^ ")" 


let (<:) a b = (a=b)
let rec unify_type (lt: typ) (rt: typ): typ = (
   if lt=rt then lt else
   (print_endline("TODO: unify "^(pp_type lt)^" with "^(pp_type rt)); exit 1)
)


let t_typ : (term,typ) hash_table = new hashtable
let ascript t tt = t_typ#set t tt
let descript t = if not(t_typ#has t) then t_typ#set t (tvar()); t_typ#get t

let rec substitute_in_term (k: string) (v: term) = function
   | Con(c,tt) -> Con(c,tt)
   | Var(m) -> if m=k then v else Var(m)
   | Abs(p,b) -> if p=k then Abs(p,b) else Abs(p,(substitute_in_term k v b))
   | App(l,r) -> App((substitute_in_term k v l),(substitute_in_term k v r))

let is_macro_body = function
   | App((Var("@")),_) -> true
   | _ -> false

let pp_namespace_item: namespace_item -> string = function
   | NS_import link -> ""
   | NS_type tt -> pp_type tt
   | NS_bind (bind,t) -> bind^" = "^(pp_term t)
   | NS_expr t -> pp_term t
let pp_namespace: namespace -> string = function 
   | ns -> (string_join "\n" (List.map pp_namespace_item ns))

let uniop op a = App((Var op),a)
let binop op a b = App((App((Var op), a)), b)
let triop op a b c = App(( App(( App((Var op),a) ),b) ),c)

let pattern pbs = (Var "#TODO pattern")
