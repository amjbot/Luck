(* Subtle change is real change. *)
open Misc
open Str

type file_bundle               = filename list
and  resource_bundle           = resource list
and  annotated_namespace       = namespace * ((int * typ) list) 
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
   | Con of int * string * typ                (* constant *)
   | Var of int * string                      (* variable reference *)
   | Abs of int * string * term               (* lambda abstraction *)
   | App of int * term * term                 (* function application *)
(* Types are all the properties that are provable at compile time *)
and typ = 
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
let con s t = Con (unique_int(), s, t)
let var s = Var(unique_int(), s)
let app l r = App (unique_int(), l, r)
let abs p b = Abs (unique_int(), p, b)


let tvar() = TVar ("_"^(unique_string()))
let tarr p b tt = 
    let a = match p with Some t -> t | None -> tvar() 
    and b = match b with Some t -> t | None -> tvar()
    in match tt with
    | Some(TArrow(a,b) as c) -> a,b,c
    | _ -> a,b,TArrow(a,b)


let rec pp_type: typ -> string = function
   | TProp(p,ps) -> p^"("^(string_join "," (List.map pp_type ps))^")"
   | TVar(v) -> v
   | TForall(x,t) -> "forall "^x^(pp_type t)
   | TExists(x,t) -> "exists "^x^(pp_type t)
   | TArrow(a,b) -> "("^(pp_type a)^" -> "^(pp_type b)^")"
   | TAll(ts) -> "("^(string_join " & " (List.map pp_type ts))^")"
   | TAny(ts) -> "("^(string_join " | " (List.map pp_type ts))^")"
   | TNot t -> "~"^(pp_type t)
let rec pp_term: term -> string = function
   | Con (_,s,tt) -> "(\""^ s ^"\": "^ (pp_type tt) ^"\")"
   | Var (_,s) -> s
   | Abs (_,p,t) -> "\\" ^ p ^ ". " ^ (pp_term t)
   | App (_,t1,t2) -> "(" ^ (pp_term t1) ^ " " ^ (pp_term t2) ^ ")" 


let term_n = function
   | Con (n,_,_) -> n
   | Var (n,_) -> n
   | Abs (n,_,_) -> n
   | App (n,_,_) -> n


let t_typ : (int,typ) hash_table = new hashtable
let ascript t tt = t_typ#set (term_n t) tt
let descript t = let tn = term_n t in if not(t_typ#has tn) then t_typ#set tn (tvar()); t_typ#get tn

let rec substitute_in_term (k: string) (v: term) = function
   | Con(n,c,tt) -> Con(n,c,tt)
   | Var(n,m) -> if m=k then v else Var(n,m)
   | Abs(n,p,b) -> if p=k then Abs(n,p,b) else Abs(n,p,(substitute_in_term k v b))
   | App(n,l,r) -> App(n,(substitute_in_term k v l),(substitute_in_term k v r))

let is_macro_body = function
   | App(_,(Var(_,"@")),_) -> true
   | _ -> false

let pp_namespace_item: namespace_item -> string = function
   | NS_import link -> ""
   | NS_type tt -> pp_type tt
   | NS_bind (bind,t) -> bind^" = "^(pp_term t)
   | NS_expr t -> pp_term t
let pp_namespace: namespace -> string = function 
   | ns -> (string_join "\n" (List.map pp_namespace_item ns))

let uniop op a = app (var op) a
let binop op a b = app (app (var op) a) b
let triop op a b c = app (app (app (var op) a) b ) c

let pattern pbs = (var "#TODO pattern")
