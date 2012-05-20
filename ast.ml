(* Subtle change is real change. *)
open Misc

type file_bundle               = filename list
and  resource_bundle           = resource list
and  annotated_namespace       = namespace * ((int * typ) list) 
and  target_executable         = filename list

(* "Namespaces are one honking great idea -- let's do more of those!" -- Tim Peters *)
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
and typ = string

class type type_system = object
   method parse : unit CharParse.CharPrim.state -> (unit, typ) CharParse.CharPrim.rcon
   method check : (int*(typ list)) list -> (int*int*int) list -> (int*typ) list
                  (* annotations *) (* applications *) (* solution *)
                  (* NOTE: one term can have more than one type, in the case of ambiguous references to global variables *)
                  (* NOTE: multiple types on the same constraint signifies ambiguity, 
                           multiple constraints on the same term signifies multiple constraints *)
   method new_tarr : (typ option * typ option * typ option) -> (typ*typ*typ) (* type of argument, body, abstraction *)
   method new_tvar : unit -> typ
end
exception TypeError of int * string


(* Compiler Options *)
let option_target = ref "sml"
let option_test = ref false
let option_out = ref "a.out"
let option_typesystem : type_system option ref = ref None

(* For the convenience *)
let con s t = Con (unique_int(), s, t)
let var s = Var(unique_int(), s)
let app l r = App (unique_int(), l, r)
let abs p b = Abs (unique_int(), p, b)
let tarr (os: typ option *  typ option * typ option): (typ*typ*typ) = (get_option (!option_typesystem))#new_tarr os
let quantify (t: typ) = t
let tvar (): typ = (get_option (!option_typesystem))#new_tvar ()

let term_n = function
   | Con (n,_,_) -> n
   | Var (n,_) -> n
   | Abs (n,_,_) -> n
   | App (n,_,_) -> n

let t_typ : (int,typ) hash_table = new hashtable
let ascript t tt = t_typ#set (term_n t) tt
let descript t = let tn = term_n t in if not(t_typ#has tn) then t_typ#set tn ((get_option (!option_typesystem))#new_tvar()); t_typ#get tn

let rec substitute_in_term (k: string) (v: term) = function
   | Con(n,c,tt) -> Con(n,c,tt)
   | Var(n,m) -> if m=k then v else Var(n,m)
   | Abs(n,p,b) -> if p=k then Abs(n,p,b) else Abs(n,p,(substitute_in_term k v b))
   | App(n,l,r) -> App(n,(substitute_in_term k v l),(substitute_in_term k v r))

let is_macro_body = function
   | App(_,(Var(_,"@")),_) -> true
   | _ -> false

let rec pp_term: term -> string = function
   | Con (_,s,tt) -> "(\""^ s ^"\": "^ tt ^"\")"
   | Var (_,s) -> s
   | Abs (_,p,t) -> "\\" ^ p ^ ". " ^ (pp_term t)
   | App (_,t1,t2) -> "(" ^ (pp_term t1) ^ " " ^ (pp_term t2) ^ ")" 
let pp_namespace_item: namespace_item -> string = function
   | NS_import link -> ""
   | NS_type tt -> tt
   | NS_bind (bind,t) -> bind^" = "^(pp_term t)
   | NS_expr t -> pp_term t
let pp_namespace: namespace -> string = function 
   | ns -> (string_join "\n" (List.map pp_namespace_item ns))

let uniop op a = app (var op) a
let binop op a b = app (app (var op) a) b
let triop op a b c = app (app (app (var op) a) b ) c
let pattern pbs = (var "#TODO pattern")
