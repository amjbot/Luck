open Misc
open Ast
open Log

(* TODO:

   1. create test case for simply typed lambda calculus [x]
   2. solve test case for simply typed lambda calculus [x]
   3. connect simply typed lambda calculus with ast/prs frontend [3/19/2012?]
   4. connect simply typed lambda calculus with gen backend [3/19/2012?]

   ditto 1-4, s/simply typed lambda/F<:/g
   ditto 1-4, s/simply typed lambda/hard luck/g
   ditto 1-4, s/simply typed lambda/soft luck/g

   Simply Typed Lambda Calculus (DUE: 2012/03) [x]
   F<:                          (DUE: 2012/04)
   L<: and/or L<:?              (DUE: 2012/05)
   ...
   v1.0                         (DUE: 2012/12)
*)

let extract_globals : hard_link list -> (string,string) hash_table = fun nss -> (
   let globals = new hashtable in
   globals#set "@" "@";
   List.iter (fun (uri,ns,prefix,symbols) -> List.iter (function
      | NS_bind (k,t) -> 
        let local_name = if prefix="" then k else (prefix^k) in
        let global_name = uri^"$"^k in
        (* ambiguous strings stay ambigous here *)
        globals#set local_name (if globals#has local_name then (globals#get local_name)^" "^global_name else global_name)
      | _ -> ()
   ) ns) nss; globals
)

let flatten_namespace (nss: resource_bundle): namespace = (
   let rec normalize_term_names : string -> (string,string) hash_table -> term -> term = fun uri ns t -> (
      match t with
      | Con(_,_,_) -> t
      | Var(n,s) -> if ns#has s then Var(n,ns#get s) else Var(n,(uri^"$"^s))
      | Abs(n,p,b) -> 
        let pn = uri^"$"^p and ns = ns#shadow() in ns#set p pn;
        Abs(n,pn,normalize_term_names uri ns b)
      | App(n,f,x) -> App(n,normalize_term_names uri ns f,normalize_term_names uri ns x)
   ) in
   let flat_ns : namespace ref = ref [] in
   List.iter (fun (uri,ns,deps) ->
      let globals = extract_globals ((uri,ns,"",["*"]) :: deps) in
      flat_ns := List.map (function
         | NS_type tt -> assert false (* are type names relative to current namespace *)
         | NS_bind (k,t) -> let k = (uri^"$"^k)
           in NS_bind (k,(normalize_term_names uri globals t))
         | NS_expr t -> NS_expr (normalize_term_names uri globals t)
         | t -> t
      ) ns @ !flat_ns;
   ) nss; !flat_ns
)
let fix_namespace ((ns,a): annotated_namespace): namespace = (
   (* TODO: remove ambiguities in referencing polymorphic global functions *)
   ns
)
let extract_global_types (ns: namespace): (string,(typ list)) hash_table = (
   let globals : (string,(typ list)) hash_table = new hashtable in
   let put_type (name: string) (tt: typ): unit =
      globals#set name (if not (globals#has name) then [tt] else (tt :: (globals#get name)))
   in
   List.iter (function
      | NS_type tt -> assert false (* how to handle type definitions? just add another rule and syntax form? *)
      | NS_bind (k,t) -> put_type k (descript t)
      | _ -> ()
   ) ns; globals
)
let extract_system (globals: (string,(typ list)) hash_table) (ns: namespace): (((int*(typ list)) list) * ((int*int*int) list)) = (
  let a : (int*(typ list)) list ref = ref [] in
  let c : (int*int*int) list ref= ref [] in
  let rec extract_term_system (ns: (string,(typ list)) hash_table) (t: term): unit = (
    print_endline("Extract system from term: "^(pp_term t));
    match t with
    | Con(n,s,tt) -> a := (n,[tt]) :: !a
    | Var(n,s) -> let ts = List.flatten (List.map (fun s ->
           (print_endline ("break up identifier: "^s));
           if ns#has s then ns#get s else
           (print_endline ("Could not find symbol "^s^" in namespace."); exit 1)
    ) (string_split " " s))
    in (a := ((n,ts) :: !a))
    | App(n,l,r) -> c := ((term_n l),(term_n r),n) :: !c
    | Abs(n,p,b) -> let ns = ns#shadow() in ns#del p; (
      (* let pt = List.assoc (term_n p) !a in
      let bt = List.assoc (term_n b) !a in *)
      extract_term_system ns b;
      let pt,bt,tt = (get_option !option_typesystem)#new_tarr(None,None,None) in
      a := (n,[tt]) :: !a
    )
  ) in 
  List.iter (function
   | NS_bind(s,t) -> extract_term_system globals t
   | NS_expr t -> extract_term_system globals t
   | _ -> ()
  ) ns; (!a,!c)
)
let extract_constraints (ns: namespace) = (
  []
)
(* 
  annotate = flatten_namespace -> extract_global_types -> extract_system -> typesystem#check -> fix_namespace
  flatten_namespace : resource_bundle -> namespace
  extract_global_types : namespace -> globals
  extract_system : globals -> namespace -> (annotations,constraints)
  typesystem#check : (annotations,constraints) -> annotations
  fix_namespace : annotated_namespace -> namespace
*)
let annotate (rb: resource_bundle): annotated_namespace = (
   (* 1, extract types of global namespace *)
   let ns = flatten_namespace rb in
   let globals = extract_global_types ns in
      (* 2, extract types of all terms -- ambiguous terms just have more than one type *)
      (* 3, extract constraints on all terms *)
   print_endline "Print global namespace:";
   List.iter (fun (k,vs) -> print_endline(k^" : "^(string_join " | " vs))) (globals#items());
   let (annotations,constraints) = extract_system globals ns in
   print_endline "Print annotations:";
   List.iter (fun (n,ts) -> print_endline ("#"^(string_of_int n)^" : "^(string_join " | " ts))) annotations;
   print_endline "Print constraints:";
   List.iter (fun (p,b,t) -> print_endline ("'"^(string_of_int p)^" '"^(string_of_int b)^" => '"^(string_of_int t))) constraints;
   let annotations = (get_option !Ast.option_typesystem)#check annotations constraints in
   let ns = fix_namespace (ns, annotations) in
   (ns,annotations)
)


let test_cases : (type_system * ((int*(typ list)) list) * ((int*int*int) list)) list = [
   (new Ts_simple.checker, [(1,["'a -> 'a"]);(2,["int"])], [(1,2,3)]);
   (new Ts_simple.checker, [(1,["'a -> 'a -> 'a"]);(2,["int"]);(3,["int"])], [(1,2,4);(4,3,5)]);
   (new Ts_poly.checker, [(1,["int -> int"; "unit -> unit"]);(2,["int"])], [(1,2,3)])
]

let test () = (
   List.iter (fun (checker, objects, arrows) ->
      let solution = checker#check objects arrows in
      print_endline "Solution to equation set:";
      List.iter (fun (i,tt) ->
         print_endline ("t#"^(string_of_int i)^" : "^tt)
      ) solution; print_endline ""; ()
   ) test_cases
)
