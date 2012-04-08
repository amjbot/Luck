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


(* STEP 1. flatten_namespace : resource_bundle -> namespace *)
(* hide extract_globals, it is a helper method and damn ugly at that *)
let flatten_namespace (nss: resource_bundle): namespace = (
   (* extract mapping from relatively global variable names to absolute global variable names *)
   let to_absolute (uri: string) (var: string) (n: int) = uri^"$"^var^"#"^(string_of_int n) in
   let map_relative_to_absolute_names : hard_link list -> (string,string) hash_table = fun nss -> (
      let table = new hashtable in
      table#set "@" "@";
      List.iter (fun (uri,ns,prefix,symbols) -> List.iter (function
         | NS_bind (k,t) ->
         let relative_name = if prefix="" then k else (prefix^"."^k) in
         let absolute_name = to_absolute uri k (term_n t) in
         table#set relative_name (if table#has relative_name then (table#get relative_name)^"\n"^absolute_name else absolute_name)
         | _ -> ()
      ) ns) nss; table
   ) in
   let rec normalize_term_names : string -> (string,string) hash_table -> term -> term = fun uri ns t -> (
      match t with
      | Con(_,_,_) -> t
      | Var(n,s) -> if ns#has s then Var(n,ns#get s) else (print_endline ("Undefined variable name: "^s); assert false)
      | Abs(n,p,b) ->
        let pn = to_absolute uri p n and ns = ns#shadow() in ns#set p pn;
        Abs(n,pn,normalize_term_names uri ns b)
      | App(n,f,x) -> App(n,normalize_term_names uri ns f,normalize_term_names uri ns x)
   ) in
   let flat_ns : namespace ref = ref [] in
   List.iter (fun (uri,ns,deps) ->
      let diff = map_relative_to_absolute_names ((uri,ns,"",["*"]) :: deps) in
      flat_ns := List.map (function
         | NS_type tt -> assert false (* are type names relative to current namespace? *)
         | NS_bind (k,t) -> let k = to_absolute uri k (term_n t)
           in NS_bind (k,(normalize_term_names uri diff t))
         | NS_expr t -> NS_expr (normalize_term_names uri diff t)
         | t -> t
      ) ns @ !flat_ns;
   ) nss; !flat_ns
)


(* STEP 2. extract_global_types : namespace -> globals *)
let extract_global_types (ns: namespace): (string,typ) hash_table = (
   let globals : (string,typ) hash_table = new hashtable in
   List.iter (function
      | NS_type tt -> assert false (* how to handle type definitions? just add another rule and syntax form? *)
      | NS_bind (k,t) -> 
        assert(not(globals#has k));
        globals#set k (descript t)
      | _ -> ()
   ) ns; globals
)


(* STEP 3. extract_system : globals -> namespace -> (annotations,constraints) *)
let extract_system (globals: (string,typ) hash_table) (ns: namespace): (((int*(typ list)) list) * ((int*int*int) list)) = (
  let a : (int*(typ list)) list ref = ref [] in
  let c : (int*int*int) list ref= ref [] in
  let rec extract_term_macro (ns: (string,typ) hash_table) (t: term): unit = (
     match t with
     | App(n,l,(Con(_,_,_))) -> extract_term_macro ns l
     | App(n,l,r) -> extract_term_macro ns l; extract_term_system ns r
     | Abs(_,_,_) as v -> extract_term_system ns v
     | _ -> ()
  ) 
  and extract_term_system (ns: (string,typ) hash_table) (t: term): unit = (
    (* todo, extract constraints from everything except macros *)
    match t with
    | Con(n,s,tt) -> a := (n,[tt]) :: !a
    | Var(n,s) -> let ts = List.map 
       (fun s -> if ns#has s then ns#get s else (print_endline ("Undefined variable: "^s); assert false)) 
       (string_split "[\n]" s) in (a := ((n,ts) :: !a))
    | App(n,l,r) -> (
      match l with
      | Var(_,"@") -> extract_term_macro ns r
      | _ -> (c := ((term_n l),(term_n r),n) :: !c; extract_term_system ns l; extract_term_system ns r)
    )
    | Abs(n,p,b) -> (
      let ns = ns#shadow() in
      let pt,bt,tt = (get_option !option_typesystem)#new_tarr(None,None,None) in
      ns#set p pt;
      extract_term_system ns b;
      a := (n,[tt]) :: !a
    )
  ) in 
  List.iter (function
   | NS_bind(s,t) -> extract_term_system globals t
   | NS_expr t -> extract_term_system globals t
   | _ -> ()
  ) ns; (!a,!c)
)


(* STEP 4. typesystem#check : (annotations,constraints) -> annotations *)
(* external *)


(* STEP 5. fix_namespace : annotated_namespace -> namespace *)
let fix_namespace ((ns,a): annotated_namespace): namespace = (
   (* TODO: remove ambiguities in referencing polymorphic global functions *)
   ns
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
   List.iter (fun (k,v) -> print_endline(k^" : "^v)) (globals#items());
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
