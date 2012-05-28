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
let flatten_namespace (nss: resource_bundle): namespace = (
   (* extract mapping from relatively global variable names to absolute global variable names *)
   let to_absolute (uri: string) (var: string) (n: int) = uri^"$"^var^"#"^(string_of_int n) in
   let global_types: (string,typ)hash_table = new hashtable in
   let map_relative_to_absolute_names : hard_link list -> (string,string) hash_table = fun nss -> (
      let table = new hashtable in
      table#set "@" "@";
      List.iter (fun (uri,ns,prefix,symbols) -> List.iter (function
         | NS_bind (k,t) -> (
            let relative_name = if prefix="" then k else (prefix^"."^k) in
            let absolute_name = to_absolute uri k (term_n t) in
            global_types#set absolute_name (descript t);
            if table#has relative_name
            then table#set relative_name ((table#get relative_name)^"\n"^absolute_name)
            else table#set relative_name absolute_name 
         ) | _ -> ()
      ) ns) nss; table
   ) in
   let rec normalize_term_names : string -> (string,string) hash_table -> term -> term = fun uri ns t -> (
      match t with
      | Con(_,_) -> t
      | Var(s) -> if ns#has s then Var(ns#get s) else fatal_error("Undefined variable name: "^s)
      | Abs(p,b) ->
        let pn = to_absolute uri p (unique_int()) and ns = ns#shadow() in ns#set p pn;
        Abs(pn,normalize_term_names uri ns b)
      | App(f,x) -> App(normalize_term_names uri ns f,normalize_term_names uri ns x)
   ) in
   let flat_ns : namespace ref = ref [] in
   List.iter (fun (uri,ns,deps) ->
      let diff = map_relative_to_absolute_names ((uri,ns,"",["*"]) :: deps) in
      flat_ns := List.map (function
         | NS_type tt -> assert false (* are type names relative to current namespace? *)
         | NS_bind (k,t) -> let k = to_absolute uri k (term_n t) in
           let t' = normalize_term_names uri diff t in
           ascript t' (descript t); NS_bind (k,t')
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
      | NS_bind (k,t) -> (assert (not (globals#has k)); globals#set k (descript t))
      | _ -> ()
   ) ns; globals
)


(* STEP 3. extract_system : globals -> namespace -> (annotations,constraints) *)
let extract_system (globals: (string,typ) hash_table) (ns: namespace): ((term*typ) list) = (
  let a : (term*typ) list ref = ref [] in
  let rec extract_term_macro (ns: (string,typ) hash_table) (t: term): unit = (
     match t with
     | App(l,(Con(_,_))) -> extract_term_macro ns l
     | App(l,r) -> extract_term_macro ns l; extract_term_system ns r
     | Abs(_,_) as v -> extract_term_system ns v
     | _ -> ()
  ) 
  and extract_term_system (ns: (string,typ) hash_table) (t: term): unit = (
    (* todo, extract constraints from everything except macros *)
    match t with
    | Con(s,tt) -> a := (t,tt) :: !a
    | Var(s) -> let tt = TAny (List.map 
       (fun s -> if ns#has s then ns#get s else fatal_error ("Undefined variable: "^s)) 
       (string_split "[\n]" s)) in (a := ((t,tt) :: !a))
    | App(l,r) -> (
      match l with
      | Var("@") -> extract_term_macro ns r
      | _ -> (extract_term_system ns l; extract_term_system ns r);
      (a := (t,(tvar())) :: !a)
    )
    | Abs(p,b) -> (
      let ns = ns#shadow() in
      let pt,bt,tt = tarr None None
                     (if List.mem_assoc t !a then Some(List.assoc t !a) else None) in
      ns#set p pt; extract_term_system ns b;
     if not(List.mem_assoc t !a) then a := (t,tt) :: !a
    )
  ) in 
  List.iter (function
   | NS_bind(s,t) -> a := (t,descript t) :: !a; extract_term_system globals t
   | NS_expr t -> extract_term_system globals t
   | _ -> ()
  ) ns; !a
)

(* Inference rules *)
let contradiction (ix,it) (jx,jt) = 
    if ix=jx && (match it,jt with (it,TNot jt) -> it=jt | _ -> false)
    then fatal_error("Contradiction")
    else []

let isolate_part (ix,it) = 
    match it with TAll ts -> List.map(fun t -> (ix,t)) ts | _ -> []

let apply_simple (f,ft) (x,xt) (fx,fxt) =
    match ft,fx with
    | TArrow(pt,bt),(App(_,x')) -> if x=x' && xt <: pt then [(fx,bt)] else []
    | _ -> []

(* STEP 4. typesystem#check : annotations -> annotations *)
let typecheck (a: (term*typ) list): ((term*typ) list) = (
    (* normalize types, infer propositions, check consistency *)
    let facts = new hashtable in
    let add_facts kvs = List.iter (fun (k,v) -> 
        facts#set k (if facts#has k then (unify_type (facts#get k) v) else v)
    ) kvs in
    let stable = ref false in
    List.iter (fun (t,tt) -> let k,v = (t,normalize_type tt) in add_facts [(k,v)]) a;
    while not !stable do 
        let prev_facts = facts#shadow() in
        List.iter (fun i ->
           add_facts (isolate_part i);
           List.iter (fun j -> if i<>j then(
              add_facts (contradiction i j);
              List.iter (fun k -> if i<>j && j<>k then(
                  add_facts (apply_simple i j k)
              )) (prev_facts#items())
           )) (prev_facts#items())
        ) (prev_facts#items());
        if (List.length (facts#items())) = (List.length (prev_facts#items())) then stable := true
        else List.iter (fun (t,tt) ->
            if (not (prev_facts#has t)) || ((prev_facts#get t) <> (facts#get t)) then
            print_endline("Proved new property, #"^(string_of_int(term_n t))^" : "^(pp_type tt))  
        ) (facts#items())
    done;
    facts#items()
)


(* STEP 5. fix_namespace : annotated_namespace -> namespace *)
let fix_namespace ((ns,a): annotated_namespace): namespace = (
   let globals = new hashtable in
   List.iter(function
     | NS_bind(k,t) -> (
       try globals#set k (List.assoc t a)
       with Not_found -> (print_endline ("Could not find annotation for global term: "^k); exit 1)
     )| _ -> ()
   ) ns;
   (* TODO: remove ambiguities in referencing polymorphic global functions *)
   let rec fix_term : term -> term = function
   | Var(s) as v -> 
     let vs = string_split "[\n]" s in
     if List.length vs=1 then Var(s) else (
        let vt = List.assoc v a in
        let vts = List.map (fun v -> 
           try (v, (globals#get v)) with Not_found ->
           (print_endline("Missing variable "^v^" when searching for var:type in context"); exit 1)
        ) vs in
        let vts = List.filter (fun (v,t) -> vt <: t) vts in
        if List.length vts < 1 then fatal_error("Over-constrained variable, "^s^" : "^(pp_type vt))
        else if List.length vts > 1 then fatal_error("Under-constrained variable, "^s^" : "^(pp_type vt))
        else Var(fst(List.nth vts 0))
     )
   | Abs(p,b) -> Abs(p,fix_term b)
   | App(l,r) -> App(fix_term l,fix_term r)
   | Con(v,tt) -> Con(v,tt) in
   List.map (function
   | NS_bind(k,t) -> NS_bind(k,fix_term t)
   | NS_expr(t) -> NS_expr(fix_term t)
   | ns_item -> ns_item
   ) ns
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
   List.iter (fun (k,v) -> print_endline(k^" : "^(pp_type v))) (globals#items());
   let annotations = extract_system globals ns in
   print_endline "Print annotations:";
   List.iter (fun (t,tt) -> print_endline ("#"^(string_of_int (term_n t))^" = "^(pp_short_term t)^" : "^(pp_type tt))) annotations;
   let annotations = typecheck annotations in
   let ns = fix_namespace (ns, annotations) in
   (ns,annotations)
)


