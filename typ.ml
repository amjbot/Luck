open Misc
open Ast
open Log

(* TODO:
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
      | Var(n,s) -> if ns#has s then Var(n,ns#get s) else fatal_error("Undefined variable name: "^s)
      | Abs(n,p,b) ->
        let pn = to_absolute uri p n and ns = ns#shadow() in ns#set p pn;
        Abs(n,pn,normalize_term_names uri ns b)
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
     | Abs(_,_,_) as v -> extract_term_system ns v
     | _ -> ()
  ) 
  and extract_term_system (ns: (string,typ) hash_table) (t: term): unit = (
    (* todo, extract constraints from everything except macros *)
    match t with
    | Con(s,tt) -> a := (t,tt) :: !a
    | Var(n,s) -> (let tt = (List.map 
       (fun s -> if ns#has s then ns#get s else fatal_error ("Undefined variable: "^s)) 
       (string_split "[\n]" s)) in 
        if List.length tt=0
        then (a := ((t,tvar()) :: !a))
        else if List.length tt=1
        then (a := ((t,List.nth tt 0) :: !a))
        else (a := ((t,TAny tt) :: !a))
    )
    | App(l,r) -> (
      match l with
      | Var(n,"@") -> extract_term_macro ns r
      | _ -> (extract_term_system ns l; extract_term_system ns r);
      (a := (t,(tvar())) :: !a)
    )
    | Abs(n,p,b) -> (
      let ns = ns#shadow() in
      let pt,bt,tt = tarr None None
                     (if List.mem_assoc t !a then Some(List.assoc t !a) else None) in
      ns#set p pt; extract_term_system ns b;
      if not(List.mem_assoc t !a) then a := (t,tt) :: !a
    )
  ) in 
  List.iter (function
    | NS_bind(s,t) -> a := (t,globals#get s) :: !a; extract_term_system globals t
    | NS_expr t -> extract_term_system globals t
    | _ -> ()
  ) ns; List.map (fun (t,tt) -> (t,instantiate_type tt)) !a
)

(* Inference rules *)
let inside_abstraction (ix,it) = 
    match ix,it with Abs(n,p,b),TArrow(pt,bt) -> (
       let types = ref [(b,bt)] in
       let add_var t = types := (t,pt) :: !types in
       term_apply p add_var b; 
       types := (b,bt) :: !types; !types
    ) | _ -> []

let apply_simple (f,ft) (x,xt) (fx,fxt) =
    match ft,fx with
    | TArrow(pt,bt),(App(f',x')) -> if f=f' && x=x' && xt <: pt then [(fx,bt)] else []
    | _ -> []
let apply_part (f,ft) (x,xt) (fx,fxt) = (
    let result = ref [] in
    (match ft with | TAny(fts) -> List.iter (fun ft ->
     match ft,fx with | (TArrow(pt,bt) as ft),(App(f',x')) ->
        if f=f' && x=x' && xt <: pt then
        result := (fx,bt) :: (f,ft) :: !result
     | _ -> ()
    ) fts | _ -> ()); !result
)

let backpressure (f,ft) (fx,fxt) = (
    match fx,ft with 
    | App(f',x'),TArrow(p,b) -> if f=f' then [(f,TArrow(p,unify_type b fxt))] else []
    | _ -> []
)


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
           add_facts (inside_abstraction i);
           List.iter (fun j -> if i<>j then(
              add_facts (backpressure i j);
              List.iter (fun k -> if i<>j && j<>k then(
                  add_facts (apply_simple i j k);
                  add_facts (apply_part i j k)
              )) (prev_facts#items())
           )) (prev_facts#items())
        ) (prev_facts#items());
        if List.for_all (fun (k,v) -> (prev_facts#has k) && v=(prev_facts#get k)) (facts#items()) then stable := true
        else List.iter (fun (t,tt) ->
            if (not (prev_facts#has t)) || (not((prev_facts#get t)=tt)) then
            print_endline("Proved new property, #"^(string_of_int(term_n t))^" : "^(pp_type tt))  
        ) (facts#items())
    done;
    facts#items()
)
let check_typecheck input output = (
    List.iter (fun (t,tt) -> 
       try if (List.assoc t output)=tt
       then ()
       else Log.fatal_error( "typecheck failed. Expected "^(pp_type (List.assoc t output))^" but received "^(pp_type tt) )
       with Not_found -> Log.fatal_error ("typecheck lost a type for term: "^(pp_term t))
    ) (typecheck input)
)
let f1 = (var("f1"), TArrow(TType("A",[]),TType("B",[])))
let t1 = (var("t1"), TType("A",[]))
let f1t1 = (app (fst f1) (fst t1), TVar("a"))
let f1t1_answer = (fst f1t1, TType("B",[]))
let f2 = (var("f2"), TAny[ TArrow(TType("A",[]),TType("B",[])); TArrow(TType("C",[]),TType("D",[])) ] )
let f2_answer = (fst f2, TArrow(TType("A",[]),TType("B",[])))
let f2t1 = (app (fst f2) (fst t1), TVar("a"))
let f2t1_answer = (fst f2t1, TType("B",[]))

let _ = check_typecheck [f1;t1;f1t1] [f1;t1;f1t1_answer]
let _ = check_typecheck [f2;t1;f2t1] [f2_answer;t1;f2t1_answer]


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
   | Var(n,s) as v -> 
     let vs = string_split "[\n]" s in
     if List.length vs=1 then Var(n,s) else (
        let vt = List.assoc v a in
        let vts = List.map (fun v -> 
           try (v, (globals#get v)) with Not_found ->
           (print_endline("Missing variable "^v^" when searching for var:type in context"); exit 1)
        ) vs in
        let vts_type = string_join " | " (List.map (fun (v,t) -> pp_type t) vts) in
        let vts = List.filter (fun (v,t) -> vt <: t) vts in
        if List.length vts < 1 then fatal_error("Over-constrained variable, #"^(v $ term_n $ string_of_int)^" "^s^" : "^(pp_type vt)^" not in "^vts_type)
        else if List.length vts > 1 then fatal_error("Under-constrained variable, #"^(v $ term_n $ string_of_int)^" "^s^" : "^(pp_type vt)^" not in "^vts_type)
        else Var(n,fst(List.nth vts 0))
     )
   | Abs(n,p,b) -> Abs(n,p,fix_term b)
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


