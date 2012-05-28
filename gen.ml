open Misc
open Ast
open Prs
open Log
open Typ

class type target_language = object
   method translate : annotated_namespace -> target_executable
end

let ident_count : int ref = ref 0
let ident_cache : (string,string) hash_table = new hashtable
let hash_ident k = 
   if not (ident_cache#has k)
   then (incr ident_count; ident_cache#set k ("luckid"^(string_of_int !ident_count)));
   ident_cache#get k

class sml_language : target_language = object (this)
   method private translate_ident (ident: string): string = hash_ident ident
   method private translate_simple_macro (m: term) = (
      let rec flatten_macro_atom = function
      | Con(c,tt) as t -> (match tt with
         | TType("string",[]) -> c
         | _ -> this#translate_term t
      )| t -> this#translate_term t in
      let rec flatten_macro_body = function
      | App(l,r) -> (flatten_macro_body l)^(flatten_macro_atom r) 
      | Con(c,tt) as t -> (match tt with
         | TType("string",[]) -> c
         | _ -> assert false
      ) in
      match m with
      | App((Var ("@")),r) -> flatten_macro_body r
      | _ -> assert false
   )
   method private translate_macro (m: term) (xs: term list) = (
      (* Wow, this totally subsumes lisp macros. Hah! *)
      match m with
      | Abs(p,b) -> (match xs with 
         | [] -> assert false 
         | x::xs -> this#translate_macro (substitute_in_term p x b) xs
      ) | App((Var ("@")),r) -> assert ((List.length xs)=0); (this#translate_simple_macro m)
      | App(l,r) -> this#translate_macro l (r::xs)
      | _ -> assert false
   )

   method private translate_term (t: term): string = (
      match t with
      | Con(v,tt) -> (match tt with 
         | TType("int",[]) -> v
         | TType("string",[]) -> 
           let v = Str.global_replace (Str.regexp "\n") "\\n" v in
           "\""^v^"\""
         (*
         ("void", fun s -> s );
         ("bool", fun s -> s );
         ("float", fun s -> s );
         ("char", fun s -> s );
         *)
         | _ -> print_endline ("Unknown constant type: "^(pp_type tt)); assert false
      )
      | Var(k) -> this#translate_ident k
      | Abs(p,b) -> "(fn "^(this#translate_ident p)^" => "^(this#translate_term b)^")"
      | App((Var("@")),_) as t-> this#translate_simple_macro t
      | App(f,x) -> (* if is_applied_macro f then this#translate_macro f [x] else *)
        "("^(this#translate_term f)^" "^(this#translate_term x)^")"
   )
   method translate ((ns,a):annotated_namespace): target_executable = (
      print_endline ("|annotations| = "^(string_of_int (List.length a)));
      List.iter (
         fun (t,tt) -> print_endline ((string_of_int (term_n t))^" : "^(pp_type tt))
      ) a;
      let type_binds = List.flatten (List.map (function
         (* how should this work? *)
         | _ -> []
      ) ns) in
      let term_binds = List.flatten (List.map (function
         | NS_bind (k,t) -> [k,t]
         | _ -> []
      ) ns) in
      let term_stmts = List.flatten (List.map (function
         | NS_expr t -> [t]
         | _ -> []
      ) ns) in
      let sml_source = (if (List.length term_binds)>0 then "val " else "") ^ (
         string_join "\nand " 
         (List.map (fun (k,t) -> (this#translate_ident k)^" = "^(this#translate_term t)) term_binds)
      ) ^ (if (List.length term_binds)>0 then ";\n\n" else "") ^ (
         string_join ";\n" (List.map this#translate_term term_stmts)
      ) ^ (if (List.length term_stmts)>0 then ";" else "") in
      print_endline "MLton program source:";
      print_endline sml_source;
      (* compile with mlton *)
      let exe_file = !option_out in
      let tmp_name,tmp_out = Filename.open_temp_file "tmpluck_" ".sml" in
      output_string tmp_out sml_source;
      close_out tmp_out;
      let retcode = Sys.command ("mlton -output "^exe_file^" "^tmp_name) in
      if retcode != 0 then (
         let source_lines = Str.split_delim (Str.regexp "[\n]") sml_source in
         let tabwidth = String.length ((string_of_int (List.length source_lines))^" ") in
         for ri=1 to (List.length source_lines) do
            let line_number = (string_of_int ri) in
            print_endline( line_number^(String.make (tabwidth-(String.length line_number)) ' ')^(List.nth source_lines (ri-1)))
         done
      );
      [exe_file]
   )
end
let language_table : (string * target_language) list = [
   ("sml", new sml_language)
]
let translate (ans: annotated_namespace): target_executable = (
   let language = try 
      List.assoc (!option_target) language_table
   with Not_found -> fatal_error ("Could not find target definition for language \""^(!option_target)^"\"")
   in language#translate ans
)
