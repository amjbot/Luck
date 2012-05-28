open Log
open Ast
open Gen
open Misc
open Str

open CharParse.CharPrim
open CharParse.CharComb
open CharParse.M

let string_of_chars cs = (
   let ss = String.create (List.length cs) in
   let si = ref 0 in
   List.iter (fun c -> String.set ss !si c; incr si) cs; 
   ss
)

type uri = { scheme: string; path: string }
let create_uri ~scheme:scheme ~path:path = { scheme=scheme; path=path }
let parse_uri st = (
   (attempt ((many1 alphaNum) >>= fun cscheme -> string "://" >> return (string_of_chars cscheme)) <|> return "luck") 
   >>= fun scheme -> (many1 (noneOf ['?']))
   >>= fun cpath -> return (create_uri ~scheme:scheme ~path:(string_of_chars cpath))
) st
let parse_uri uri = (
  match parse "uri" (LazyList.M.ofString uri) parse_uri with
      Success x -> x
    | Failure err -> fatal_error("Unable to parse path uri: "^(Error.M.errorToString err))
);;
let print_uri uri = uri.scheme ^ "://" ^ uri.path;;




let load_luck_resource ?tgt:(tgt="sml") uri = (
   let uri = {uri with path=absolute_path uri.path} in
   let default_imports = if string_match (regexp ".*lang\\([.][a-zA-Z]+\\)?[.]lu$") uri.path 0 
       then [] else [NS_import ("lang.lu","",["*"])] in
   let namespace = default_imports @ Prs.parse_module uri.path in
   let dependencies = List.flatten (List.map (function
       | NS_import (imp,prefix,symbols) -> (
          let imp_uri = parse_uri imp in
          let unsettled_uri = ref None in
          List.iter (fun p ->
              let f = (Filename.concat p imp_uri.path) in
              if Sys.file_exists f then unsettled_uri := Some f
              else let f = global_replace (regexp "[.]lu$") ".sml.lu" f in
              if Sys.file_exists f then unsettled_uri := Some f
          ) (split (regexp ";") (env "LUCK_PATH"));
          let settled_uri = (match !unsettled_uri with
             | Some x -> x
             | None -> Filename.concat (Filename.dirname uri.path) imp_uri.path
          ) in
          [print_uri { imp_uri with path=settled_uri }, prefix, symbols]
       )
       | _ -> []
   ) namespace) in
   ((print_uri uri),namespace,dependencies)
)
let load_resource uri = (
  match uri.scheme with
  | "luck" -> load_luck_resource uri
  | _ -> fatal_error ("unrecognized resource scheme: "^uri.scheme)
)


let file2resource (fb: file_bundle) = (
   let resource_bundle = new hashtable in
   let frontier = ref fb in
   while List.length !frontier > 0 do
      let file = List.hd !frontier in
      let file = print_uri (parse_uri file) in
      frontier := List.tl !frontier;     
      if not (resource_bundle#has file) then (
         let (uri, ns, depends) = load_resource (parse_uri file) in
         let uri = print_uri (parse_uri uri) in
         resource_bundle#set uri (uri,ns,depends);
         frontier := !frontier @ (List.map (fun (a,b,c) -> a) depends)
      )
   done;
   List.map (fun (uri, ns, dep) ->
       (uri, ns, List.map (fun (link, prefix, symbols) ->
           match resource_bundle#get link with (_,nslink,_) -> (link, nslink, prefix, symbols)
       ) dep)
   ) (resource_bundle#values ())
)
let resource2annotated (rb: resource_bundle) = Typ.annotate rb
let annotated2target (arb: annotated_namespace) = Gen.translate arb
let compile (fb: file_bundle): unit = 
  (fb $ file2resource $ resource2annotated $ annotated2target $ ignore)
