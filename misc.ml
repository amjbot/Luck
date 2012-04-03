open Unix
open Str
exception NotImplemented


let _uid = ref 0
let unique_int () = incr _uid; !_uid
let unique_string () = "_uuid_"^(string_of_int (unique_int()))

let get_option x = match x with
   | Some t -> t
   | None -> raise Not_found

let rec string_join : string -> string list -> string = fun sep -> function
   | [] -> ""
   | s :: [] -> s
   | s :: ss -> s ^ sep ^ (string_join sep ss)

let id x = x
let ($) x f = f x
let (@@) str pat = Str.string_match (Str.regexp pat) str 0
let grep str pat = (
   if not (Str.string_match (Str.regexp pat) str 0)
   then raise Not_found
   else Str.matched_group 1 str
)
let env v = try Sys.getenv v with Not_found -> ""

let find pattern =
  let select str = Str.string_match (Str.regexp pattern) str 0 in
  let rec walk acc = function
  | [] -> (acc)
  | dir::tail ->
      let contents = Array.to_list (Sys.readdir dir) in
      let contents = List.rev_map (Filename.concat dir) contents in
      let dirs, files =
        List.fold_left (fun (dirs,files) f ->
             match (stat f).st_kind with
             | S_REG -> (dirs, f::files)
             | S_DIR -> (f::dirs, files)
             | _ -> (dirs, files)
          ) ([],[]) contents
      in
      let matched = List.filter (select) files in
      walk (matched @ acc) (dirs @ tail)
  in
  walk [] ["."]
;;
let absolute_path filename = filename;;

class type ['a, 'b] hash_table =
   object 
     method has : 'a -> bool
     method get : 'a -> 'b
     method set : 'a -> 'b -> unit
     method del : 'a -> unit
     method items : unit -> ('a*'b) list
     method keys : unit -> ('a) list
     method values : unit -> ('b) list
     method clear : unit -> unit
     method shadow : unit -> ('a, 'b) hash_table
   end;;
class ['a, 'b] hashtable : ['a, 'b] hash_table =
   object (self)
     val table = Hashtbl.create 1024
     method has key = Hashtbl.mem table key
     method get key = Hashtbl.find table key
     method set key = Hashtbl.replace table key
     method del key = Hashtbl.remove table key
     method items () = Hashtbl.fold (fun k v c -> (k,v) :: c) table []
     method clear () = Hashtbl.clear table
     method keys () = List.map fst (self#items ())
     method values () = List.map snd (self#items ())
     method shadow () = 
     let new_table = new hashtable in
     List.iter (fun (k,v) -> new_table#set k v) (self#items());
     new_table
     (* new shadow_table (self:> ('a,'b) hash_table) *)
   end
(*
and ['a, 'b] shadow_table parent : ['a, 'b] hash_table =
   object (self)
     val table = Hashtbl.create 1024
     val hide = Hashtbl.create 1024
     method has key = (Hashtbl.mem table key) || parent#has key
     method get key = try Hashtbl.find table key with Not_found -> parent#get key
     method set key = Hashtbl.replace table key
     method clear () = Hashtbl.clear table; parent#clear()
     method items () = (Hashtbl.fold (fun k v c -> (k,v) :: c) table []) @ (parent#items ())
     method keys () = (List.map fst (self#items ())) @ (parent#keys ())
     method values () = (List.map snd (self#items ())) @ (parent#values ()) 
     method shadow () = new shadow_table (self:> ('a,'b) hash_table)
   end;;
*)
