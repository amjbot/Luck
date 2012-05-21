open Misc
open Ast

let file_bundle : file_bundle ref = ref []

let anon_fun arg = (
   if arg @@ "charm" then
      List.iter (fun f -> file_bundle := (f :: (!file_bundle))) (find ".*[.]lux")
   else file_bundle := (arg :: (!file_bundle))
)
let options = [
  ("-test",(Arg.Unit (fun _ -> Ast.option_test := true)),"Run internal tests")
]

let _ = Ast.option_typesystem := Some (new Ts_luck.checker)
let _ = Arg.parse options anon_fun "luck [path...]"
let _ = Prj.compile !file_bundle
