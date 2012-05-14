module LuckLD : Language.LanguageDef =
struct
  open CharParse.CharPrim
  open CharParse.M

  let commentStart = "(*"
  let commentEnd = "*)"
  let commentLine = "#"
  let nestedComments = true
  let identStart st = (letter <|> (char '_')) st
                             (* of course, a leading prime is used in the
                             case of tyvars, but it's easiest to handle
                             these seperately *)
  let identLetter st = (alphaNum <|> (char '_')) st
  let reservedOpNames = ["[";"]";"{";"}";"(";")";";";":";",";"'"]
  let opStart st = oneOf (explode "!%&$#+-/:<=>>@\\~'^|*") st
  let opLetter st = oneOf (List.filter (fun i -> not (List.mem (String.make 1 i) reservedOpNames)) (explode "!%&$#+-/:<=>>@\\~'^|*")) st
  let reservedNames =
    ["_"; "and"; "as"; "catch"; "do"; "else";
     "fn"; "for"; "function"; "if"; "import"; "in"; 
     "let"; "new"; "of"; "or"; "property"; "then"; "throw"; 
     "type"; "with"; "while"]

  (* cannot be used in user-defined operators *)

  let caseSensitive = true

  let negSign st = (char '-') st
  let posSign = mzero

end

module L = Language.M(LuckLD)
open L
open CharParse
open CharPrim
open CharComb
open CharExpr

exception ParseError of string
open Misc
open Ast


(* token parsers *)
let pINT     st = (integer >>= fun c -> return (string_of_int c)) st
let pFLOAT   st = (float >>= fun c -> return (string_of_float c)) st
let pBOOL st = (
   (reserved "true" >>= fun _ -> return "true") <|>
   (reserved "false" >>= fun _ -> return "false")
) st;;
let pCHAR st = (
   symbolChar '\'' >> (charLetter <|> charEscape) >>= fun c -> symbolChar '\'' >> return (Char.escaped c)
) st;;
let pSTRING st = stringLiteral st
let identifier st = (identifier <|> (reservedOp "$" >> stringLiteral)) st
let pTYPE st = (get_option (!Ast.option_typesystem))#parse st

let rec pCONST st = (
   (reserved "true" >> return (con "true" "bool")) <|>
   (reserved "false" >> return (con "false" "bool")) <|>
   (pINT >>= fun c -> return (con c "int")) <|>
   (pFLOAT >>= fun c -> return (con c "float")) <|>
   (pCHAR >>= fun c -> return (con c "char")) <|>
   (pSTRING >>= fun c -> return (con c "string"))
) st
and pATOM st = (
   pCONST <|>
   (parens pEXPR) <|>
   (brackets (commaSep pEXPR) >>= fun ls -> 
      return (List.fold_left
         (fun t v -> binop ".add" t v) (var "[]") ls
      )
   ) <|>
   (reserved "new" >> identifier >>= fun c -> return (var ("new "^c))) <|>
   (identifier >>= fun c -> return (var c)) <|>
   (reservedOp "..." >>= fun _ -> return (app (var "throw") (var "NotImplemented"))) <|>
   (reservedOp "@" >> many pEXPR >>= fun sexp -> return (app (var "@") (List.fold_left app (con "" "string") sexp)) )
) st

(*
    declaring syntactic forms, and declaring functions are totally separate things.
    type directed parsing cannot unify, due to insane ambiguities with type inference.
    one syntactic form must have one interpretation... per namespace at least.
*)

and pSIMPLEEXPR st =
  let table = [
    (* Pointer Dereferencing *)
    [Postfix (reservedOp "!" >> return (fun l -> uniop "!" l))];
    
    [
    (* Function Application *)
     Postfix (parens pEXPR >>= fun r -> return (fun l -> app l r));

    (* Subscription, Slicing *)
     Postfix (brackets (
        (pEXPR <|> return (var "()")) >>= fun l -> 
        (
           (reservedOp ":" >> (pEXPR <|> return (var "()")) >>= fun r -> return (fun t -> triop "[:]" t l r)) <|>
           (return (fun t -> binop "[]" t l))
        )
     ));

    (* Attribute Reference *)
     Postfix (reservedOp "." >> identifier >>= fun r -> return (fun l -> uniop ("."^r) l) )
    ];

    (* Exponentiation *)
    [Infix (AssocLeft, reservedOp "**" >> return (fun e1 e2 -> binop "**" e1 e2  ))];

    (* Positive, Negative *)
    [Prefix (reservedOp "+" >> return (fun e -> app (var "+") e )); Prefix (reservedOp "-" >> return (fun e -> uniop "-" e ))];

    (* Multiplication, Division, Floor Division, Remainder *)
    [
       Infix (AssocLeft, reservedOp "*" >> return (fun e1 e2 -> binop "*" e1 e2 ));
       Infix (AssocLeft, reservedOp "/" >> return (fun e1 e2 -> binop "/" e1 e2 ));
       Infix (AssocLeft, reservedOp "//" >> return (fun e1 e2 -> binop "//" e1 e2 ));
       Infix (AssocLeft, reservedOp "%" >> return (fun e1 e2 -> binop "%" e1 e2 ));
    ];

    (* Addition, Subtraction *)
    [
       Infix (AssocLeft, reservedOp "+" >> return (fun e1 e2 -> binop "+" e1 e2  ));
       Infix (AssocLeft, reservedOp "-" >> return (fun e1 e2 -> binop "-" e1 e2  ))
    ];

    (* Left Shift, Right Shift *)
    [
       Infix (AssocLeft, reservedOp ">>" >> return (fun e1 e2 -> binop ">>" e1 e2  ));
       Infix (AssocLeft, reservedOp "<<" >> return (fun e1 e2 -> binop "<<" e1 e2  ))
    ];

    (* Comparison Operators *)
    [
       Infix (AssocLeft, reservedOp ">" >> return (fun e1 e2 -> binop ">" e1 e2  ));
       Infix (AssocLeft, reservedOp "<" >> return (fun e1 e2 -> binop "<" e1 e2  ));
       Infix (AssocLeft, reservedOp ">=" >> return (fun e1 e2 -> binop ">=" e1 e2  ));
       Infix (AssocLeft, reservedOp "<=" >> return (fun e1 e2 -> binop "<=" e1 e2  ));
       Infix (AssocLeft, reservedOp "!=" >> return (fun e1 e2 -> binop "!=" e1 e2  ));
       Infix (AssocLeft, reservedOp "==" >> return (fun e1 e2 -> binop "==" e1 e2  ));
       Infix (AssocLeft, reservedOp "~=" >> return (fun e1 e2 -> binop "~=" e1 e2  ))
    ];

    (* Identity Tests *)
    [
       Infix (AssocLeft, reserved "is" >> return (fun e1 e2 -> binop "is" e1 e2  ));
       Infix (AssocLeft, reserved "is" >> reserved "not" >> return (fun e1 e2 -> uniop "not" (binop "is" e1 e2)  ));
    ];

    ]
  in
    ( (((buildExpressionParser table pATOM) <?> "expression") st ) : ('a, Ast.term) CharParse.CharPrim.rcon) 

and pEXPR st =
  let table = [
    (* Membership Tests *)
    [
       Infix (AssocLeft, reserved "in" >> return (fun e1 e2 -> binop "in" e1 e2  ));
       Infix (AssocLeft, reserved "not" >> reserved "in" >> return (fun e1 e2 -> uniop "not" (binop "in" e1 e2)  ));
    ];

    (* Boolean Not *)
    [Prefix (reserved "not" >> return (fun e -> uniop "not" e ))];

    (* Boolean And *)
    [Infix (AssocLeft, reserved "and" >> return (fun e1 e2 -> binop "and" e1 e2  ))];

    (* Boolean Or *)
    [Infix (AssocLeft, reserved "or" >> return (fun e1 e2 -> binop "or" e1 e2  ))];

    (* Assignment Operators *)
    [
       Infix (AssocLeft, reservedOp ":=" >> return (fun e1 e2 -> binop ":=" e1 e2  ));
       Infix (AssocLeft, reservedOp "+=" >> return (fun e1 e2 -> binop "+=" e1 e2  ))
    ];

    (* Throw Expression *)
    [Nonfix ( reserved "throw" >> (pEXPR
              >>= fun e1 -> return (uniop "throw" e1)
    ) <?> "throw expression" )];

    (* If Expression *)
    [Nonfix ( reserved "if" >> (pEXPR
              >>= fun e1 -> reserved "then" >> pEXPR
              >>= fun e2 -> ((reserved "else" >> pEXPR) <|> return (var "()"))
              >>= fun e3 -> return (triop "if" e1 e2 e3)
    ) <?> "if expression" );

    (* While Loop *)
    Prefix ( reserved "while" >> (pEXPR
              >>= fun e1 -> reserved "then"
              >>  return (fun e2 -> (binop "while" e1 e2) )
    ) <?> "while expression" )];

    (* Function Composition *)
    [Infix (AssocLeft, reservedOp "|" >> return (fun e1 e2 -> binop "|" e1 e2  ))];

    (* Lambda Declaration *)
    [Prefix ( reservedOp "\\" >> identifier
              >>= fun p -> reservedOp "."
              >> return (fun e -> abs p e) )];

    (* Sequence Operator *)
    [Infix (AssocLeft, reservedOp ";" >> return (fun e1 e2 -> binop ";" e1 e2  ))];

  ] in (
  (attempt
     ((pSIMPLEEXPR) >>= fun l -> reservedOp ":" >> 
     (many1(braces( pLHS >>= fun a -> reservedOp "->" >> pEXPR >>= fun b -> return (a,b)) ))
     >>= fun r -> return (app (pattern r) l) )
  ) <|>
  (buildExpressionParser table pSIMPLEEXPR) <?> "expression") st
and pLHS st = pATOM st
	

let pEXPRSTMT st = ((pEXPR >>= fun x -> return (NS_expr x)) <?> "expression") st;;
let pTYPESTMT st = ((pTYPE >>= fun x -> return (NS_type x)) <?> "type declaration") st;;
let pIMPORTSTMT st = ((
   pSTRING >>= fun x ->
   ((reserved "as" >> identifier) <|> return "") >>= fun y ->
   ((reserved "limit" >> (commaSep1 identifier)) <|> return ["*"]) >>= fun z ->
   optional (reservedOp ";") >> return (NS_import (x,y,z))
) <?> "import statement" ) st;;

let pFUNCTIONIDENT st = (
   (identifier >>= fun i -> return i) <|>
   (reservedOp "." >> identifier >>= fun i -> return ("."^i))
) st;;
let pFUNCTIONPARAMIDENT st = (
   identifier <|>
   ((reserved "_") >> (return "_"))
) st;;
let pOPTIONALTYPE st = (
   (reservedOp ":" >> ((pTYPE >>= fun t -> return (Some t)) <?> "ascribed type")) <|>
   (return None)
) st;;
let pFUNCTIONPARAM st = (
   parens (pFUNCTIONPARAMIDENT >>= fun p -> pOPTIONALTYPE >>= fun tt -> return ((fun b -> abs p b), tt))
) st;;
let pFUNCTION st = (
   pFUNCTIONIDENT >>= fun fn -> (many1 pFUNCTIONPARAM) >>= fun ps -> 
   pOPTIONALTYPE >>= fun rt -> (reservedOp "=") >> pEXPR >>= fun b -> return (
      let (f,ft) = List.fold_right (
         fun (p,pt) (b,rt) -> let (_,_,ft) = tarr (pt, rt, None) in
         ((p b),Some ft)
      ) (ps: ((term -> term)*(typ option)) list)
        ( (b:term), (rt:typ option) ) in
      ascript f (get_option ft); 
      NS_bind(fn,f)
   )
) st;;

let pLETSTMT st = ((
   identifier >>= fun p -> reservedOp "=" >> pEXPR >>= fun e -> 
   optional (reservedOp ";") >> return (NS_bind (p, e))
) <?> "let statement") st;;

let pTOPSTMT st = (
   (reserved "import" >> pIMPORTSTMT) <|>
   (reserved "type" >> pTYPESTMT) <|>
   (reserved "let" >> pLETSTMT) <|>
   (reserved "function" >> pFUNCTION) <|>
   pEXPRSTMT
) st;;
let rec pPROGRAM st = (
   (eof >> return []) <|>
   (pTOPSTMT >>= fun l -> pPROGRAM >>= fun r -> return (l :: r) ) <?>
   "program"
) st;;

let parse_expr : string -> typ = fun s -> (
    match parse "expr" (LazyList.M.ofString s)
          (whiteSpace >> pTYPE >>= fun r -> eof >> return r) with
        Success x -> x
      | Failure err -> raise (ParseError ("In <string> "^(Error.M.errorToString err)))
);;
let parse_module : string -> namespace_item list = fun f -> (
    match parse "program" (LazyList.M.ofChannel (open_in f))
          (whiteSpace >> pPROGRAM) with
        Success x -> x
      | Failure err -> raise (ParseError ("In "^f^" "^(Error.M.errorToString err)))
);;
