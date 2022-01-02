open Parser

let tokenToString : token -> string = function
  | IDENT s    -> Printf.sprintf "IDENT %s" s
  | KAN u      -> Printf.sprintf "KAN %s" (Z.to_string u)
  | DEF        -> "DEF"         | SIGMA      -> "SIGMA"
  | PI         -> "PI"          | HOLE       -> "HOLE"
  | RPARENS    -> "RPARENS"     | LPARENS    -> "LPARENS"
  | LAM        -> "LAM"         | PROD       -> "PROD"
  | OPTION     -> "OPTION"      | AXIOM      -> "AXIOM"
  | IRREF      -> "IRREF"       | EOF        -> "EOF"
  | FST        -> "FST"         | SND        -> "SND"
  | DEFEQ      -> "DEFEQ"       | COMMA      -> "COMMA"
  | COLON      -> "COLON"       | ARROW      -> "ARROW"
  | WHERE      -> "WHERE"       | MODULE     -> "MODULE"
  | IMPORT     -> "IMPORT"      | BOTREC     -> "BOTREC"
  | NIND       -> "NIND"        | ZIND       -> "ZIND"