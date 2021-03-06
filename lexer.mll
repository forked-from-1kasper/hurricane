{
  open Parser
  open Lexing

  let nextLine lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = pos.pos_cnum;
                 pos_lnum = pos.pos_lnum + 1 }

  let ten = Z.of_int 10

  let getLevel s =
    let res = ref Z.zero in let queue = Queue.of_seq (String.to_seq s) in
    let sym = Queue.take queue in if (sym <> 'U' && sym <> 'V') then
      failwith "invalid universe";

    while not (Queue.is_empty queue) do
      if (Queue.take queue <> '\xE2' ||
          Queue.take queue <> '\x82')
      then failwith "invalid universe level while lexing";

      let value = Char.code (Queue.take queue) - 0x80 in
      res := Z.add (Z.mul !res ten) (Z.of_int value)
    done; !res
}

let lat1   = [^ '\t' ' ' '\r' '\n' '(' ')' ':' '.' ',' '<' '>']
let beg    = lat1 # '-'
let bytes2 = ['\192'-'\223']['\128'-'\191']
let bytes3 = ['\224'-'\239']['\128'-'\191']['\128'-'\191']
let bytes4 = ['\240'-'\247']['\128'-'\191']['\128'-'\191']['\128'-'\191']

let nl               = "\r\n"|"\r"|"\n"
let inlineComment    = "--" [^ '\n' '\r']* (nl|eof)
let multilineComment = "{-" [^ '-']* '-' ([^ '-' '}'][^ '-']* '-' | '-')* '}'
let comment          = inlineComment | multilineComment

let utf8    = lat1|bytes2|bytes3|bytes4
let ident   = beg utf8*
let ws      = ['\t' ' ']
let colon   = ':'
let defeq   = ":="     | "\xE2\x89\x94" | "\xE2\x89\x9C" | "\xE2\x89\x9D" (* ≔ | ≜ | ≝ *)
let arrow   = "->"     | "\xE2\x86\x92" (* → *)
let prod    = "*"      | "\xC3\x97"     (* × *)
let lam     = "\\"     | "\xCE\xBB"     (* λ *)
let pi      = "forall" | "\xCE\xA0"     (* Π *)
let sigma   = "sigma"  | "\xCE\xA3"     (* Σ *)
let def     = "definition" | "def" | "theorem" | "lemma" | "corollary" | "proposition"
let axiom   = "axiom"|"postulate"

let subscript = '\xE2' '\x82' ['\x80'-'\x89']
let kan       = 'U' subscript*

let nind  = "N-ind"
let zind  = "Z-ind"

let bot    = "_|_" | "\xE2\x8A\xA5" (* ⊥ *)
let botrec = bot "-rec"

rule main = parse
| nl         { nextLine lexbuf; main lexbuf }
| comment    { nextLine lexbuf; main lexbuf }
| ws+        { main lexbuf }
| "module"   { MODULE }      | "where"    { WHERE }
| "import"   { IMPORT }      | "option"   { OPTION }
| def        { DEF }         | colon      { COLON }
| ','        { COMMA }       | '_'        { IRREF }
| '('        { LPARENS }     | ')'        { RPARENS }
| ".1"       { FST }         | ".2"       { SND }
| pi         { PI }          | sigma      { SIGMA }
| "<"        { LT }          | ">"        { GT }
| axiom      { AXIOM }       | defeq      { DEFEQ }
| lam        { LAM }         | arrow      { ARROW }
| prod       { PROD }        | kan as s   { KAN (getLevel s) }
| "?"        { HOLE }        | nind       { NIND }
| zind       { ZIND }        | botrec     { BOTREC }
| "coe"      { COE }         | "PathP"    { PATHP }
| "@"        { APPFORMULA }  | "iso"      { ISO }
| ident as s { IDENT s }     | eof        { EOF }
