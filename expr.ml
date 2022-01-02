open Ident

type exp =
  | EKan of Z.t                                                               (* cosmos *)
  | EVar of name | EHole                                                   (* variables *)
  | EPi of exp * (name * exp) | ELam of exp * (name * exp) | EApp of exp * exp     (* Π *)
  | ESig of exp * (name * exp) | EPair of exp * exp | EFst of exp | ESnd of exp    (* Σ *)
  | EI | ELeft | ERight | ECoe of exp                                       (* interval *)
  | EPathP of exp | EPLam of exp | EAppFormula of exp * exp                     (* path *)
  | EN | EZero | ESucc | ENInd of exp                                              (* N *)
  | EZ | EPos | ENeg | EZInd of exp | EZSucc | EZPred                              (* Z *)
  | EBot | EBotRec of exp                                                          (* ⊥ *)

type tele = name * exp

type scope = Local | Global

type value =
  | VKan of Z.t
  | Var of name * value | VHole
  | VPi of value * clos | VLam of value * clos | VApp of value * value
  | VSig of value * clos | VPair of value * value | VFst of value | VSnd of value
  | VI | VLeft | VRight | VCoe of value
  | VPathP of value | VPLam of value | VAppFormula of value * value
  | VN | VZero | VSucc | VNInd of value
  | VZ | VPos | VNeg | VZInd of value | VZSucc | VZPred
  | VBot | VBotRec of value

and clos = name * (value -> value)

and term = Exp of exp | Value of value

and record = scope * term * term

and ctx = record Env.t

let eLam p a b = ELam (a, (p, b))
let ePi  p a b = EPi  (a, (p, b))
let eSig p a b = ESig (a, (p, b))

let name x = Name (x, 0)
let decl x = EVar (name x)

let upVar p x ctx = match p with Irrefutable -> ctx | _ -> Env.add p x ctx

let upLocal ctx p t v : ctx = upVar p (Local, Value t, Value v) ctx
let upGlobal ctx p t v : ctx = upVar p (Global, Value t, Value v) ctx

let rec telescope ctor e : tele list -> exp = function
  | (p, a) :: xs -> ctor p a (telescope ctor e xs)
  | []           -> e

let parens b x = if b then "(" ^ x ^ ")" else x

let rec ppExp paren e = let x = match e with
  | EKan n -> "U" ^ showSubscript n
  | ELam (a, (p, b)) -> Printf.sprintf "λ %s, %s" (showTele p a) (showExp b)
  | EPi (a, (p, b)) -> showPiExp a p b
  | ESig (a, (p, b)) -> Printf.sprintf "Σ %s, %s" (showTele p a) (showExp b)
  | EPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showExp fst) (showExp snd)
  | EFst exp -> ppExp true exp ^ ".1"
  | ESnd exp -> ppExp true exp ^ ".2"
  | EApp (f, x) -> Printf.sprintf "%s %s" (showExp f) (ppExp true x)
  | EVar p -> showName p | EHole -> "?"
  | EI -> "I" | ELeft -> "left" | ERight -> "right"
  | ECoe e -> Printf.sprintf "coe %s" (ppExp true e)
  | EPathP e -> Printf.sprintf "PathP %s" (ppExp true e)
  | EPLam (ELam (_, (i, e))) -> Printf.sprintf "<%s> %s" (showName i) (showExp e)
  | EPLam _ -> failwith "showExp: unreachable code was reached"
  | EAppFormula (f, x) -> Printf.sprintf "%s @ %s" (ppExp true f) (ppExp true x)
  | EN -> "N" | EZero -> "zero" | ESucc -> "succ"
  | ENInd e -> Printf.sprintf "N-ind %s" (ppExp true e)
  | EZ -> "Z" | EPos -> "pos" | ENeg -> "neg" | EZSucc -> "Z-succ" | EZPred -> "Z-pred"
  | EZInd e -> Printf.sprintf "Z-ind %s" (ppExp true e)
  | EBot -> "⊥" | EBotRec e -> Printf.sprintf "⊥-ind %s" (ppExp true e)
  in match e with
  | EKan _ | EVar _  | EFst _ | ESnd _
  | EHole  | EPair _ | EBot
  | EN     | EZero   | ESucc
  | EZ     | EPos    | ENeg
  | EI     | ELeft   | ERight -> x
  | _ -> parens paren x

and showExp e = ppExp false e
and showTele p x = Printf.sprintf "(%s : %s)" (showName p) (showExp x)

and showPiExp a p b = match p with
  | Irrefutable -> Printf.sprintf "%s → %s" (ppExp true a) (showExp b)
  | _           -> Printf.sprintf "Π %s, %s" (showTele p a) (showExp b)

let rec ppValue paren v = let x = match v with
  | VKan n -> "U" ^ showSubscript n
  | VLam (x, (p, clos)) -> Printf.sprintf "λ %s, %s" (showTele p x) (showClos p x clos)
  | VPi (x, (p, clos)) -> showPiValue x p clos
  | VSig (x, (p, clos)) -> Printf.sprintf "Σ %s, %s" (showTele p x) (showClos p x clos)
  | VPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showValue fst) (showValue snd)
  | VFst v -> ppValue true v ^ ".1"
  | VSnd v -> ppValue true v ^ ".2"
  | VApp (f, x) -> Printf.sprintf "%s %s" (showValue f) (ppValue true x)
  | Var (p, _) -> showName p | VHole -> "?"
  | VI -> "I" | VLeft -> "left" | VRight -> "right"
  | VCoe v -> Printf.sprintf "coe %s" (ppValue true v)
  | VPathP v -> Printf.sprintf "PathP %s" (ppValue true v)
  | VPLam (VLam (_, (p, clos))) -> Printf.sprintf "<%s> %s" (showName p) (showClos p VI clos)
  | VPLam _ -> failwith "showExp: unreachable code was reached"
  | VAppFormula (f, x) -> Printf.sprintf "%s @ %s" (ppValue true f) (ppValue true x)
  | VN -> "N" | VZero -> "zero" | VSucc -> "succ"
  | VNInd e -> Printf.sprintf "N-ind %s" (ppValue true e)
  | VZ -> "Z" | VPos -> "pos" | VNeg -> "neg" | VZSucc -> "Z-succ" | VZPred -> "Z-pred"
  | VZInd e -> Printf.sprintf "Z-ind %s" (ppValue true e)
  | VBot -> "⊥" | VBotRec e -> Printf.sprintf "⊥-ind %s" (ppValue true e)
  in match v with
  | VKan _ | Var _   | VFst _ | VSnd _ 
  | VHole  | VPair _ | VBot
  | VN     | VZero   | VSucc
  | VZ     | VPos    | VNeg
  | VI     | VLeft   | VRight -> x
  | _ -> parens paren x

and showValue v = ppValue false v
and showClos p t clos = showValue (clos (Var (p, t)))

and showTele p x = Printf.sprintf "(%s : %s)" (showName p) (showValue x)

and showPiValue x p clos = match p with
  | Irrefutable -> Printf.sprintf "%s → %s" (ppValue true x) (showClos p x clos)
  | _           -> Printf.sprintf "Π %s, %s" (showTele p x) (showClos p x clos)

and showTerm : term -> string = function Exp e -> showExp e | Value v -> showValue v

let showGamma (ctx : ctx) : string =
  Env.bindings ctx
  |> List.filter_map
      (fun (p, x) -> match x with
        | Local, t, _ -> Some (Printf.sprintf "%s : %s" (showName p) (showTerm t))
        | _, _, _     -> None)
  |> String.concat "\n"
