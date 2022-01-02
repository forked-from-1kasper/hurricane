open Ident
open Error
open Expr

let extPair : value -> value * value = function
  | VPair (u, v) -> (u, v)
  | v            -> raise (ExpectedPair v)

let extPi : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u -> raise (ExpectedPi u)

let extPathP = function
  | VApp (VApp (VPathP v, u0), u1) -> (v, u0, u1)
  | v                              -> raise (ExpectedPath v)

let extSig : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u -> raise (ExpectedSig u)

let extKan : value -> Z.t = function
  | VKan n -> n
  | v      -> raise (ExpectedFibrant v)

let extVar ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value (Var (y, _))) -> y
  | Some (_, _, Exp (EVar y)) -> y
  | _ -> x

let imax a b = match a, b with
  | VKan u, VKan v -> VKan (max u v)
  | _, _ -> raise (ExpectedVSet a)

let implv a b = VPi (a, (Irrefutable, fun _ -> b))
let prodv a b = VSig (a, (Irrefutable, fun _ -> b))
let pathv t a b = VApp (VApp (VPathP (VLam (VI, (Irrefutable, fun _ -> t))), a), b)

let succv n = VApp (VSucc, n)
let posv  n = VApp (VPos,  n)
let negv  n = VApp (VNeg,  n)

let impl a b = EPi (a, (Irrefutable, b))
let prod a b = ESig (a, (Irrefutable, b))

let freshVar ns n = match Env.find_opt n ns with Some x -> x | None -> n

let rec salt (ns : name Env.t) : exp -> exp = function
  | ELam (a, (p, b))      -> saltTele eLam ns p a b
  | EKan n                -> EKan n
  | EPi (a, (p, b))       -> saltTele ePi ns p a b
  | ESig (a, (p, b))      -> saltTele eSig ns p a b
  | EPair (a, b)          -> EPair (salt ns a, salt ns b)
  | EFst e                -> EFst (salt ns e)
  | ESnd e                -> ESnd (salt ns e)
  | EApp (f, x)           -> EApp (salt ns f, salt ns x)
  | EVar x                -> EVar (freshVar ns x)
  | EHole                 -> EHole
  | EN                    -> EN
  | EZero                 -> EZero
  | ESucc                 -> ESucc
  | ENInd e               -> ENInd (salt ns e)
  | EZ                    -> EZ
  | EPos                  -> EPos
  | ENeg                  -> ENeg
  | EZSucc                -> EZSucc
  | EZPred                -> EZPred
  | EZInd e               -> EZInd (salt ns e)
  | EBot                  -> EBot
  | EBotRec e             -> EBotRec (salt ns e)
  | EI                    -> EI
  | EPathP e              -> EPathP (salt ns e)
  | ELeft                 -> ELeft
  | ERight                -> ERight
  | ECoe e                -> ECoe (salt ns e)
  | EPLam e               -> EPLam (salt ns e)
  | EAppFormula (p, i)    -> EAppFormula (salt ns p, salt ns i)
  | EIso e                -> EIso (salt ns e)

and saltTele ctor ns p a b =
  let x = fresh p in ctor x (salt ns a) (salt (Env.add p x ns) b)

let freshExp = salt Env.empty

let convVar p = function
  | Var (q, _) -> p = q
  | _          -> false

let rho2 x x' y y' = Env.add y y' (Env.add x x' Env.empty)
