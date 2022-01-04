open Prelude
open Error
open Trace
open Ident
open Elab
open Expr

let ieq u v : bool = !Prefs.girard || u = v

let vfst : value -> value = function
  | VPair (u, _) -> u
  | v            -> VFst v

let vsnd : value -> value = function
  | VPair (_, u) -> u
  | v            -> VSnd v

let idfun t = VLam (t, (freshName "x", fun x -> x))

let freshDim () = Var (freshName "ι", VI)

(* Evaluator *)
let rec eval (e0 : exp) (ctx : ctx) = traceEval e0; match e0 with
  | EKan u                -> VKan u
  | EVar x                -> getRho ctx x
  | EHole                 -> VHole
  | EPi  (a, (p, b))      -> let t = eval a ctx in VPi (t, (fresh p, closByVal ctx p t b))
  | ESig (a, (p, b))      -> let t = eval a ctx in VSig (t, (fresh p, closByVal ctx p t b))
  | ELam (a, (p, b))      -> let t = eval a ctx in VLam (t, (fresh p, closByVal ctx p t b))
  | EApp (f, x)           -> app (eval f ctx, eval x ctx)
  | EPair (e1, e2)        -> VPair (eval e1 ctx, eval e2 ctx)
  | EFst e                -> vfst (eval e ctx)
  | ESnd e                -> vsnd (eval e ctx)
  | EN                    -> VN
  | EZero                 -> VZero
  | ESucc                 -> VSucc
  | ENInd e               -> VNInd (eval e ctx)
  | EZ                    -> VZ
  | EPos                  -> VPos
  | ENeg                  -> VNeg
  | EZSucc                -> VZSucc
  | EZPred                -> VZPred
  | EZInd e               -> VZInd (eval e ctx)
  | EBot                  -> VBot
  | EBotRec e             -> VBotRec (eval e ctx)
  | EI                    -> VI
  | ELeft                 -> VLeft
  | ERight                -> VRight
  | ECoe e                -> coe (eval e ctx)
  | EPathP e              -> VPathP (eval e ctx)
  | EPLam e               -> VPLam (eval e ctx)
  | EAppFormula (e, x)    -> appFormula (eval e ctx) (eval x ctx)
  | EIso e                -> VIso (eval e ctx)

and appFormula v x = match v with
  | VPLam f -> app (f, x)
  | _       -> let (_, u0, u1) = extPathP (inferV v) in
    begin match x with
      | VLeft  -> u0
      | VRight -> u1
      | i      -> VAppFormula (v, i)
    end

and coe p =
  let i = freshName "ι" in let t = app (p, Var (i, VI)) in
  (* coe (λ x, A) i ~> λ j y, y when x ∉ FV(A) *)
  if not (mem i t) then VLam (VI, (Irrefutable, fun _ -> idfun t)) else VCoe p

and closByVal ctx p t e v = traceClos e p v;
  (* dirty hack to handle free variables introduced by type checker *)
  let ctx' = match v with
  | Var (x, t) -> if Env.mem x ctx then ctx else upLocal ctx x t v
  | _          -> ctx in
  eval e (upLocal ctx' p t v)

and app (f, x) = match f, x with
  (* (λ (x : t), f) v ~> f[x/v] *)
  | VLam (_, (_, f)), v -> f v
  (* N-ind A z s zero ~> z *)
  | VApp (VApp (VNInd _, z), _), VZero -> z

  (* N-ind A z s (succ n) ~> s (N-ind A z s n) *)
  | VApp (VApp (VNInd _, _), s), VApp (VSucc, n) -> app (app (s, n), app (f, n))
  (* Z-ind A p n (pos x) ~> p x *)
  | VApp (VApp (VZInd _, p), _), VApp (VPos, x) -> app (p, x)
  (* Z-ind A p n (neg x) ~> n x *)
  | VApp (VApp (VZInd _, _), n), VApp (VNeg, x) -> app (n, x)

  (* Z-succ (neg (succ n)) ~> neg n *)
  | VZSucc, VApp (VNeg, VApp (VSucc, n)) -> negv n
  (* Z-succ (neg zero) ~> pos zero *)
  | VZSucc, VApp (VNeg, VZero) -> posv VZero
  (* Z-succ (pos n) ~> pos (succ n) *)
  | VZSucc, VApp (VPos, n) -> posv (succv n)
  (* Z-pred (neg n) ~> neg (succ n) *)
  | VZPred, VApp (VNeg, n) -> negv (succv n)
  (* Z-pred (pos zero) ~> neg zero *)
  | VZPred, VApp (VPos, VZero) -> negv VZero
  (* Z-pred (pos (succ n)) ~> pos n *)
  | VZPred, VApp (VPos, VApp (VSucc, n)) -> posv n
  (* Z-succ (Z-pred z) ~> z *)
  | VZSucc, VApp (VZPred, z) -> z
  (* Z-pred (Z-succ z) ~> z *)
  | VZPred, VApp (VZSucc, z) -> z

  (* coe A left ~> λ x, x *)
  | VCoe t, VLeft -> idfun (app (t, VLeft))
  (* iso A B f g p q left ~> A *)
  | VApp (VApp (VApp (VApp (VApp (VIso a, _), _), _), _), _), VLeft -> a
  (* iso A B f g p q right ~> B *)
  | VApp (VApp (VApp (VApp (VApp (VIso _, b), _), _), _), _), VRight -> b

  (* coe (iso A B f g p q) right ~> f *)
  | VCoe p, VRight -> let i = freshName "ι" in
    begin match app (p, Var (i, VI)) with
      | VApp (VApp (VApp (VApp (VApp (VApp (VIso a, b), f), g), p), q), j) ->
        if not (mem i a || mem i b || mem i f
             || mem i g || mem i p || mem i q) && convVar i j
        then f else VApp (VCoe p, VRight)
      | _ -> VApp (VCoe p, VRight)
    end
  | _, _ -> VApp (f, x)

and app2 f x y = app (app (f, x), y)

and getRho ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value v) -> v
  | Some (_, _, Exp e)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and act e i ctx = eval (EAppFormula (e, i)) ctx

(* This is part of evaluator, not type checker *)
and inferV v = traceInferV v; match v with
  | Var (_, t) -> t
  | VLam (t, (x, f)) -> VPi (t, (x, fun x -> inferV (f x)))
  | VPi (t, (x, f)) | VSig (t, (x, f)) -> imax (inferV t) (inferV (f (Var (x, t))))
  | VFst e -> inferFst (inferV e)
  | VSnd e -> inferSnd (vfst e) (inferV e)
  | VApp (f, x) -> let (_, (_, g)) = extPi (inferV f) in g x
  | VKan n -> VKan (Z.succ n)
  | VN -> VKan Z.zero | VZero -> VN | VSucc -> implv VN VN
  | VNInd v -> inferNInd v
  | VZ -> VKan Z.zero | VPos -> implv VN VZ | VNeg -> implv VN VZ
  | VZSucc -> implv VZ VZ | VZPred -> implv VZ VZ | VZInd v -> inferZInd v
  | VBot -> VKan Z.zero | VBotRec v -> implv VBot v
  | VI -> VKan Z.zero | VLeft | VRight -> VI
  | VCoe t -> inferCoe t
  | VPathP t -> inferPathP (extKan (inferV (app (t, freshDim ())))) t
  | VAppFormula (f, x) -> let (p, _, _) = extPathP (inferV f) in app (p, x)
  | VPLam f -> let t = VLam (VI, (freshName "ι", fun i -> inferV (app (f, i)))) in
    VApp (VApp (VPathP t, app (f, VLeft)), app (f, VRight))
  | VIso t -> inferIso (extKan (inferV t)) t
  | VPair _ | VHole -> raise (InferVError v)

and linv a f g = let x = freshName "x" in
  VPi (a, (x, fun x -> pathv a (app (g, app (f, x))) x))

and rinv b f h = let x = freshName "x" in
  VPi (b, (x, fun x -> pathv b (app (f, app (h, x))) x))

and inferIso k a = let f = freshName "f" in let g = freshName "g" in
  VPi (VKan k, (freshName "B", fun b ->
    VPi (implv a b, (f, fun f ->
      VPi (implv b a, (g, fun g ->
        implv (linv a f g)
          (implv (rinv b f g)
            (implv VI (VKan k)))))))))

and inferCoe t = VPi (VI, (freshName "ι", fun i -> implv (app (t, VLeft)) (app (t, i))))

and inferPathP n t = implv (app (t, VLeft)) (implv (app (t, VRight)) (VKan n))

and inferNInd v =
  let e = fun x -> app (v, x) in
  implv (e VZero)
    (implv (VPi (VN, (freshName "n", fun n -> implv (e n) (e (succv n)))))
           (VPi (VN, (freshName "n", e))))

and inferZInd v =
  let e = fun x -> app (v, x) in
  implv (VPi (VN, (freshName "n", e << posv)))
    (implv (VPi (VN, (freshName "n", e << negv)))
      (VPi (VZ, (freshName "z", e))))

and zsuccv z = app (VZSucc, z)

and inferFst = function
  | VSig (t, _) -> t
  | v           -> raise (ExpectedSig v)

and inferSnd v = function
  | VSig (_, (_, g)) -> g v
  | u                -> raise (ExpectedSig u)

(* Convertibility *)
and conv v1 v2 : bool = traceConv v1 v2;
  v1 == v2 || begin match v1, v2 with
    | VKan u, VKan v -> ieq u v
    | VPair (a, b), VPair (c, d) -> conv a c && conv b d
    | VPair (a, b), v | v, VPair (a, b) -> conv (vfst v) a && conv (vsnd v) b
    | VPi  (a, (p, f)), VPi  (b, (_, g))
    | VSig (a, (p, f)), VSig (b, (_, g))
    | VLam (a, (p, f)), VLam (b, (_, g)) ->
      let x = Var (p, a) in conv a b && conv (f x) (g x)
    | VLam (a, (p, f)), b | b, VLam (a, (p, f)) ->
      let x = Var (p, a) in conv (app (b, x)) (f x)
    | VApp (f, x), VApp (g, y) -> conv f g && conv x y
    | Var (u, _), Var (v, _) -> u = v
    | VFst x, VFst y | VSnd x, VSnd y -> conv x y
    | VN, VN -> true
    | VZero, VZero -> true
    | VSucc, VSucc -> true
    | VNInd u, VNInd v -> conv u v
    | VZ, VZ -> true
    | VPos, VPos -> true
    | VNeg, VNeg -> true
    | VZSucc, VZSucc -> true
    | VZPred, VZPred -> true
    | VZInd u, VZInd v -> conv u v
    | VBot, VBot -> true
    | VBotRec u, VBotRec v -> conv u v
    | VI, VI -> true
    | VLeft, VLeft -> true
    | VRight, VRight -> true
    | VCoe u, VCoe v -> conv u v
    | VPathP u, VPathP v -> conv u v
    | VPLam f, VPLam g -> conv f g
    | VPLam f, v | v, VPLam f -> let i = freshDim () in conv (appFormula v i) (app (f, i))
    | VAppFormula (f, x), VAppFormula (g, y) -> conv f g && conv x y
    | VIso u, VIso v -> conv u v
    | _, _ -> false
  end

and eqNf v1 v2 : unit = traceEqNF v1 v2;
  if conv v1 v2 then () else raise (Ineq (v1, v2))

(* Type checker itself *)
and lookup (x : name) (ctx : ctx) = match Env.find_opt x ctx with
  | Some (_, Value v, _) -> v
  | Some (_, Exp e, _)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and check ctx (e0 : exp) (t0 : value) =
  traceCheck e0 t0; try match e0, t0 with
  | EHole, v -> traceHole v ctx
  | ELam (a, (p, b)), VPi (t, (_, g)) ->
    ignore (extKan (infer ctx a)); eqNf (eval a ctx) t;
    let x = Var (p, t) in let ctx' = upLocal ctx p t x in check ctx' b (g x)
  | EPair (e1, e2), VSig (t, (_, g)) ->
    ignore (extKan (inferV t));
    check ctx e1 t; check ctx e2 (g (eval e1 ctx))
  | EPLam (ELam (EI, (i, e))), VApp (VApp (VPathP p, u0), u1) ->
    let v = Var (i, VI) in let ctx' = upLocal ctx i VI v in
    let v0 = eval e (upLocal ctx i VI VLeft) in
    let v1 = eval e (upLocal ctx i VI VRight) in
    check ctx' e (app (p, v)); eqNf v0 u0; eqNf v1 u1
  | e, t -> eqNf (infer ctx e) t
  with ex -> Printf.printf "When trying to typecheck\n  %s\nAgainst type\n  %s\n" (showExp e0) (showValue t0); raise ex

and infer ctx e : value = traceInfer e; try match e with
  | EVar x -> lookup x ctx
  | EKan u -> VKan (Z.succ u)
  | ESig (a, (p, b)) | EPi (a, (p, b)) -> inferTele ctx p a b
  | ELam (a, (p, b)) -> inferLam ctx p a b
  | EApp (f, x) -> begin match infer ctx f with
    | VPi (t, (_, g)) -> check ctx x t; g (eval x ctx)
    | v -> raise (ExpectedPi v)
  end
  | EFst e -> inferFst (infer ctx e)
  | ESnd e -> inferSnd (vfst (eval e ctx)) (infer ctx e)
  | EN -> VKan Z.zero | EZero -> VN | ESucc -> implv VN VN
  | ENInd e -> inferInd false ctx VN e inferNInd
  | EZ -> VKan Z.zero | EPos -> implv VN VZ | ENeg -> implv VN VZ
  | EZSucc -> implv VZ VZ | EZPred -> implv VZ VZ
  | EZInd e -> inferInd false ctx VZ e inferZInd
  | EBot -> VKan Z.zero | EBotRec e -> ignore (extKan (infer ctx e)); implv VBot (eval e ctx)
  | EI -> VKan Z.zero | ELeft | ERight -> VI
  | ECoe e -> let k = infer ctx e in let (t, (p, g)) = extPi k in
    let n = extKan (g (Var (p, t))) in eqNf k (implv VI (VKan n)); inferCoe (eval e ctx)
  | EPathP e -> let k = infer ctx e in let (t, (p, g)) = extPi k in
    let n = extKan (g (Var (p, t))) in eqNf k (implv VI (VKan n)); inferPathP n (eval e ctx)
  | EAppFormula (f, x) -> check ctx x VI;
    let (p, _, _) = extPathP (infer ctx f) in app (p, eval x ctx)
  | EPLam (ELam (EI, (i, e))) ->
    let ctx' = upLocal ctx i VI (Var (i, VI)) in ignore (infer ctx' e);
    let g = fun j -> eval e (upLocal ctx i VI j) in
    let t = VLam (VI, (freshName "ι", inferV >> g)) in
    VApp (VApp (VPathP t, g VLeft), g VRight)
  | EIso t -> inferIso (extKan (infer ctx t)) (eval t ctx)
  | EPLam _ | EPair _ | EHole -> raise (InferError e)
  with ex -> Printf.printf "When trying to infer type of\n  %s\n" (showExp e); raise ex

and inferInd fibrant ctx t e f =
  let (t', (p, g)) = extPi (infer ctx e) in eqNf t t'; let k = g (Var (p, t)) in
  ignore (if fibrant then extKan k else extKan k); f (eval e ctx)

and inferTele ctx p a b =
  ignore (extKan (infer ctx a));
  let t = eval a ctx in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in
  let v = infer ctx' b in imax (infer ctx a) v

and inferLam ctx p a e =
  ignore (extKan (infer ctx a)); let t = eval a ctx in
  ignore (infer (upLocal ctx p t (Var (p, t))) e);
  VPi (t, (p, fun x -> infer (upLocal ctx p t x) e))

and mem x = function
  | Var (y, _) -> x = y
  | VSig (t, (p, f)) | VPi (t, (p, f)) | VLam (t, (p, f)) ->
    mem x t || mem x (f (Var (p, t)))
  | VBot   | VKan _ | VHole
  | VN     | VZero  | VSucc
  | VZ     | VPos   | VNeg
  | VI     | VLeft  | VRight
  | VZSucc | VZPred -> false

  | VFst e   | VSnd e    | VNInd e
  | VZInd e  | VBotRec e | VCoe e
  | VPathP e | VPLam e   | VIso e -> mem x e

  | VPair (a, b) | VApp (a, b) | VAppFormula (a, b) -> mem x a || mem x b

(* Readback *)
let rec rbV v : exp = traceRbV v; match v with
  | VLam (t, g)           -> rbVTele eLam t g
  | VPair (u, v)          -> EPair (rbV u, rbV v)
  | VKan u                -> EKan u
  | VPi (t, g)            -> rbVTele ePi t g
  | VSig (t, g)           -> rbVTele eSig t g
  | Var (x, _)            -> EVar x
  | VApp (f, x)           -> EApp (rbV f, rbV x)
  | VFst k                -> EFst (rbV k)
  | VSnd k                -> ESnd (rbV k)
  | VHole                 -> EHole
  | VN                    -> EN
  | VZero                 -> EZero
  | VSucc                 -> ESucc
  | VNInd v               -> ENInd (rbV v)
  | VZ                    -> EZ
  | VPos                  -> EPos
  | VNeg                  -> ENeg
  | VZSucc                -> EZSucc
  | VZPred                -> EZPred
  | VZInd v               -> EZInd (rbV v)
  | VBot                  -> EBot
  | VBotRec v             -> EBotRec (rbV v)
  | VI                    -> EI
  | VLeft                 -> ELeft
  | VRight                -> ERight
  | VCoe v                -> ECoe (rbV v)
  | VPathP v              -> EPathP (rbV v)
  | VPLam v               -> EPLam (rbV v)
  | VAppFormula (f, x)    -> EAppFormula (rbV f, rbV x)
  | VIso v                -> EIso (rbV v)

and rbVTele ctor t (p, g) = let x = Var (p, t) in ctor p (rbV t) (rbV (g x))

