module Frex.Magic

import Data.Nat
import Data.Fin
import Data.Vect

import public Language.Reflection
import public Language.Reflection.Relation

import Frex

%language ElabReflection

N : Name -> TTImp
N = IVar emptyFC

normalise : {0 as : Type} -> TTImp -> Elab TTImp
normalise {as} tm
  = do tm' <- check {expected = as} tm
       quote tm'

getTypeUnambig : Name -> Elab TTImp
getTypeUnambig n
  = do ts <- getType n
       forceUnambig ts
  where forceUnambig : List (Name, TTImp) -> Elab TTImp
        forceUnambig [] = fail $ (show n) ++ " is undefined"
        forceUnambig [(_, tm)] = pure tm
        forceUnambig _ = fail $ (show n) ++ "is ambiguous"

record OpSyn where
  constructor MkOpSyn
  name : Name
  arity : Nat
  sem : TTImp
  0 carrier : Type

squash : List (Elab a) -> Elab (List a)
squash [] = pure []
squash $ x :: xs
  = do x <- x
       xs <- squash xs
       pure $ x :: xs

public export
curry : {n : Nat} -> (a ^ n -> a) -> n `ary` a
curry {n = 0}     f = f []
curry {n = (S n)} f = \x => Magic.curry (f . (x ::))

unapply : (n : Nat) -> TTImp -> Elab (TTImp, TTImp ^ n)
unapply Z tm = pure (tm, [])
unapply (S n) $ IApp _ tm x
  = do (tm, xs) <- unapply n tm
       pure $ (tm, x :: xs)
unapply n@(S _) tm
  = failAt (getFC tm) $ "could not unapply " ++ show n ++ " arguments"

unlambda : (n : Nat) -> TTImp -> Elab TTImp
unlambda Z tm = pure tm
unlambda (S n) $ ILam _ _ _ _ _ ret = unlambda n ret
unlambda n@(S _) tm
  = failAt (getFC tm) $ "could not unlambda " ++ show n ++ " arguments"

eta : (n : Nat) -> TTImp -> Elab TTImp
eta n tm = do tm <- unlambda n tm
              (tm, _) <- unapply n tm
              pure tm

forceAtom : TTImp -> Elab Name
forceAtom (IVar _ n) = pure n
forceAtom t =
  failAt (getFC t) "expected term to reduce to a simple name"

matchPrefix : TTImp -> (op : OpSyn) -> Elab $ TTImp ^ op .arity
matchPrefix tm op
  = do (tm, args) <- unapply (op .arity) tm
       if op .sem == tm
          then pure $ reverse args
          else failAt (getFC tm) "failed to match prefix"

interface FoldSyn a b where
  atom : (0 _ : Type) -> TTImp -> b -> (a, b)
  term : (op : OpSyn) -> a ^ (op .arity) -> a

findOp : TTImp
  -> List OpSyn
  -> Elab $ Maybe $ DPair OpSyn $ \op => TTImp ^ op .arity
findOp tm [] = pure Nothing
findOp tm $ op :: ops =
    try (do args <- matchPrefix tm op
            pure $ Just $ MkDPair op args)
        (findOp tm ops)

fold : FoldSyn a b => (0 _ : Type) -> List OpSyn -> b -> TTImp -> Elab (a, b)
fold @{folder} t ops init tm = foldAcc tm $ init
  where mutual
    foldArgs : Vect n TTImp -> b -> Elab (a ^ n, b)
    foldArgs [] acc = pure ([], acc)
    foldArgs (x :: xs) acc
      = do (x , acc) <- foldAcc x acc
           (xs , acc) <- foldArgs xs acc
           pure (x :: xs, acc)

    foldAcc : TTImp -> b -> Elab (a, b)
    foldAcc tm acc
      = do Just $ MkDPair op args <- findOp tm ops
              | _ => pure $ atom t tm acc
           (args, acc) <- foldArgs args acc
           pure (term @{folder} op args, acc)

[countLeaves] FoldSyn Nat () where
  atom _ _ acc = (1, acc)
  term _ xs = sum xs

-- TODO
isOpen : (0 _ : Type) -> TTImp -> Elab Bool
isOpen _ $ IPrimVal _ _ = pure False
isOpen t $ IVar _ n
  = do ty <- forceAtom !(quote t)
       cons <- getCons ty
       pure $ not $ any (n ==) cons
isOpen t $ IApp _ f x = pure $ !(isOpen t f) || !(isOpen t x)
isOpen _ _ = pure True

public export
insert : TTImp -> List TTImp -> List TTImp
insert t [] = [t]
insert t ctx@(x :: xs)
  = if x == t
       then ctx
       else x :: insert t xs

[findOpen] FoldSyn () (Elab $ List TTImp) where
  atom t tm ctx = ((), update)
    where update : Elab $ List TTImp
          update
            = if !(isOpen t tm)
                 then pure $ insert tm !(ctx)
                 else ctx
  term _ _ = ()

[buildSyntax] FoldSyn (Elab TTImp) (Vect n TTImp) where
  atom _ tm ctx = (aux, ctx)
    where aux : Elab TTImp
          aux = case findIndex (tm ==) ctx of 
                     Just n => do n <- quote n
                                  pure `(Dyn ~(n))
                     Nothing => pure `(Sta ~(tm))
  term op args = pure `(Call (MkOp ~(N $ op .name)) ~(!(aux args)))
    where aux : {n : Nat} -> (Elab TTImp) ^ n -> Elab TTImp
          aux {n = 0} [] = pure `([])
          aux {n = S n} $ x :: xs = pure `(~(!x) :: ~(!(aux xs)))

extractOps : {pres : Presentation}
  -> (a : Model pres)
  -> Elab (List OpSyn)
extractOps {pres} a
  = do let MkSignature ops = pres.signature
       ops <- quote ops
       opT <- forceAtom ops
       constructors <- getCons opT
       squash $ map extractOp constructors
  where extractOp : Name -> Elab OpSyn
        extractOp syn
          = do op <- check {expected = Op pres.signature} `(MkOp ~(N syn))
               let n = op.fst
               let sem = Magic.curry {a = U a} $ a.Sem op
               sem <- normalise {as = n `ary` U a} !(quote sem)
               sem <- eta n sem
               logTerm "magic" 2 "op" $ N syn
               logTerm "magic" 2 "sem" sem
               pure $ MkOpSyn syn n sem $ U a

extractGoal : (0 _ : Type) -> Elab (TTImp, TTImp)
extractGoal ty
  = do Just goal <- goal
          | _ => fail "couldn't find goal"
       (_, [rhs, lhs]) <- unapply 2 goal
       lhs <- normalise {as = ty} lhs
       rhs <- normalise {as = ty} rhs
       logTerm "magic" 2 "lhs" lhs
       logTerm "magic" 2 "rhs" rhs
       pure (lhs, rhs)

reifyEnv : (0 t : Type) -> TTImp ^ n -> Elab $ t ^ n
reifyEnv {n = 0} t [] = pure []
reifyEnv {n = S n} t $ x :: xs
  = pure $ !(check {expected = t} x) :: !(reifyEnv t xs)

public export
frexMagic : {t : Type}
  -> {pres : Presentation}
  -> Frexlet {pres = pres}
  -> Model pres
  -> Elab t
frexMagic {pres = pres} frex a
  = do ops <- extractOps a
       (lhs, rhs) <- extractGoal $ U a
       (_, env) <- fold @{findOpen} (U a) ops (pure []) lhs
       (_, env) <- fold @{findOpen} (U a) ops env rhs

       let env = fromList !(env)
       let n = length env

       (lhs, _) <- fold @{buildSyntax} () ops env lhs
       (rhs, _) <- fold @{buildSyntax} () ops env rhs

       lhs <- lhs
       rhs <- rhs
       let eq = `(MkPair ~(lhs) ~(rhs))

       logSugaredTerm "magic" 2 "eq" eq

       env <- reifyEnv (U a) env
       env <- quote env

       let frex = frex a {n}

       pres <- quote pres
       a <- quote a
       frex <- quote frex

       check `(Frex.solveVect
                {pres = ~(pres)} {a = ~(a)}
                ~(frex) ~(env) ~(eq))
