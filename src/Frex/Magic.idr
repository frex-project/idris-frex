module Frex.Magic

import public Control.Monad.State

import Data.Nat
import Data.Fin
import Data.Vect

import public Frex

import public Language.Reflection
import public Language.Reflection.Relation

%language ElabReflection

N : Name -> TTImp
N = IVar emptyFC

normalise : {0 as : Type} -> TTImp -> Elab TTImp
normalise {as} tm = quote !(check {expected = as} tm)

disambig : (Name -> Elab $ List (Name, t)) -> Name -> Elab t
disambig f n = forceUnambig !(f n)
  where forceUnambig : List (Name, t) -> Elab t
        forceUnambig [] = fail $ show n ++ " is undefined"
        forceUnambig [(_, tm)] = pure tm
        forceUnambig _ = fail $ show n ++ " is ambiguous"

unwrap : Maybe t -> Elab t
unwrap $ Just x = pure x
unwrap Nothing = fail "attempted to unwrap `Nothing`"

unapply : (n : Nat) -> TTImp -> Elab (TTImp, TTImp ^ n)
unapply Z tm = pure (tm, [])
unapply (S n) $ IApp _ tm x
  = do (tm, xs) <- unapply n tm
       pure $ (tm, x :: xs)
unapply n@(S _) tm
  = failAt (getFC tm) $ "could not unapply " ++ show n ++ " arguments"

unlambda : (n : Nat) -> TTImp -> Elab (TTImp, Name ^ n)
unlambda Z tm = pure (tm, [])
unlambda (S n) $ ILam _ _ _ x _ ret
  = do (tm, xs) <- unlambda n ret
       case x of 
            Just x => pure (tm, x :: xs)
            Nothing => pure (tm, !(genSym "x") :: xs)
unlambda n@(S _) tm 
  = failAt (getFC tm) $ "could not unlambda " ++ show n ++ " arguments"

record Operator where
  constructor MkOperator
  symbol : Name
  arity : Nat
  params : Name ^ arity
  sem : TTImp
  0 carrier : Type

public export
curry : {0 a : Type} -> {n : Nat} -> (a ^ n -> a) -> Elab TTImp
curry {a} {n} f
  = do curried <- currySyn n !(quote a) !(quote f)
       logSugaredTerm "magic" 2 "curried" curried
       pure curried
  where currySyn : Nat -> TTImp -> TTImp -> Elab TTImp
        currySyn Z a f = pure `(~(f) [])
        currySyn (S n) a f
          = do x <- genSym $ "x" ++ show n
               body <- currySyn n a `(~(f) . (~(N x) ::))
               pure $ ILam emptyFC MW ExplicitArg (Just x) a body

atomise : TTImp -> Elab Name
atomise (IVar _ n) = pure n
atomise t =
  failAt (getFC t) "expected term to reduce to a simple name"

Matches : Operator -> Type
Matches op = (Maybe TTImp) ^ op.arity

emptyMatches : {op : Operator} -> Matches op
emptyMatches {op} = replicate op.arity Nothing

Match : Operator -> Type -> Type
Match op = StateT (Matches op) Elab

findMatches : {op : Operator} -> TTImp -> TTImp -> Match op ()
findMatches {op} s@(IVar _ n) t
  = do case elemIndex n op.params of
          Just k => updateMatch k t
          Nothing => when (not $ metadataEq s t) $ failAt (getFC t) "mismatch"
  where updateMatch : Fin op.arity -> TTImp -> Match op ()
        updateMatch k t
          = do case index k !get of
                    Just t' => when (t /= t') $ failAt (getFC t') "mismatch"
                    _ => pure ()
               modify $ updateAt k (\_ => Just t)
findMatches s t
  = do when (not $ metadataEq s t) $ failAt (getFC t) "mismatch"
       sequence_
          $ map (\(x, y) => findMatches x y)
          $ zip (subexprs s) (subexprs t)

match : (op : Operator) -> TTImp -> Elab $ TTImp ^ op.arity
match op t
  = do matched <- execStateT emptyMatches (findMatches op.sem t)
       traverse unwrap matched

interface FoldSyntax a b where
  atom : (0 _ : Type) -> TTImp -> b -> (a, b)
  term : (op : Operator) -> a ^ (op.arity) -> a

findOp : TTImp
  -> List Operator
  -> Elab $ Maybe $ DPair Operator $ \op => TTImp ^ op.arity
findOp tm [] = pure Nothing
findOp tm $ op :: ops =
    try (do logSugaredTerm "magic" 1 "matching" tm
            args <- match op tm
            pure $ Just $ MkDPair op args)
        (findOp tm ops)

fold : FoldSyntax a b => (0 _ : Type)
  -> List Operator -> b -> TTImp -> Elab (a, b)
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

isOpen : (0 _ : Type) -> TTImp -> Elab Bool
isOpen _ $ IPrimVal _ _ = pure False
isOpen t $ IVar _ n
  = do info <- (disambig getInfo n) <|> (pure $ MkNameInfo Bound)
       checkNameInfo info
  where checkNameInfo : NameInfo -> Elab Bool
        checkNameInfo $ MkNameInfo Bound
          = do ty <- getLocalType n
               pure $ ty == !(quote t)
        checkNameInfo $ MkNameInfo Func = pure True
        checkNameInfo $ MkNameInfo _ = pure False
isOpen t $ IApp _ f x = pure $ !(isOpen t f) || !(isOpen t x)
isOpen _ _ = pure True

public export
insert : TTImp -> List TTImp -> List TTImp
insert t [] = [t]
insert t ctx@(x :: xs)
  = if x == t
       then ctx
       else x :: insert t xs

[findOpen] FoldSyntax () (Elab $ List TTImp) where
  atom t tm ctx = ((), update)
    where update : Elab $ List TTImp
          update = if !(isOpen t tm)
                      then pure $ insert tm !(ctx)
                      else ctx
  term _ _ = ()

[buildSyntax] FoldSyntax (Elab TTImp) (Vect n TTImp) where
  atom _ tm ctx = (aux, ctx)
    where aux : Elab TTImp
          aux = case findIndex (tm ==) ctx of 
                     Just n => do n <- quote n
                                  pure `(Dyn ~(n))
                     Nothing => pure `(Sta ~(tm))
  term op args = pure `(Call (MkOp ~(N $ op.symbol)) ~(!(aux args)))
    where aux : {n : Nat} -> (Elab TTImp) ^ n -> Elab TTImp
          aux {n = 0} [] = pure `([])
          aux {n = S n} $ x :: xs = pure `(~(!x) :: ~(!(aux xs)))

extractOps : {pres : Presentation}
  -> (a : Model pres)
  -> Elab (List Operator)
extractOps {pres} a
  = do let MkSignature ops = pres.signature
       ops <- quote ops
       opT <- atomise ops
       constructors <- getCons opT
       traverse extractOp constructors
  where extractOp : Name -> Elab Operator
        extractOp symbol
          = do op <- check {expected = Op pres.signature} `(MkOp ~(N symbol))
               let n = op.fst
               sem <- Magic.curry {a = a.Algebra.algebra.U}
                  $ a.Algebra.algebra.Semantics op
               sem <- normalise {as = n `ary` a.Algebra.algebra.U} sem
               (sem, bound) <- unlambda n sem
               logSugaredTerm "magic" 1 "op" $ N symbol
               logSugaredTerm "magic" 1 "sem" sem
               pure $ MkOperator symbol n bound sem $ a.Algebra.algebra.U

extractGoal : (0 _ : Type) -> Elab (TTImp, TTImp)
extractGoal ty
  = do Just goal <- goal
          | _ => fail "couldn't find goal"
       (_, [rhs, lhs]) <- unapply 2 goal
       lhs <- normalise {as = ty} lhs
       rhs <- normalise {as = ty} rhs
       logSugaredTerm "magic" 1 "lhs" lhs
       logSugaredTerm "magic" 1 "rhs" rhs
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
       env <- env

       traverse_ (logSugaredTerm "magic" 1 "env") env

       let env = fromList env
       let n = length env

       (lhs, _) <- fold @{buildSyntax} () ops env lhs
       (rhs, _) <- fold @{buildSyntax} () ops env rhs

       lhs <- lhs
       rhs <- rhs
       let eq = `(MkPair ~(lhs) ~(rhs))

       logSugaredTerm "magic" 1 "eq" eq

       env <- reifyEnv (U a) env
       env <- quote env

       let frex = frex a {n}

       pres <- quote pres
       a <- quote a
       frex <- quote frex

       check `(Frex.solveVect
                {pres = ~(pres)} {a = ~(a)}
                ~(frex) ~(env) ~(eq))
