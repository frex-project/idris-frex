module Language.Reflection.Relation

import Data.Bool

import Language.Reflection

public export
partial
Eq LazyReason where
  LInf     == LInf     = True
  LLazy    == LLazy    = True
  LUnknown == LUnknown = True
  _ == _ = False

public export
partial
Eq Namespace where
  MkNS ns == MkNS ns' = ns == ns'

public export
partial
Eq Count where
  M0 == M0 = True
  M1 == M1 = True
  MW == MW = True
  _  == _  = False

public export
partial
Eq BindMode where
  PI c    == PI c'   = c == c'
  PATTERN == PATTERN = True
  NONE    == NONE    = True
  _ == _ = False

public export
partial
Eq UseSide where
  UseLeft  == UseLeft  = True
  UseRight == UseRight = True
  _ == _ = False

public export
partial
Eq DotReason where
  NonLinearVar    == NonLinearVar    = True
  VarApplied      == VarApplied      = True
  NotConstructor  == NotConstructor  = True
  ErasedArg       == ErasedArg       = True
  UserDotted      == UserDotted      = True
  UnknownDot      == UnknownDot      = True
  UnderAppliedCon == UnderAppliedCon = True
  _ == _ = False

public export
partial
Eq WithFlag where
  Syntactic == Syntactic = True

public export
partial
Eq UserName where
  Basic n    == Basic n'   = n == n'
  Field n    == Field n'   = n == n'
  Underscore == Underscore = True
  _ == _ = False

public export
partial
Eq Name where
  NS ns n        == NS ns' n'       = ns == ns' && n == n'
  UN n           == UN n'           = n == n'
  MN n i         == MN n' i'        = n == n' && i == i'
  DN _ n         == DN _ n'         = n == n'
  Nested i n     == Nested i' n'    = i == i' && n == n'
  CaseBlock n i  == CaseBlock n' i' = n == n' && i == i'
  WithBlock n i  == WithBlock n' i' = n == n' && i == i'
  _ == _ = False

public export
partial
Eq Constant where
  I c         == I c'        = c == c'
  BI c        == BI c'       = c == c'
  I8 c        == I8 c'       = c == c'
  I16 c       == I16 c'      = c == c'
  I32 c       == I32 c'      = c == c'
  I64 c       == I64 c'      = c == c'
  B8 c        == B8 c'       = c == c'
  B16 c       == B16 c'      = c == c'
  B32 c       == B32 c'      = c == c'
  B64 c       == B64 c'      = c == c'
  Str c       == Str c'      = c == c'
  Ch c        == Ch c'       = c == c'
  Db c        == Db c'       = c == c'
  WorldVal    == WorldVal    = True
  IntType     == IntType     = True
  IntegerType == IntegerType = True
  Int8Type    == Int8Type    = True
  Int16Type   == Int16Type   = True
  Int32Type   == Int32Type   = True
  Int64Type   == Int64Type   = True
  Bits8Type   == Bits8Type   = True
  Bits16Type  == Bits16Type  = True
  Bits32Type  == Bits32Type  = True
  Bits64Type  == Bits64Type  = True
  StringType  == StringType  = True
  CharType    == CharType    = True
  DoubleType  == DoubleType  = True
  WorldType   == WorldType   = True
  _ == _ = False

mutual
  public export
  partial
  Eq (PiInfo TTImp) where
    ImplicitArg   == ImplicitArg = True
    ExplicitArg   == ExplicitArg = True
    AutoImplicit  == AutoImplicit = True
    DefImplicit t == DefImplicit t' = t == t'
    _ == _ = False

  public export
  partial
  Eq Clause where
    PatClause _ lhs rhs == PatClause _ lhs' rhs' =
      lhs == lhs' && rhs == rhs'
    WithClause _ l w p f cs == WithClause _ l' w' p' f' cs' =
      l == l' && w == w' && p == p' && f == f' && cs == cs'
    ImpossibleClause _ l == ImpossibleClause _ l' = l == l' 
    _ == _ = False

  public export
  partial
  Eq IFieldUpdate where
    ISetField p t == ISetField p' t' =
      p == p' && t == t'
    ISetFieldApp p t == ISetFieldApp p' t' =
      p == p' && t == t'
    _ == _ = False

  public export
  partial
  Eq AltType where
    FirstSuccess    == FirstSuccess     = True
    Unique          == Unique           = True
    UniqueDefault t == UniqueDefault t' = t == t'
    _ == _ = False

  public export
  partial
  Eq TTImp where
    IVar _ v == IVar _ v' = v == v'
    IPi _ c i n a r == IPi _ c' i' n' a' r' =
      c == c' && i == i' && n == n' && a == a' && r == r'
    ILam _ c i n a r == ILam _ c' i' n' a' r' =
      c == c' && i == i' && n == n' && a == a' && r == r'
    ILet _ _ c n ty val s == ILet _ _ c' n' ty' val' s' =
      c == c' && n == n' && ty == ty' && val == val' && s == s'
    ICase _ t ty cs == ICase _ t' ty' cs'
      = t == t' && ty == ty' && cs == cs'
    IUpdate _ fs t == IUpdate _ fs' t' =
      fs == fs' && t == t'

    IApp _ f x == IApp _ f' x' = f == f' && x == x'
    INamedApp _ f n x == INamedApp _ f' n' x' =
      f == f' && n == n' && x == x'
    IAutoApp _ f x == IAutoApp _ f' x' = f == f' && x == x'
    IWithApp _ f x == IWithApp _ f' x' = f == f' && x == x'

    ISearch _ n == ISearch _ n' = n == n'
    IAlternative _ t as == IAlternative _ t' as' =
      t == t' && as == as'
    IRewrite _ p q == IRewrite _ p' q' =
      p == p' && q == q'

    IBindHere _ m t == IBindHere _ m' t' =
      m == m' && t == t'
    IBindVar _ s == IBindVar _ s' = s == s'
    IAs _ _ u n t == IAs _ _ u' n' t' =
      u == u' && n == n' && t == t'
    IMustUnify _ r t == IMustUnify _ r' t' =
      r == r' && t == t'

    IDelayed _ r t == IDelayed _ r' t' = r == r' && t == t'
    IDelay _ t == IDelay _ t' = t == t'
    IForce _ t == IForce _ t' = t == t'

    IQuote _ tm == IQuote _ tm' = tm == tm'
    IQuoteName _ n == IQuoteName _ n' = n == n'
    IUnquote _ tm == IUnquote _ tm' = tm == tm'

    IPrimVal _ c == IPrimVal _ c' = c == c'
    IType _ == IType _ = True
    IHole _ s == IHole _ s' = s == s'

    Implicit _ b == Implicit _ b' = b == b'
    IWithUnambigNames _ ns t == IWithUnambigNames _ ns' t' =
      ns == ns' && t == t' 

    _ == _ = False

Metadata : TTImp -> Type
Metadata $ IVar _ _ = Name
Metadata $ IPi _ _ _ _ _ _ = (Count, PiInfo TTImp, Maybe Name)
Metadata $ ILam _ _ _ _ _ _ = (Count, PiInfo TTImp, Maybe Name)
Metadata $ ILet _ _ _ _ _ _ _ = (Count, Name)
Metadata $ INamedApp _ _ _ _ = Name
Metadata $ ISearch _ _ = Nat
Metadata $ IAlternative _ _ _ = AltType
Metadata $ IBindHere _ _ _ = BindMode
Metadata $ IBindVar _ _ = String
Metadata $ IAs _ _ _ _ _ = (UseSide, Name)
Metadata $ IMustUnify _ _ _ = DotReason
Metadata $ IDelayed _ _ _ = LazyReason
Metadata $ IQuoteName _ _ = Name
Metadata $ IPrimVal _ _ = Constant
Metadata $ IHole _ _ = String
Metadata $ Implicit _ _ = Bool
Metadata $ _ = ()

metadata : (t : TTImp) -> Metadata t
metadata $ IVar _ n = n
metadata $ IPi _ c i n _ _ = (c, i, n)
metadata $ ILam _ c i n _ _ = (c, i, n)
metadata $ ILet _ _ c n _ _ _ = (c, n)
metadata $ INamedApp _ _ n _ = n
metadata $ ISearch _ d = d
metadata $ IAlternative _ t _ = t
metadata $ IBindHere _ m _ = m
metadata $ IBindVar _ v = v
metadata $ IAs _ _ u n _ = (u, n)
metadata $ IMustUnify _ r _ = r
metadata $ IDelayed _ r _ = r
metadata $ IQuoteName _ n = n
metadata $ IPrimVal _ c = c
metadata $ IHole _ h = h
metadata $ Implicit _ b = b
metadata $ _ = believe_me ()

public export
metadataEq : TTImp -> TTImp -> Bool
metadataEq s@(IVar _ _) t@(IVar _ _) = metadata s == metadata t
metadataEq s@(IPi _ _ _ _ _ _) t@(IPi _ _ _ _ _ _) = metadata s == metadata t
metadataEq s@(ILam _ _ _ _ _ _) t@(ILam _ _ _ _ _ _) = metadata s == metadata t
metadataEq s@(ILet _ _ _ _ _ _ _) t@(ILet _ _ _ _ _ _ _) = metadata s == metadata t
metadataEq s@(ICase _ _ _ _) t@(ICase _ _ _ _) = metadata s == metadata t
metadataEq s@(ILocal _ _ _) t@(ILocal _ _ _) = metadata s == metadata t
metadataEq s@(IUpdate _ _ _) t@(IUpdate _ _ _) = metadata s == metadata t
metadataEq s@(IApp _ _ _) t@(IApp _ _ _) = metadata s == metadata t
metadataEq s@(INamedApp _ _ _ _) t@(INamedApp _ _ _ _) = metadata s == metadata t
metadataEq s@(IAutoApp _ _ _) t@(IAutoApp _ _ _) = metadata s == metadata t
metadataEq s@(IWithApp _ _ _) t@(IWithApp _ _ _) = metadata s == metadata t
metadataEq s@(ISearch _ _) t@(ISearch _ _) = metadata s == metadata t
metadataEq s@(IAlternative _ _ _) t@(IAlternative _ _ _) = metadata s == metadata t
metadataEq s@(IRewrite _ _ _) t@(IRewrite _ _ _) = metadata s == metadata t
metadataEq s@(IBindHere _ _ _) t@(IBindHere _ _ _) = metadata s == metadata t
metadataEq s@(IBindVar _ _) t@(IBindVar _ _) = metadata s == metadata t
metadataEq s@(IAs _ _ _ _ _) t@(IAs _ _ _ _ _) = metadata s == metadata t
metadataEq s@(IMustUnify _ _ _) t@(IMustUnify _ _ _) = metadata s == metadata t
metadataEq s@(IDelayed _ _ _) t@(IDelayed _ _ _) = metadata s == metadata t
metadataEq s@(IDelay _ _) t@(IDelay _ _) = metadata s == metadata t
metadataEq s@(IForce _ _) t@(IForce _ _) = metadata s == metadata t
metadataEq s@(IQuote _ _) t@(IQuote _ _) = metadata s == metadata t
metadataEq s@(IQuoteName _ _) t@(IQuoteName _ _) = metadata s == metadata t
metadataEq s@(IQuoteDecl _ _) t@(IQuoteDecl _ _) = metadata s == metadata t
metadataEq s@(IUnquote _ _) t@(IUnquote _ _) = metadata s == metadata t
metadataEq s@(IPrimVal _ _) t@(IPrimVal _ _) = metadata s == metadata t
metadataEq s@(IType _) t@(IType _) = metadata s == metadata t
metadataEq s@(IHole _ _) t@(IHole _ _) = metadata s == metadata t
metadataEq s@(Implicit _ _) t@(Implicit _ _) = metadata s == metadata t
metadataEq s@(IWithUnambigNames _ _ _) t@(IWithUnambigNames _ _ _) = metadata s == metadata t
metadataEq _ _ = False

public export
subexprs : TTImp -> List TTImp
subexprs $ IPi _ _ _ _ a r = [a, r]
subexprs $ ILam _ _ _ _ a r = [a, r]
subexprs $ ILet _ _ _ _ t v s = [t, v, s]
subexprs $ ICase _ x t cs = [x, t] ++ foldMap subclause cs
  where subclause : Clause -> List TTImp
        subclause $ PatClause _ l r = [l, r]
        subclause $ WithClause _ l r _ _ cs = [l, r] ++ foldMap subclause cs
        subclause $ ImpossibleClause _ l = [l]
subexprs $ ILocal _ _ e = [e]
subexprs $ IUpdate _ _ _ = [] -- TODO
subexprs $ IApp _ f x = [f, x]
subexprs $ INamedApp _ f _ x = [f, x]
subexprs $ IAutoApp _ f x = [f, x]
subexprs $ IWithApp _ f x = [f, x]
subexprs $ IAlternative _ _ xs = xs
subexprs $ IRewrite _ x y = [x, y]
subexprs $ IBindHere _ _ x = [x]
subexprs $ IAs _ _ _ _ x = [x]
subexprs $ IMustUnify _ _ x = [x]
subexprs $ IDelayed _ _ x = [x]
subexprs $ IDelay _ x = [x]
subexprs $ IForce _ x = [x]
subexprs $ IQuote _ x = [x]
subexprs $ IUnquote _ x = [x]
subexprs $ IWithUnambigNames _ _ x = [x]
subexprs _ = []
