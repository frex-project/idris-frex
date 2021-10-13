import Data.Bool

import Language.Reflection

public export
Eq LazyReason where
  LInf     == LInf     = True
  LLazy    == LLazy    = True
  LUnknown == LUnknown = True
  _ == _ = False

public export
Eq Namespace where
  MkNS ns == MkNS ns' = ns == ns'

public export
Eq Count where
  M0 == M0 = True
  M1 == M1 = True
  MW == MW = True
  _  == _  = False

public export
Eq BindMode where
  PI c    == PI c'   = c == c'
  PATTERN == PATTERN = True
  NONE    == NONE    = True
  _ == _ = False

public export
Eq UseSide where
  UseLeft  == UseLeft  = True
  UseRight == UseRight = True
  _ == _ = False

public export
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
Eq WithFlag where
  Syntactic == Syntactic = True

public export
Eq UserName where
  Basic n    == Basic n'   = n == n'
  Field n    == Field n'   = n == n'
  Underscore == Underscore = True
  _ == _ = False

public export
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
  Eq (PiInfo TTImp) where
    ImplicitArg   == ImplicitArg = True
    ExplicitArg   == ExplicitArg = True
    AutoImplicit  == AutoImplicit = True
    DefImplicit t == DefImplicit t' = t == t'
    _ == _ = False

  public export
  Eq Clause where
    PatClause _ lhs rhs == PatClause _ lhs' rhs' =
      lhs == lhs' && rhs == rhs'
    WithClause _ l w p f cs == WithClause _ l' w' p' f' cs' =
      l == l' && w == w' && p == p' && f == f' && cs == cs'
    ImpossibleClause _ l == ImpossibleClause _ l' = l == l' 
    _ == _ = False

  public export
  Eq IFieldUpdate where
    ISetField p t == ISetField p' t' =
      p == p' && t == t'
    ISetFieldApp p t == ISetFieldApp p' t' =
      p == p' && t == t'
    _ == _ = False

  public export
  Eq AltType where
    FirstSuccess    == FirstSuccess     = True
    Unique          == Unique           = True
    UniqueDefault t == UniqueDefault t' = t == t'
    _ == _ = False

  public export
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
