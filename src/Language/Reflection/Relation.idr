module Language.Reflection.Relation

import Data.Bool

import Language.Reflection

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
        subclause $ WithClause _ l _ r _ _ cs = [l, r] ++ foldMap subclause cs
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
