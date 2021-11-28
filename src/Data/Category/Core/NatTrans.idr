module Data.Category.Core.NatTrans

import Data.Category.Core.Category
import Data.Category.Core.Functor

import Data.Setoid.Fun

public export 0
Transformation : {c,d : Category} -> (f,g : c ~> d) -> Type
Transformation f g = (a : c.Obj) -> d.Hom (f !! a) (g !! a)

public export 0
Naturality : {c, d : Category} -> {f,g : c ~> d} -> (alpha : Transformation f g) -> Type
Naturality alpha = {a,b : c.Obj} -> (u : c.Hom a b) ->
  (d.HomSet _ _).equivalence.relation
    (alpha b . f.map u)
    (g.map u . alpha a)

public export
record (~>) {C,D : Category} (F, G : C ~> D) where
  constructor MkNatTrans
  transformation : Transformation F G
  naturality : Naturality {f = F, g = G} transformation

infix 8 ^

public export
(^) : {C, D : Category} -> {F, G : C ~> D} -> F ~> G -> Transformation F G
(^) = (.transformation)

public export
Id : {c, d : Category} -> {f : c ~> d} -> f ~> f
Id = MkNatTrans
  { transformation = \a => Id
  , naturality = \u => CalcWith (d.HomSet _ _) $
    |~ (Id . f.map u)
    ~~ f.map u        ...(d.laws.idLftNeutral _)
    ~~ (f.map u . Id) ..<(d.laws.idRgtNeutral _)
  }

public export
(.) : {c, d : Category} -> {f,g,h : c ~> d} -> g ~> h -> f ~> g -> f ~> h
(.) alpha beta = MkNatTrans
  { transformation = \a => (alpha ^ a) . (beta ^ a)
  , naturality = \ u => CalcWith (d.HomSet _ _) $
    |~ ((alpha ^ _) . ( beta ^ _)) . f.map u
    ~~ ( alpha ^ _) . ((beta ^ _)  . f.map u)  ..<(d.laws.associativity _ _ _)
    ~~ ( alpha ^ _) . ((g.map u) . (beta ^ _)) ...(d.cong (_,_) (_,_) $
                                                   MkAnd
                                                     ((d.HomSet _ _).equivalence.reflexive _)
                                                     $ beta.naturality u)
    ~~ ((alpha ^ _) . (g.map u)) . (beta ^ _)  ...(d.laws.associativity _ _ _)
    ~~ (h.map u . ( alpha ^ _)) . (beta ^ _)   ...(d.cong (_,_) (_,_) $
                                                   MkAnd
                                                     (alpha.naturality u)
                                                     $ (d.HomSet _ _).equivalence.reflexive _)
    ~~ (h.map u . ((alpha ^ _) . ( beta ^ _))) ..<(d.laws.associativity _ _ _)
  }

public export 0
NatTransEq : {c,d : Category} -> (f,g : c ~> d) -> Rel (f ~> g)
NatTransEq f g alpha beta = (a : c.Obj) -> (d.HomSet _ _).equivalence.relation
                     (alpha ^ a) (beta ^ a)

public export
(~~>) : {c,d : Category} -> (f,g : c ~> d) -> Setoid
f ~~> g = MkSetoid
  { U = f ~> g
    -- Might be easier had we showed Setoids have dependent products
    -- but we haven't yet, so we'll just do it directly
  , equivalence = MkEquivalence
      { relation = NatTransEq f g
      , reflexive = \alpha,a => (d.HomSet _ _).equivalence.reflexive _
      , symmetric = \alpha,beta,prf,a => (d.HomSet _ _).equivalence.symmetric _ _ $
                    prf a
      , transitive = \alpha,beta,gamma,a_eq_b,b_eq_c,a =>
                     (d.HomSet _ _).equivalence.transitive _ _ _
                     (a_eq_b a) (b_eq_c a)
      }
  }

public export
compose : {c,d : Category} -> {f,g,h : c ~> d} ->
  (g ~~> h `Pair` f ~~> g) ~> (f ~~> h)
compose = MkSetoidHomomorphism
  { H = uncurry (.)
  , homomorphic = \(alpha1, beta1),(alpha2,beta2),prf,a =>
      d.cong (alpha1 ^ a , beta1 ^ a) (alpha2 ^ a , beta2 ^ a) $
      MkAnd (prf.fst a) (prf.snd a)
  }

public export
Functor : (c,d : Category) -> Category
Functor c d = MkCategory
  { Obj = c ~> d
  , structure = MkStructure
      { Arr = (~~>)
      , idArr = Id
      , compArr = compose
      }
  , laws = Check
      { idRgtNeutral = \alpha => MkHomEq $ \a => d.laws.idRgtNeutral _
      , idLftNeutral = \alpha => MkHomEq $ \a => d.laws.idLftNeutral _
      , associativity = \alpha,beta,gamma => MkHomEq $ \a => d.laws.associativity _ _ _
      }
  }

||| Horizontal composition of natural transformations
public export
(*) : {b,c,d : Category} -> {f1,f2 : c ~> d} -> {g1,g2 : b ~> c} ->
      f1 ~> f2 -> g1 ~> g2 -> (f1 . g1) ~> (f2 . g2)
alpha * beta = MkNatTrans
  { transformation = \a => (alpha ^ (g2 !! a)) . f1.map (beta ^ a)
  , naturality = \u => CalcWith (d.HomSet _ _) $
      {-           /----(alpha * beta ^ x)-----v
            f1 g1 x      def                 f2 g2 x
              |   `--------> f1 g2 x ----------^|
              | f1.functoriality|               |
              |  (beta.nat)     |  alpha.nat    |
              |                 v               |
              v  /--------->  f1 g2 y --------v v
            f1 g1 y           def           f2 g2 y
                 `-----------------------------^
      -}
       |~ ((alpha ^ (g2 !! _)) . f1.map (beta ^ _)) . (f1.map (g1.map u))
       ~~ (alpha ^ (g2 !! _)) . (f1.map (beta ^ _)) . (f1.map (g1.map u))
                          ..<(d.laws.associativity _ _ _)
       ~~ (alpha ^ (g2 !! _)) . (f1.map (g2.map u)) . (f1.map (beta ^ _))
                          ...(_ . (f1.byFunctoriality
                                [_ , _] [_ , _]
                                $ beta.naturality u))
       ~~ ((alpha ^ (g2 !! _)) . (f1.map (g2.map u))) . (f1.map (beta ^ _))
                          ...(d.laws.associativity _ _ _)
       ~~ ((f2.map (g2.map u)) . (alpha ^ (g2 !! _))) . (f1.map (beta ^ _))
                          ...(alpha.naturality _ . _)
       ~~ (f2.map (g2.map u)) . ((alpha ^ (g2 !! _)) . (f1.map (beta ^ _)))
                          ..<(d.laws.associativity _ _ _)
  }

public export
ComponentwiseIso : {c,d : Category} -> {f,g : c ~> d} ->
  (alpha : f ~> g) -> ((a : c.Obj) -> d.Invertible (alpha ^ a)) ->
  (Functor c d).Invertible $ MkHom alpha
ComponentwiseIso alpha inverses =
  let beta : Transformation g f
      beta a = (inverses a).inverse
  in IsInvertible
  { inverse = MkHom $ MkNatTrans
    { transformation = \a => (inverses a).inverse
      {-             beta a
            -----------------------------
           /        isInverse            v
         g a = ga <--------------------- f a
          |    |       alpha ^ a        /|
          | id |                       / |
     g u  |   /  g u  (alpha.nat) f u /  | f u
          |  /                       /id |
          v v        alpha ^ b      v    v
         g b <--------------------f b = f b
           \        isInverse            ^
            ------------------------------
                     beta b
      -}
    , naturality = \u => CalcWith (d.HomSet _ _) $
      |~ (beta _) . (g.map u)
      ~~ (beta _) . (g.map u . Id)   ..<(_ . d.laws.idRgtNeutral _)
      ~~ (beta _) . (g.map u . ((alpha ^ _) . (beta _)))
                                     ..<(_ . (_ . (inverses _).isInverse.IntoFromId))
      ~~ (beta _) . ((g.map u . (alpha ^ _)) . (beta _))
                                     ...(_ . d.laws.associativity _ _ _)
      ~~ (beta _) . (((alpha ^ _) . (f.map u)) . (beta _))
                                     ..<(_ . (alpha.naturality _ . _))
      ~~ ((beta _) . ((alpha ^ _) . (f.map u))) . (beta _)
                                     ...(d.laws.associativity
                                           (beta _)
                                           ((alpha ^ _) . (f.map u))
                                           (beta _))
      ~~ (((beta _) . (alpha ^ _)) . (f.map u)) . (beta _)
                                     ...(d.laws.associativity _ _ _ . _)
      ~~ (Id . (f.map u)) . (beta _) ...(((inverses _).isInverse.FromIntoId . _)
                                          . _)
      ~~ (f.map u) . (beta _) ...(d.laws.idLftNeutral _ . _)
    }
  , isInverse = MutuallyInverse
    { IntoFromId = MkHomEq $ \a => (inverses a).isInverse.IntoFromId
    , FromIntoId = MkHomEq $ \a => (inverses a).isInverse.FromIntoId
    }
  }
