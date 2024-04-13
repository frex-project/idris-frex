||| The 'minimal amount of data' for an adjunction is a choice of
||| universal arrow from every object to the candidate right adjoint
module Data.Category.Adjunction.Universal

import Data.Category
import Data.Category.Adjunction
import Data.Category.Colimit.Universal

%ambiguity_depth 5

parameters {B,C : Category} (G : B ~> C) (univ : (x : C .Obj) -> x `Universal` G)
  public export
  Farr : (x : C .Obj) -> x `Arrow` G
  Farr x = (univ x).Data

  public export
  Fobj : C .Obj -> B .Obj
  Fobj x = (Farr x).Cod

  public export
  Unit : (x : C .Obj) -> C .Hom x (G !! Fobj x)
  Unit x = (Farr x).Arr

  public export
  phiMor : {x : C .Obj} -> {b : B .Obj} -> (u : C .Hom x (G !! b)) ->
    Farr x ~> MkArrow {Cod = b, Arr = u}
  phiMor {x,b} u = U $ (univ x).UP.exists (MkArrow {Cod = b,  Arr = u})

  public export
  phi : {x : C .Obj} -> {b : B .Obj} -> C .Hom x (G !! b) -> B .Hom (Fobj x) b
  phi {x,b} u = (phiMor u).H

  public export
  phiCong : {x : C .Obj} -> {b : B .Obj} ->
    SetoidHomomorphism (C .HomSet x (G !! b)) (B .HomSet (Fobj x) b) (phi {x,b})
  phiCong {x,b} u v prf =
    {- The 'secret sauce' is that we have an Arrow-morphism xi : (b,u) -> (b,v):
          -- u ---> G !! b
         /  (prf)     |
       x     =        | G Id =: G xi
         \            v
          -- v ---> G !! b
       Therefore, we can form the composite Arr-morphism
         xi . phi u : (univ x).Data -> (b, v)
       so that we have two morphism:

         (univ x).Data -- exists (b,u) ---> (b,u)
            \                                  | xi
             \                                 v
              ----------- exists (b,v) ---> (b,v)

       By initiality, they are equal. The resulting proof is:

          Fobj x -- phi u --> b
            \                 | Id
             \                v
              ----- phi v --> b
       which we may use to conclude the proof
    -}
    let Arr_u, Arr_v : x `Arrow` G
        Arr_u = MkArrow {Cod = b, Arr = u}
        Arr_v = MkArrow {Cod = b, Arr = v}
        xi : Arr_u ~> Arr_v
        xi = MkHomo
          { H = Id
          , preserves = CalcWith (C .HomSet _ _) $
            |~ G .map Id . u
            ~~ Id . u ...(G .functoriality.id _ . u)
            ~~ u      ...(C .laws.idLftNeutral _)
            ~~ v      ...(prf)
          }
        h1,h2 : Farr x ~> Arr_v
        h1 = U $ MkHom xi . (univ x).UP.exists Arr_u
        h2 = U $ (univ x).UP.exists Arr_v
        lemma : (B .HomSet (Fobj x) b).equivalence.relation
                  (Id . phi u)
                  (phi v)
        lemma = ((univ x).UP.unique Arr_v (MkHom h1) (MkHom h2)).runEq
    in CalcWith (B .HomSet _ _) $
    |~ phi u
    ~~ Id . phi u ..<(B .laws.idLftNeutral _)
    ~~ phi v      ...(lemma)

  public export
  psi : {x : C .Obj} -> {b : B .Obj} -> B .Hom (Fobj x) b -> C .Hom x (G !! b)
  psi {x,b} p = G .map p . (Unit x)

  public export
  psiCong : {x : C .Obj} -> {b : B .Obj} ->
    SetoidHomomorphism (B .HomSet (Fobj x) b) (C .HomSet x (G !! b))
      (psi {x,b})
  psiCong {x,b} p q prf = CalcWith (C .HomSet x (G !! b)) $
    |~ G .map p . (Unit x)
    ~~ G .map q . (Unit x)
      ...((G .structure.mapHom.homomorphic p q prf) . (Unit x))

  public export
  Fmap : {x,y : C .Obj} -> C .Hom x y -> B .Hom (Fobj x) (Fobj y)
  Fmap {y} u = phi (Unit y . u)

  public export
  GFmap : {x,y : C .Obj} -> (u : C .Hom x y) ->
    C .Hom (G !! Fobj x) (G !! Fobj y)
  GFmap u = G .map $ Fmap u

  public export
  UnitNat : {x,y : C .Obj} -> (u : C .Hom x y) ->
    (C .HomSet x (G !! Fobj y)).equivalence.relation
      (Unit y . u)
      ((GFmap u) . (Unit x))
  UnitNat {x,y} u = (C .HomSet x (G !! Fobj y)).equivalence.symmetric _ _
    (phiMor (Unit y . u)).preserves

  congUnit : {x,y : C .Obj} ->
             {u1, u2 : C .Hom (G !! Fobj x) y} ->
             (prf : (C .HomSet (G !! Fobj x) y).equivalence.relation u1 u2) ->
             (C .HomSet x y).equivalence.relation
                  (u1 . (Unit x))
                  (u2 . (Unit x))
  -- bug: should be the following, but takes forever to typecheck
  --congUnit {x} prf = prf . (Unit x)

  %unbound_implicits off
  public export
  F : C ~> B
  F = MkFunctor
    { structure = MkStructure
        { mapObj = Fobj
        , mapHom = MkSetoidHomomorphism
          { H = Fmap
          , homomorphic = \u,v,prf => phiCong _ _ (Unit _ . prf)
          }
        }
    , functoriality = Check
        { id = \x =>
          let h1,h2 : (x ~~> G).Hom (Farr x) (Farr x)
              h1 = MkHom $ MkHomo
                { H = Fmap Id
                , preserves = CalcWith (C .HomSet _ _) $
                  |~ G .map (Fmap Id) . (Unit x)
                  ~~ Unit x . Id ..<(UnitNat Id)
                  ~~ Unit x      ...(C .laws.idRgtNeutral _)
                }
              h2 = Id
          in ((univ x).UP.unique (Farr x) h1 h2).runEq
        , comp = \u,v =>
          {- Appeal to UP.unique, since we have two Arrow-morphisms:

                --------------[Unit X]------------> GF X
               /                                     |
              /            phiMor.preserves          |
             X                   =                   | GF (u . v)
              \                                      |
               \                                     v
                --[v]--> Y --[u]--> Z --[Unit Z]--> GF Z
             and
                --------------[Unit X]------------> GF X
               /                                     | GF v
              /   UnitNat                            v
             X      =         ---[Unit Y]---------> GF Y
              \              /    UnitNat            | GF u
               \           /          =              v
                --[v]--> Y --[u]--> Z --[Unit Z]--> GF Z
          -}
          let X,Y,Z : C .Obj
              X = v.src
              Y = u.src
              Z = u.tgt
              ArrTgt : X `Arrow` G
              ArrTgt = (MkArrow {Cod = Fobj Z, Arr = Unit Z . (u . v)})

              h1,h2 : (X ~~> G).Hom
                        (Farr X)
                        ArrTgt
              h1 = MkHom $ MkHomo
                { H = Fmap (u . v)
                , preserves = (phiMor {x = X, b = Fobj Z}
                                      (Unit Z . (u . v))).preserves
                }
              h2 = MkHom $ MkHomo
                { H = Fmap u . Fmap v
                , preserves = CalcWith (C .HomSet _ _) $
                  |~ (G .map $ Fmap u . Fmap v) . (Unit X)
                  ~~ ((GFmap u) . (GFmap v)) . (Unit X)
                                       ...(congUnit $
                                           G .functoriality.comp (Fmap u) (Fmap v))
                  ~~  (GFmap u) . ((GFmap v)  . (Unit X))
                                       ..<(C .laws.associativity (GFmap u) (GFmap v) (Unit X))
                  ~~  (GFmap u) . (Unit Y  . v)
                                       ..<(?h131)--(GFmap u) . (UnitNat v)) -- bug?
                  ~~ ((GFmap u) .  Unit Y) . v
                                       ...(C .laws.associativity (GFmap u) (Unit Y) v)
                  ~~ (Unit Z . u) . v  ..<(?h1909) --UnitNat u . v) -- bug?
                  ~~ (Unit Z) . (u . v) ..<(C .laws.associativity (Unit Z) u v)
                }
          in ((univ X).UP.unique ArrTgt h1 h2).runEq
        }
    }
  %unbound_implicits on

  public export
  psi_phi : {x : C .Obj} -> {b : B .Obj} -> (u : C .Hom x (G !! b)) ->
    (C .HomSet x (G !! b)).equivalence.relation
      (psi {x,b} (phi {x,b} u))
      u
  psi_phi {x,b} u = CalcWith (C .HomSet _ _) $
    |~ G .map (phi {x,b} u) . (Unit x)
    ~~ u ...((phiMor {x,b} u).preserves)

  public export
  phi_psi : {x : C .Obj} -> {b : B .Obj} -> (p : B .Hom (Fobj x) b) ->
    (B .HomSet (Fobj x) b).equivalence.relation
      (phi {x,b} (psi {x,b} p))
      p
  phi_psi {x,b} p =
    let u : C .Hom x (G !! b)
        u = psi p
        ArrPhi : x `Arrow` G
        ArrPhi = MkArrow {Cod = b, Arr = u}
        h1,h2 : (x ~~> G).Hom (Farr x) ArrPhi
        h1 = MkHom $ phiMor {x,b} u
        h2 = MkHom $ MkHomo
          { H = p
          , preserves = (C .HomSet _ _).equivalence.reflexive _
          }
    in ((univ x).UP.unique ArrPhi h1 h2).runEq

  public export
  AdjunctionByUniversals : Adjunction C B
  AdjunctionByUniversals = MkAdjunction
    { lft = F
    , rgt = G
    , adjoint = AreAdjoint
      { mate = MkIsomorphism
        { Fwd = MkSetoidHomomorphism psi psiCong
        , Bwd = MkSetoidHomomorphism phi phiCong
        , Iso = IsIsomorphism
          { BwdFwdId = phi_psi
          , FwdBwdId = psi_phi
          }
        }
      , naturality = \p,u,f =>
        let X1,X2 : C .Obj
            X2 = u.src
            X1 = u.tgt
            B1,B2 : B .Obj
            B1 = p.src
            B2 = p.tgt
        in CalcWith (C .HomSet _ _) $
        |~ psi (p . f . (F .map u))
        ~~ G .map (p . f . (F .map u)) . (Unit X2) .=.(Refl)
        ~~ (G .map p . (G .map f) . (G .map $ F .map u)) . (Unit X2)
                           ...(?h190110)
                           --bug --...(G .functoriality [p, f, F .map u] . (Unit X2))
        ~~ ((G .map p . (G .map f)) . (G .map $ F .map u)) . (Unit X2)
                           ...(?h121921010)
                        --bug
                        {- ...(C .laws.associativity (G .map p) (G .map f)
                                 (G .map $ F .map u) . (Unit X2)) -}
        ~~ ((G .map p) . (G .map f)) . ((G .map $ F .map u) . (Unit X2))
                           ...(?h0) --bug --..<(C .laws.associativity ((G .map p) . (G .map f)) (G .map $ F .map u) (Unit X2))
        ~~ ((G .map p) . (G .map f)) . (Unit X1 . u)
                  ...(?h191910) --bug ... --..<(((G .map p) . (G .map f)) . (UnitNat u))
        ~~ (G .map p) . ((G .map f) . (Unit X1 . u))
            ..<(C .laws.associativity (G .map p) (G .map f) ((Unit X1) . u))
        ~~ (G .map p) . ((G .map f) . (Unit X1)) . u
            ...((G .map p) . (C .laws.associativity (G .map f) (Unit X1) u))
        ~~ G .map p . psi f . u .=.(Refl)
      }
    }
%hide F
%hide Farr
%hide Fobj
%hide Universal.Unit
%hide phiMor
%hide phi
%hide phiCong
%hide psi
%hide psiCong
%hide Fmap
%hide GFmap
%hide UnitNat
%hide congUnit
%hide psi_phi
%hide phi_psi
