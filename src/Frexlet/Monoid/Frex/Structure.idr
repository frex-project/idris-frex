||| The structure of the frex for (mere) monoids
||| Its elements are given by a 'polynomial' of the form:
||| 
||| an * xn * ... a1 * x1 * a0
|||
||| Its unit is 1, and multiplication is given by:
|||
||| (an * xn * ... a1 * x1 * a0) *(bm * ym * ... b1 * y1 * b0)
||| := an * xn * ... a1 * x1 * (a0*bm) * ym ... * y1 * b0
||| 
||| and some care is required for the edge cases.
module Frexlet.Monoid.Frex.Structure


import Frex

import Frexlet.Monoid.Theory
import Frexlet.Monoid.Notation

import Notation.Multiplicative

import Data.List
import Data.List.Elem

import Data.Setoid.Pair

infixl 7 <><

||| A list of elements alternating between two types starting with
||| `pen` and ending with `ult`imate.
public export
data PenList : (pen, ult : Type) -> Type 

||| A list of elements alternating between two types starting and
||| ending with an `ult`imate.
public export
data UltList : (pen, ult : Type) -> Type where
  Ultimate : (i : ult) -> UltList pen ult
  ConsUlt : (i : ult) -> PenList pen ult -> UltList pen ult

public export
data PenList : (pen, ult : Type) -> Type where
  ConsPen : (x : pen) -> UltList pen ult -> PenList pen ult

-- Smart constructors so we can get a list notation, and we don't have
-- to think too much about the parity of the list
namespace Hack
  public export
  Nil : Unit
  Nil = ()

  public export
  (::) : ult -> Unit -> UltList pen ult
  (::) x _ = Ultimate x

namespace Ult
  public export
  (::) : ult -> PenList pen ult -> UltList pen ult
  (::) = ConsUlt

%name UltList is,js,ks,ells

namespace Pen
  public export
  (::) : pen -> UltList pen ult -> PenList pen ult
  (::) = ConsPen

%name PenList xs, ys, zs

public export
(<><) : {a : Monoid} -> PenList pen (U a) -> UltList pen (U a) -> PenList pen (U a)
public export
(++)  : {a : Monoid} -> UltList pen (U a) -> UltList pen (U a) -> UltList pen (U a)

(++) (Ultimate i) (Ultimate y) = Ultimate (a.sem Product i y)
(++) (Ultimate i) (ConsUlt y is) = (a.sem Product i y) :: is
(++) (ConsUlt i xs) ys = i :: (xs <>< ys)

(<><) (ConsPen x is) js = x :: (is ++ js)

namespace Equality
  ||| Equality for UltList pen ult
  public export
  data UltListEquality : (pen, ult : Setoid) -> (is, js : UltList (U pen) (U ult)) -> Type
  
  ||| Equality for PenList pen ult
  public export
  data PenListEquality : (pen, ult : Setoid) -> (is, js : PenList (U pen) (U ult)) -> Type where
    ConsPen : pen.equivalence.relation x y -> UltListEquality pen ult is js ->
               PenListEquality pen ult (x :: is) (y :: js)
               
  public export
  data UltListEquality : (pen, ult : Setoid) -> (is, js : UltList (U pen) (U ult)) -> Type where
    Ultimate : ult.equivalence.relation i j -> UltListEquality pen ult (Ultimate i) (Ultimate j)
    ConsUlt  : ult.equivalence.relation i j -> PenListEquality pen ult xs ys ->
               UltListEquality pen ult (i :: xs) (j :: ys)
  
  -- Again, smart constructors so that we can avoid thinking about parity sometimes
  namespace Hack
    public export
    (::) : ult.equivalence.relation i j -> Unit -> UltListEquality pen ult (Ultimate i) (Ultimate j)
    (::) prf _ = Ultimate prf

  namespace Ult
    public export
    (::) : ult.equivalence.relation i j  -> PenListEquality pen ult xs ys -> 
      UltListEquality pen ult (i :: xs) (j :: ys)
    (::) = ConsUlt

  namespace Pen
    public export
    (::) : pen.equivalence.relation x y -> UltListEquality pen ult is js -> 
      PenListEquality pen ult (x :: is) (y :: js)
    (::) = ConsPen

---------------------- Equality on alternating is an equivalence 
  ----------------- Reflexivity --------------------------
  public export
  UltListReflexive : (pen, ult : Setoid) -> (is : UltList (U pen) (U ult)) 
    -> UltListEquality pen ult is is
  public export
  PenListReflexive : (pen, ult : Setoid) -> (xs : PenList (U pen) (U ult)) 
    -> PenListEquality pen ult xs xs
  
  PenListReflexive pen ult (ConsPen x is) = 
    pen.equivalence.reflexive x :: UltListReflexive pen ult is

  UltListReflexive pen ult (Ultimate i) = Ultimate (ult.equivalence.reflexive i)
  UltListReflexive pen ult (ConsUlt i xs) = 
    ult.equivalence.reflexive i :: PenListReflexive pen ult xs

  ----------------- Symmetry --------------------------
  public export
  UltListSymmetric : (pen, ult : Setoid) -> (is,js : UltList (U pen) (U ult)) ->
    (prf : UltListEquality pen ult is js) ->
    UltListEquality pen ult js is
  public export
  PenListSymmetric : (pen, ult : Setoid) -> (xs,ys : PenList (U pen) (U ult)) ->
    (prf : PenListEquality pen ult xs ys) ->
    PenListEquality pen ult ys xs

  PenListSymmetric pen ult (ConsPen x is) (ConsPen y js) (ConsPen prf1 prf2) = 
    pen.equivalence.symmetric x y prf1 :: UltListSymmetric pen ult is js prf2
    
  UltListSymmetric pen ult (Ultimate i) (Ultimate j) (Ultimate prf) = 
    Ultimate $ ult.equivalence.symmetric i j prf
  UltListSymmetric pen ult (ConsUlt i xs) (ConsUlt j ys) (ConsUlt prf1 prf2) = 
    ult.equivalence.symmetric i j prf1 :: PenListSymmetric pen ult xs ys prf2

  ---------------- Transitivity ------------------------
  public export
  UltListTransitive : (pen, ult : Setoid) -> (is,js,ks : UltList (U pen) (U ult)) ->
    (prf1 : UltListEquality pen ult is js) -> (prf2 : UltListEquality pen ult js ks) ->
    UltListEquality pen ult is ks
    
  public export
  PenListTransitive : (pen, ult : Setoid) -> (xs,ys,zs : PenList (U pen) (U ult)) ->
    (prf1 : PenListEquality pen ult xs ys) -> (prf2 : PenListEquality pen ult ys zs) ->
    PenListEquality pen ult xs zs
  
  PenListTransitive pen ult (ConsPen x is) (ConsPen y js) (ConsPen z ks) 
    (ConsPen prf11 prf12) (ConsPen prf21 prf22) = 
    pen.equivalence.transitive x y z prf11 prf21 ::
    UltListTransitive pen ult is js ks prf12 prf22

  UltListTransitive pen ult (Ultimate i) (Ultimate j) (Ultimate k) (Ultimate prf1) (Ultimate prf2) 
    = Ultimate $ ult.equivalence.transitive i j k prf1 prf2
  UltListTransitive pen ult (ConsUlt i xs) (ConsUlt j ys) (ConsUlt k zs) 
    (ConsUlt prf11 prf12) (ConsUlt prf21 prf22) = 
    ult.equivalence.transitive i j k prf11 prf21 ::
    PenListTransitive pen ult xs ys zs prf12 prf22

public export
PenListSetoid, UltListSetoid : (pen, ult : Setoid) -> Setoid
PenListSetoid pen ult = MkSetoid (PenList (U pen) (U ult)) $ MkEquivalence
  { relation   = PenListEquality   pen ult
  , reflexive  = PenListReflexive  pen ult
  , symmetric  = PenListSymmetric  pen ult
  , transitive = PenListTransitive pen ult
  }

UltListSetoid pen ult = MkSetoid (UltList (U pen) (U ult)) $ MkEquivalence
  { relation   = UltListEquality   pen ult
  , reflexive  = UltListReflexive  pen ult
  , symmetric  = UltListSymmetric  pen ult
  , transitive = UltListTransitive pen ult
  }
  
public export
FishHomomorphism : (a : Monoid) -> (x : Setoid) -> 
  SetoidHomomorphism 
    (PenListSetoid x (cast a) `Pair`
     UltListSetoid x (cast a))
    (PenListSetoid x (cast a))
    (Prelude.uncurry ((<><) {a}))
public export
AppendHomomorphism : (a : Monoid) -> (x : Setoid) -> 
  SetoidHomomorphism 
    (UltListSetoid x (cast a) `Pair`
     UltListSetoid x (cast a))
    (UltListSetoid x (cast a))
    (Prelude.uncurry ((++) {a}))

FishHomomorphism a s (ConsPen x is0, is) (ConsPen y js0, js) 
  (MkAnd (ConsPen x_eq_y is0_eq_js0) is_eq_js) = 
  x_eq_y :: AppendHomomorphism a s (is0, is) (js0, js) (MkAnd is0_eq_js0 is_eq_js)
  
AppendHomomorphism a s (Ultimate i0,Ultimate i1) (Ultimate j0, Ultimate j1) 
  (MkAnd (Ultimate i0_eq_j0) (Ultimate i1_eq_j1)) = 
  Ultimate $ a.cong 2 (Dyn 0 .*. Dyn 1) [_,_] [_,_] [i0_eq_j0, i1_eq_j1]
AppendHomomorphism a s (Ultimate i0, ConsUlt i1 xs) (Ultimate j0, ConsUlt j1 ys) 
  (MkAnd (Ultimate i0_eq_j0) (ConsUlt i1_eq_j1 xs_eq_ys)) = 
  a.cong 2 (Dyn 0 .*. Dyn 1) [_,_] [_,_] [i0_eq_j0, i1_eq_j1] :: xs_eq_ys
AppendHomomorphism a s (ConsUlt i0 xs0,is1) (ConsUlt j0 ys0, js1) 
  (MkAnd (ConsUlt i0_eq_j0 xs0_eq_ys0) is1_eq_js1) = 
  i0_eq_j0 :: FishHomomorphism a s (xs0, is1) (ys0, js1) (MkAnd xs0_eq_ys0 is1_eq_js1)
AppendHomomorphism _ _ (Ultimate _, _) (ConsUlt _ _, _) (MkAnd _ _) impossible
AppendHomomorphism _ _ (ConsUlt _ _, _) (Ultimate _, _) (MkAnd _ _) impossible


public export 0
FrexCarrier : (a : Monoid) -> (x : Setoid) -> Type
FrexCarrier a x = UltList (U x) (U a)

||| Embedding of concrete elements in the frex by identifying
||| i with the singleton i
public export
(.sta) : (a : Monoid) -> U a -> FrexCarrier a x
(.sta) a = Ultimate 

||| Embedding variables in the frex by identifying
||| x with 1 * x * 1
public export
(.dyn) : (a : Monoid) -> U x -> FrexCarrier a x
(.dyn) a v = a.sem Neutral :: v :: a.sta (a.sem Neutral)

public export 
FrexAlgebraStructure : (a : Monoid) -> (x : Setoid) -> Signature `algebraOver'` (FrexCarrier a x)
FrexAlgebraStructure a x Neutral = a.sta (a.sem Neutral)
FrexAlgebraStructure a x Product = (++) {a}

public export
FrexStructure : (a : Monoid) -> (x : Setoid) -> MonoidStructure
FrexStructure a x = MkSetoidAlgebra 
    { algebra = MkAlgebra (FrexCarrier a x) (FrexAlgebraStructure a x)
    , equivalence = (UltListSetoid x (cast a)).equivalence
    , congruence = \case
        MkOp Neutral => \_,_,_ => (UltListSetoid x (cast a)).equivalence.reflexive _
        MkOp Product => \ [is1,js1],[is2,js2],prf => 
          AppendHomomorphism a x (is1,js1) (is2,js2) (MkAnd (prf 0) (prf 1))
    }

