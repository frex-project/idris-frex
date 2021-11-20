module Binary.Properties

import Data.Fin

import Data.Nat
import Data.Nat.Division
import Data.Nat.Order
import Data.Nat.Order.Properties
import Data.Nat.Properties

import Data.Vect
import Data.Vect.Elem

import Frex
import Frex.Free

import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Nat

import Syntax.PreorderReasoning

import VectReasoning

import Binary.Modular
import Binary.Core
import Binary.BruteForce
import Binary.Number
import Binary.Bits

uip : (eq1, eq2 : x ~=~ y) -> eq1 = eq2
uip Refl Refl = Refl

export 0
numberUnique : (x : LE.Number width val_x)
            -> (y : LE.Number width val_y)
            -> val_x = val_y
            -> x = y
numberUnique [] [] _ = Refl
numberUnique {width = S width}      -- coverage checker wants to replace `_` here vvvvvvvv instead of `Refl`  --- bug?
  ((bit_x :: bits_x) {width = _, b = b_x, val = val_x, val' = val', valueFord = valford_x})
  ((bit_y :: bits_y) {width = _, b = b_y, val = val_y, val' = _   , valueFord = valford_y})
  Refl with (let 0 lemma : (a,b : Nat) -> (2*b + a = (a + b) + b)
                 lemma a b = Frex.solve 2 (Frex Nat.Additive) {prf = (%search, %search)} $
                           (2 *: (Dyn 1)) :+: (Dyn 0)
                                 =-=
                           (Dyn 0 :+: Dyn 1) :+: Dyn 1 in
           let
               0 w = Calc $
                  |~ b_x
                  ~~ mod2 b_x ...(sym $ bitModulo (bit_x))
                  ~~ mod2 (2*val_x + b_x) ...(sym $ mod2Affine b_x val_x)
                  ~~ mod2 ((b_x + val_x) + val_x)
                     ...(cong mod2 $ lemma b_x val_x) -- frexify!
                  ~~ mod2 val' ...(cong mod2 $ sym valford_x)
                  -- similarly, go backwards.
                  -- TODO: refactor these steps into a lemma
                  ~~ mod2 ((b_y + val_y) + val_y)
                          ...(cong mod2 valford_y)
                  ~~ mod2 (2*val_y + b_y)
                          ...(cong mod2 $ sym $ lemma b_y val_y) -- frexify!
                  ~~ mod2 b_y ...(mod2Affine b_y val_y)
                  ~~ b_y ...(bitModulo bit_y)
               0 u = bitUnique bit_x bit_y w
               0 v = Calc $
                     |~ 2*val_x + b_x
                     ~~ (b_x + val_x) + val_x ...(lemma b_x val_x) -- frexify!
                     ~~ val'                  ...(sym $ valford_x)
                     ~~ (b_y + val_y) + val_y ...(valford_y)
                     ~~ 2*val_y + b_y         ...(sym $ lemma b_y val_y)
                     ~~ 2*val_y + b_x         ...(cong (2*val_y +) $ sym w)
               0 z = plusRightCancel (2*val_x) (2*val_y) b_x v
               0 q = multSucLeftCancel val_x val_y 1 z
          in (w, u, q))
 numberUnique {width = S width}
  ((bit :: bits_x) {width = _, b    , val = val_x, val'       , valueFord = valueFord_x})
  ((_   :: bits_y) {width = _, b = b, val = val_y, val' = val', valueFord = valueFord_y})
  Refl | (Refl, Refl, q) with (numberUnique bits_x bits_y q)
  numberUnique {width = S width}
   ((bit :: bits) {width = _, b    , val      , val'       , valueFord = valueFord_x})
   ((_   :: _   ) {width = _, b = b, val = val, val' = val', valueFord = valueFord_y})
   Refl | (Refl, Refl, Refl) | Refl = rewrite uip valueFord_x valueFord_y in Refl

-- -- Comes later in the paper, but since type-checking `addNumber` takes
-- -- so long, it's quicker to have it here

%unbound_implicits off
export 0
numCarryUnique : forall width, val . (x, y : NumCarry width val) -> x = y
numCarryUnique
  (Carrying num_x carry_x {c = c_x, val = val_x, val'       , valueFord = valueFord_x})
  (Carrying num_y carry_y {c = c_y, val = val_y, val' = val', valueFord = valueFord_y})
  = let lemma : (a,b,c : Nat) -> (a * b + c = c + b*a)
        lemma a b c = Calc $ -- semiring frexlet would help here
            |~ a*b + c
            ~~ b*a + c ...(cong (+c) $ multCommutative a b)
            ~~ c + b*a ...(plusCommutative _ _)
        0 numer : Nat
        numer = c_x * (2 `power` width) + val_x
        0 decomposition : (c_x * (2 `power` width) + val_x
                         = c_y * (2 `power` width) + val_y)
        decomposition =
          Calc $
          |~ c_x * (2 `power` width) + val_x
          ~~ val_x + (2 `power` width) * c_x ...(      lemma c_x (2 `power` width) val_x)
          ~~ val'                            ...(sym $ valueFord_x)
          ~~ val_y + (2 `power` width) * c_y ...(      valueFord_y)
          ~~ c_y * (2 `power` width) + val_y ...(sym $ lemma c_y (2 `power` width) val_y)
        0 powern_neq_zero : NonZero (2 `power` width)
        powern_neq_zero = powerNZ width
        0 val_x_lt_2n : val_x `LT` (2 `power` width)
        val_x_lt_2n = bitsBound num_x
        0 val_y_lt_2n : val_y `LT` (2 `power` width)
        val_y_lt_2n = bitsBound num_y
    in let (div_eq_c_x, mod_eq_val_x) =
               DivisionTheoremUniqueness numer (2 `power` width) powern_neq_zero
               c_x val_x val_x_lt_2n
               Refl
           (div_eq_c_y, mod_eq_val_y) =
               DivisionTheoremUniqueness numer (2 `power` width) powern_neq_zero
               c_y val_y val_y_lt_2n
               decomposition
    in let 0 val_x_eq_val_y : (val_x = val_y)
           val_x_eq_val_y = trans (sym mod_eq_val_x) mod_eq_val_y
           -- similarly:
           0 c_x_eq_c_y : (c_x = c_y)
           c_x_eq_c_y = trans (sym div_eq_c_x) div_eq_c_y
           0 num_x_eq_num_y : (num_x = num_y)
           num_x_eq_num_y = numberUnique num_x num_y val_x_eq_val_y
           0 carry_x_eq_carry_y : (carry_x = carry_y)
           carry_x_eq_carry_y = bitUnique carry_x carry_y c_x_eq_c_y
    in keep $ Calc $
      |~ Carrying num_x carry_x {c = c_x, val = val_x, valueFord = valueFord_x}
      ~~ Carrying num_y carry_y {c = c_y, val = val_y, valueFord = valueFord_y}
      ...(cong5 (\ c : Nat , val : Nat , num : LE.Number width val, carry : Bit c,
                   valueFord : (val' = val + (2 `power` width) * c) =>
                   num `Carrying` carry)
                c_x_eq_c_y
                val_x_eq_val_y
                num_x_eq_num_y
                carry_x_eq_carry_y
                (heterogenousUIP valueFord_x valueFord_y)
                )

    where
      heterogenousUIP : forall x,y,z . (eq1 : x ~=~ y) -> (eq2 : x ~=~ z) -> eq1 = eq2
      heterogenousUIP Refl Refl = Refl

      cong5 : {0 a1 : Type}
        -> {0 a2 : a1 -> Type}
        -> {0 a3 : (x1 : a1) -> (x2 : a2 x1) -> Type}
        -> {0 a4 : (x1 : a1) -> (x2 : a2 x1) -> (x3 : a3 x1 x2) -> Type}
        -> {0 a5 : (x1 : a1) -> (x2 : a2 x1) -> (x3 : a3 x1 x2) ->
                                                (x4 : a4 x1 x2 x3) -> Type}
        -> {0 p : (z1 : a1) -> (z2 : a2 z1) -> (z3 : a3 z1 z2) ->
                 (z4 : a4 z1 z2 z3) -> (z5 : a5 z1 z2 z3 z4) -> Type}
        -> (f : (z1 : a1) -> (z2 : a2 z1) -> (z3 : a3 z1 z2) ->
                 (z4 : a4 z1 z2 z3) -> (z5 : a5 z1 z2 z3 z4) -> p z1 z2 z3 z4 z5)
        -> {x1,y1 : a1}                 -> x1 ~=~ y1
        -> {x2 : a2 x1} -> {y2 : a2 y1} -> x2 ~=~ y2
        -> {x3 : a3 x1 x2} -> {y3 : a3 y1 y2} -> x3 ~=~ y3
        -> {x4 : a4 x1 x2 x3} -> {y4 : a4 y1 y2 y3} -> x4 ~=~ y4
        -> {x5 : a5 x1 x2 x3 x4} -> {y5 : a5 y1 y2 y3 y4} -> x5 ~=~ y5
        -> f x1 x2 x3 x4 x5 ~=~ f y1 y2 y3 y4 y5
      cong5 _ Refl Refl Refl Refl Refl = Refl
%unbound_implicits on

export 0
numCarryUniqueForded : (x : NumCarry width val_x)
                    -> (y : NumCarry width val_y)
                    -> {auto 0 ford : (val_x = val_y)}
                    -> x = y
numCarryUniqueForded x y {ford = Refl} = numCarryUnique x y
