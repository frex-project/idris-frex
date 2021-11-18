module MagicListTests

import Frex.Magic
import Frexlet.Monoid

import Data.List

%language ElabReflection
%logging 2

namespace Assoc -- TODO remove when hole names are no longer leaked
  assoc : {u : Setoid} -> {a,b,c : List (U u)} -> u .ListEquality (a ++ (b ++ c)) ((a ++ b) ++ c)
  assoc {u} = %runElab frexMagic MonoidFrexlet (ListMonoid {A = u})

namespace Assoc4 -- TODO remove when hole names are no longer leaked
  assoc4 : {u : Setoid} -> {a,b,c,d : List (U u)} -> u .ListEquality ((a ++ (b ++ c)) ++ d) (a ++ (b ++ (c ++ d)))
  assoc4 {u} = %runElab frexMagic MonoidFrexlet (ListMonoid {A = u})
