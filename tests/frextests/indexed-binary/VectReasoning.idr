module VectReasoning

import Data.Vect
import Data.Vect.Elem

export
ElemToFinSpec : {xs : Vect n a} -> (pos : Elem x xs) ->
                index (elemToFin pos) xs = x
ElemToFinSpec Here = Refl
ElemToFinSpec (There pos) = ElemToFinSpec pos 
