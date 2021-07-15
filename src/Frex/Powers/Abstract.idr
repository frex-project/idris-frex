||| Abstract properties of powers
module Frex.Powers.Abstract

import Data.Setoid
import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model

import Frex.Powers.Definition

%default total

parameters {pres : Presentation} {x : Setoid} {a : Model pres}
  public export
  id : (param : Parameterisation pres x a) -> param ~> param
  id param = MkParameterisationMorphism (id _)
    $ \phi, i => (cast a).equivalence.reflexive _

  public export
  (.) : {param1, param2, param3 : Parameterisation pres x a} ->
    (param2 ~> param3) -> (param1 ~> param2) ->
    param1 ~> param3
  (.) {param1, param2, param3} u v = MkParameterisationMorphism (u.H . v.H)
    $ \phi, i => CalcWith @{cast a} $
      |~ (the _ $ param3.Eval.H i).H.H ((u.H . v.H).H.H phi)
      <~ (the _ $ param2.Eval.H i).H.H (v.H.H.H phi) ...(u.preserve _ _)
      <~ (the _ $ param1.Eval.H i).H.H phi           ...(v.preserve _ _)

  ||| Transport a parameterisation across an isomorphism
  public export
  transportParameterisation : {b : SetoidAlgebra pres.signature} ->
    (param : Parameterisation pres x a) ->
    (iso : param.Model.Algebra <~> b) -> Parameterisation pres x a
  transportParameterisation {b} param iso
    = let model : Model pres
          model = transport param.Model iso
          eval : x ~> (model ~~> a)
          eval = MkSetoidHomomorphism
            (\x => let v = Prelude.cast {to = b ~> param.Model.Algebra} (sym iso)
                       u = (param.Eval.H x)
                   in u . v)
            $ \p,q,prf,x => param.Eval.homomorphic
                      p q prf (iso.Iso.Bwd.H x)
      in MkParameterisation model eval

  public export
  coherence : {b : SetoidAlgebra pres.signature} ->
    (param : Parameterisation pres x a) ->
    (iso : param.Model.Algebra <~> b) ->
    param ~> transportParameterisation param iso
  coherence param iso = MkParameterisationMorphism
    (cast iso)
    $ \f,i => (the _ $ param.Eval.H i).H.homomorphic _ _
                     $ iso .Iso.Iso.BwdFwdId f

  public export
  coherenceSym : {b : SetoidAlgebra pres.signature} ->
    (param : Parameterisation pres x a) ->
    (iso : param.Model.Algebra <~> b) ->
    transportParameterisation param iso ~> param
  coherenceSym param iso = MkParameterisationMorphism
    (cast (sym iso))
    $ \f,i => (cast a).equivalence.reflexive _

||| Transport a power along an algebra isomorphism
public export
transport : {pres : Presentation} -> {x : Setoid} -> {a : Model pres} ->
  {b : SetoidAlgebra pres.signature} ->
  (power : x `Power` a) -> (iso : power.Data.Model.Algebra <~> b) ->
  x `Power` a
transport power iso
  = let datum : Parameterisation pres x a
        datum = transportParameterisation power.Data iso
    in MkPower
  { Data = datum
  , UP   = IsUniversal
    { Exists = \other => (coherence power.Data iso) . (power.UP.Exists other)
    , Unique = \other, extend1, extend2, f =>
      let bwdExtendEq = power.UP.Unique other
            ((coherenceSym power.Data iso) . extend1)
            ((coherenceSym power.Data iso) . extend2)
            f
      in CalcWith @{cast b} $
        |~ extend1.H.H.H f
        <~ (iso.Iso.Fwd.H . iso.Iso.Bwd.H) (extend1.H.H.H f)
              ...((cast b).equivalence.symmetric _ _  $
                   iso.Iso.Iso.FwdBwdId _)
        <~ (iso.Iso.Fwd.H . iso.Iso.Bwd.H) (extend2.H.H.H f)
              ...(iso.Iso.Fwd.homomorphic _ _ bwdExtendEq)
        <~ extend2.H.H.H f  ...(iso.Iso.Iso.FwdBwdId _)
    }
  }
