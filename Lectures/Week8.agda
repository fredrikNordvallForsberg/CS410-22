{-# OPTIONS --type-in-type #-}
module Lectures.Week8 where

open import Data.Nat hiding (_≤_)
open import Function using (_∘_)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Common.Category
open import Common.Category.Adjunctions


open import Lectures.Week7

---------------------------------------------------------------------------
-- Kleisli categories
---------------------------------------------------------------------------

open import Common.Category.Solver

module _ {C : Category} where

  open Category
  open Monad
  open NaturalTransformation

  Kleisli : Monad C -> Category
  Kleisli M = {!!}

-- Note to self: r, l, assoc















---------------------------------------------------------------------------
-- Interlude: a solver for equations in categories
---------------------------------------------------------------------------

open import Common.Category.Solver

module _ {C : Category} where

  open Category C
  open Functor

{-

      F X
       |  \   F f
F id   |   ----------
       |             \
       v              v
      F X ----------> F X
       |      F f      |
       |               |
     g |               | g
       |               |
       v     F h       v      F k
      F Y ----------> F Y ----------> F Z
       |                               ^
       \------------------------------/
                   F (h ; k)
-}


  example : {X Y Z : Obj}(F : Functor C C) ->
            (f : Hom X X)(g : Hom (act F X) (act F Y))(h : Hom Y Y)(k : Hom Y Z) ->
            (assumption : comp (fmap F f) g ≡ comp g (fmap F h)) ->
            comp (fmap F id) (comp g (fmap F (comp h k)))
              ≡ comp (comp (fmap F f) g) (fmap F k)
  example F f g h k p = {!!}




{- Solver summary:

1. Basic format to prove f ≡ g:
  C ⊧begin fSyn ≡⟦ p₁ ⟧ f₁ ≡⟦ p₂ ⟧ f₂ ≡⟦ ... ⟧ gSyn ⟦∎⟧
  where fSyn, gStn are "syntactic copies" of f, g:
    comp replaced by compSyn
    id   replaced by idSyn
    fmap replaced by fmapSyn
    other morphisms h replaced by < h >
2. Reshuffling brackets, identity laws and functors preserving id and
   comp you get for free with "solveCat refl"
3. For interesting equations, place -[ focus ]- and prove with
     reduced (rd, ... , rq p , rd ...)
   where p proves interesting equation.
-}
