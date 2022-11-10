{-# OPTIONS --type-in-type #-}
module Lectures.Week8 where

open import Data.Nat hiding (_≤_)
open import Function using (_∘_)
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤; tt)

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
  Obj (Kleisli M) = Obj C
  Hom (Kleisli M) X Y = Hom C X (act M Y)
  id (Kleisli M) = return M _
  comp (Kleisli M) f g = comp C f (comp C (fmap M g) (join M _))
  identityʳ (Kleisli M) {f = f} = begin
    comp C f (comp C (Functor.fmap (functor M) (return M _)) (join M _))
      ≡⟨ cong (comp C f) (mapReturnJoin M) ⟩
    comp C f (id C)
      ≡⟨ identityʳ C ⟩
    f ∎ where open ≡-Reasoning
  identityˡ (Kleisli M) {f = g} = C ⊧begin
    compSyn < return M _ > (compSyn (fmapSyn (functor M) < g >) < join M _ >)
      ≡⟦ solveCat refl ⟧
    -[ < return M _ > ；Syn fmapSyn (functor M) < g > ]- ；Syn < join M _ >
      ≡⟦ reduced (rd , rq (sym (natural (returnNT M) _ _ g))) ⟧
    -[  < g > ；Syn < return M _ > ]- ；Syn < join M _ >
      ≡⟦ solveCat refl ⟧
    < g > ；Syn -[ < return M _ > ；Syn < join M _ > ]-
      ≡⟦ reduced ((rq (returnJoin M)) , rd) ⟧
    < g > ；Syn -[ idSyn ]-
      ≡⟦ solveCat refl ⟧
    < g >
      ⟦∎⟧
  assoc (Kleisli M) {f = f} {g} {h} = C ⊧begin
   compSyn < f > (compSyn (fmapSyn (functor M) (compSyn < g > (compSyn (fmapSyn (functor M) < h >) < join M _ >))) < join M _ > )
      ≡⟦ solveCat refl ⟧
   < f > ；Syn fmapSyn (functor M) < g > ；Syn fmapSyn (functor M) (fmapSyn (functor M) < h >) ；Syn -[ fmapSyn (functor M) < join M _ > ；Syn < join M _ > ]-
      ≡⟦ reduced (rq (sym (joinJoin M)) , rd , rd , rd) ⟧
   < f > ；Syn fmapSyn (functor M) < g > ；Syn fmapSyn (functor M) (fmapSyn (functor M) < h >) ；Syn -[ < join M _ > ；Syn < join M _ > ]-
     ≡⟦ solveCat refl ⟧
   < f > ；Syn fmapSyn (functor M) < g > ；Syn -[ fmapSyn (functor M) (fmapSyn (functor M) < h >) ；Syn < join M _ > ]- ；Syn < join M _ >
     ≡⟦ reduced (rd , rq (natural (joinNT M) _ _ h) , rd , rd) ⟧
   < f > ；Syn (fmapSyn (functor M) < g >) ；Syn -[ < join M _ > ；Syn fmapSyn (functor M) < h > ]- ；Syn < join M _ >
     ≡⟦ solveCat refl ⟧
   compSyn (compSyn < f > (compSyn (fmapSyn (functor M) < g >) < join M _ >))
    (compSyn (fmapSyn (functor M) < h >) < join M _ >)
      ⟦∎⟧

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
  example F f g h k p = C ⊧begin -- \models
    compSyn (fmapSyn F idSyn) (compSyn < g > (fmapSyn F (compSyn < h > < k >)))
      ≡⟦ solveCat refl ⟧  -- \[[ \]]
    -[ < g > ；Syn fmapSyn F < h > ]- ；Syn fmapSyn F < k > -- \;
      ≡⟦ reduced (rd , rq (sym p)) ⟧
    -[ fmapSyn F < f > ；Syn < g > ]- ；Syn fmapSyn F < k >
      ≡⟦ solveCat refl ⟧
    compSyn (compSyn (fmapSyn F < f > ) < g > ) (fmapSyn F < k >)
      ⟦∎⟧




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

---------------------------------------------------------------------------
-- Adjunctions
---------------------------------------------------------------------------

open Category
open Functor

open import Lectures.Week6 hiding (SET)
open Preorder
open MonotoneMap

-----------------
-- Order, order!
-----------------

forget : Functor PREORDER SET
act forget X = Carrier X
fmap forget f = fun f
identity forget = refl
homomorphism forget = refl

-- Recall smallestOrder : SET → PREORDER

morphismOutOfSmallestOrder : {X : Set}{P : Preorder} →
                             {!!} →
                             Hom PREORDER (act smallestOrder X) P
morphismOutOfSmallestOrder = {!!}












-- In fact, they are all like that



















-- The "Everything is related to everything else" construction

chaotic : Functor SET PREORDER
Carrier (act chaotic B) = B
_≤_ (act chaotic B) b b' = ⊤
reflexive (act chaotic B) = tt
transitive (act chaotic B) _ _ = tt
propositional (act chaotic B) p q = refl
fun (fmap chaotic f) = f
monotone (fmap chaotic f) x y p = tt
identity chaotic = eqMonotoneMap refl
homomorphism chaotic = eqMonotoneMap refl

morphismsIntoChaotic : {X : Set}{P : Preorder} →
                       {!!} →
                       Hom PREORDER P (act chaotic X)
morphismsIntoChaotic = {!!}


-----------------------
-- Floors and ceilings
-----------------------



















-----------------------
-- The common pattern
-----------------------

open import Common.Category.Adjunctions
open Adjunction


discrete⊣forget : Adjunction smallestOrder forget
discrete⊣forget = {!!}

forget⊣chaotic : Adjunction forget chaotic
forget⊣chaotic = {!!}


















-----------------------
-- One more example
-----------------------

PAIR : Category -> Category -> Category
PAIR C D = {!!}

diag : {C : Category} -> Functor C (PAIR C C)
diag = {!!}

Either : Functor (PAIR SET SET) SET
Either = {!!}

Either⊣diag : Adjunction Either (diag {SET})
Either⊣diag = {!!}
