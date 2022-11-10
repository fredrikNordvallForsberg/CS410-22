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
                             Hom SET                         X (act forget P) →
                             Hom PREORDER (act smallestOrder X)            P
fun (morphismOutOfSmallestOrder f) = f
monotone (morphismOutOfSmallestOrder {P = P} f) x .x refl = reflexive P

morphismOutOfSmallestOrderAllOfThem : {X : Set}{P : Preorder} →
                                      Hom PREORDER (act smallestOrder X)            P →
                                      Hom SET                         X (act forget P)
morphismOutOfSmallestOrderAllOfThem h = fun h

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
                       Hom SET (act forget P)             X →
                       Hom PREORDER        P (act chaotic X)
fun (morphismsIntoChaotic f) = f
monotone (morphismsIntoChaotic f) x y p = tt


-----------------------
-- Floors and ceilings
-----------------------

{-
Consider (ℚ, ≤) and (ℤ, ≤). Are they related?

Yes, we have inject : (ℤ, ≤) → (ℚ, ≤) (order-preserving).

[ If we see (ℤ, ≤) and (ℚ, ≤) as "boring" categories with at most one
morphism between objects, inject is a functor.]

What about (ℚ, ≤) → (ℤ, ≤)?

floor : (ℚ, ≤) → (ℤ, ≤)
ceiling : (ℚ, ≤) → (ℤ, ≤)

How do these relate?


ceiling q ≤        i    in ℤ   iff
        q ≤ inject i    in ℚ

i        ≤ floor q    iff
inject i ≤ q

-}


-----------------------
-- The common pattern
-----------------------

open import Common.Category.Adjunctions
open Adjunction

  -- F ⊣ G "F is the left adjoint of G", "G is the right adjoint of F"

discrete⊣forget : Adjunction smallestOrder forget
to discrete⊣forget = morphismOutOfSmallestOrderAllOfThem
from discrete⊣forget = morphismOutOfSmallestOrder
left-inverse-of discrete⊣forget h = eqMonotoneMap refl
right-inverse-of discrete⊣forget k = refl
to-natural discrete⊣forget f g = refl

forget⊣chaotic : Adjunction forget chaotic
fun (to forget⊣chaotic f) = f
monotone (to forget⊣chaotic f) = _
from forget⊣chaotic f = fun f
left-inverse-of forget⊣chaotic h = refl
right-inverse-of forget⊣chaotic h = eqMonotoneMap refl
to-natural forget⊣chaotic f g = ext \ h -> eqMonotoneMap refl

-----------------------
-- One more example
-----------------------

PAIR : Category -> Category -> Category
Obj (PAIR C D) = Obj C × Obj D
Hom (PAIR C D) (X , Y) (X' , Y')= Hom C X X' × Hom D Y Y'
id (PAIR C D) {X , Y} = id C , id D
comp (PAIR C D) (f , g) (f' , g') = (comp C f f') , (comp D g g')
assoc (PAIR C D) = cong₂ _,_ (assoc C) (assoc D)
identityˡ (PAIR C D) = cong₂ _,_ (identityˡ C) (identityˡ D)
identityʳ (PAIR C D) = cong₂ _,_ (identityʳ C) (identityʳ D)

diag : {C : Category} -> Functor C (PAIR C C)
act diag X = (X , X)
fmap diag f = (f , f)
identity diag = refl
homomorphism diag = refl

Either : Functor (PAIR SET SET) SET
act Either (X , Y) = X ⊎ Y
fmap Either (f , g) = Data.Sum.map f g
identity Either = ext λ { (inj₁ x) → refl ; (inj₂ y) → refl }
homomorphism Either = ext λ { (inj₁ x) → refl ; (inj₂ y) → refl }

Either⊣diag : Adjunction Either (diag {SET})
to Either⊣diag {X , Y} f = (λ x → f (inj₁ x)) , (λ y → f (inj₂ y))
from Either⊣diag (h , k) (inj₁ x) = h x
from Either⊣diag (h , k) (inj₂ y) = k y
left-inverse-of Either⊣diag h = ext λ { (inj₁ x) → refl ; (inj₂ y) → refl }
right-inverse-of Either⊣diag (f , g) = refl
to-natural Either⊣diag (f , f') g = refl
