{-# OPTIONS --type-in-type #-}
module Lectures.Week6 where

open import Data.Unit hiding (_≤_)
open import Data.Product

open import Function as Fun

open import Relation.Binary.PropositionalEquality
open import Axiom.UniquenessOfIdentityProofs.WithK

open import Common.Category

open Category

---------------------------------------------------------------------------
-- The category of sets
---------------------------------------------------------------------------

SET : Category
SET = {!!}



















---------------------------------------------------------------------------
-- Monoids and monoid morphisms
---------------------------------------------------------------------------

record Monoid : Set₁ where
  field
    Carrier : Set
    _∙_ : Carrier -> Carrier -> Carrier
    ε : Carrier

  field
    assoc : ∀ {x y z} → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z
    identityˡ : ∀ {x} → ε ∙ x ≡ x
    identityʳ : ∀ {x} → x ∙ ε ≡ x
open Monoid

record MonoidMorphism (A B : Monoid) : Set where
  private
    module A = Monoid A
    module B = Monoid B

  field
    fun : Carrier A -> Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-∙ : ∀ x y → fun (x A.∙ y) ≡ (fun x B.∙ fun y)
open MonoidMorphism

eqMonoidMorphism : {A B : Monoid} -> {f g : MonoidMorphism A B} ->
                   fun f ≡ fun g -> f ≡ g
eqMonoidMorphism {A} {B} {f} {g} refl =
  eqMonoidMorphism' (ext (λ x → ext λ y → uip _ _)) (uip _ _)
  where
    module A = Monoid A
    module B = Monoid B
    eqMonoidMorphism' :
      {fun : A.Carrier -> B.Carrier}
      {∙-f ∙-g : ∀ x y → fun (x A.∙ y) ≡ (fun x B.∙ fun y)}
      {ε-f ε-g : fun (A.ε) ≡ B.ε} ->
      ∙-f ≡ ∙-g -> ε-f ≡ ε-g ->
        _≡_ {A = MonoidMorphism A B}
            (record { fun = fun ; preserves-∙ = ∙-f ; preserves-ε = ε-f })
            (record { fun = fun ; preserves-∙ = ∙-g ; preserves-ε = ε-g })
    eqMonoidMorphism' refl refl = refl

MONOID : Category
MONOID = {!!}


















---------------------------------------------------------------------------
-- Preorders and order-preserving functions
---------------------------------------------------------------------------

record Preorder : Set1 where
  field
    Carrier : Set
    _≤_ : Carrier -> Carrier -> Set
    reflexive : ∀ {x} → x ≤ x
    transitive : ∀ {x y z} → x ≤ y -> y ≤ z -> x ≤ z
    propositional : ∀ {x y} → (p q : x ≤ y) -> p ≡ q
open Preorder

record MonotoneMap (P Q : Preorder) : Set1 where
  private
    module P = Preorder P
    module Q = Preorder Q

  field
    fun : Carrier P -> Carrier Q
    monotone : ∀ x y → x P.≤ y -> fun x Q.≤ fun y
open MonotoneMap

eqMonotoneMap : {P Q : Preorder} -> {f g : MonotoneMap P Q} ->
                   fun f ≡ fun g -> f ≡ g
eqMonotoneMap {P} {Q} {f} {g} refl
  = cong (λ z → record { fun = fun g; monotone = z })
         (ext λ x → ext (λ y → ext λ p → propositional Q _ _))

PREORDER : Category
PREORDER = {!!}

















---------------------------------------------------------------------------
-- Discrete categories
---------------------------------------------------------------------------

discrete : Set -> Category
discrete X = {!!}















---------------------------------------------------------------------------
-- Monoids as categories
---------------------------------------------------------------------------

monoid : Monoid -> Category
monoid M = {!!}


















---------------------------------------------------------------------------
-- Preorders as categories
---------------------------------------------------------------------------

porder : Preorder -> Category
porder P = {!!}

