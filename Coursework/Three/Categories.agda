{-# OPTIONS --type-in-type #-}
module Coursework.Three.Categories where

open import Relation.Binary.PropositionalEquality
open import Axiom.UniquenessOfIdentityProofs.WithK

import Function as Fun

open import Common.Category

{- Monoids -}

record Monoid : Set₁ where
  field
    Carrier : Set
    _∙_ : Carrier -> Carrier -> Carrier
    ε : Carrier

  field
    assoc : ∀ {x y z} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
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

open Category
open Functor

MONOID : Category
Obj MONOID = Monoid
Hom MONOID = MonoidMorphism
fun (id MONOID) = Fun.id
preserves-ε (id MONOID) = refl
preserves-∙ (id MONOID) x y = refl
fun (comp MONOID f g) = Fun._∘′_ (fun g) (fun f)
preserves-ε (comp MONOID f g) rewrite preserves-ε f | preserves-ε g = refl
preserves-∙ (comp MONOID f g) x y rewrite preserves-∙ f x y | preserves-∙ g (fun f x) (fun f y) = refl
assoc MONOID = eqMonoidMorphism refl
identityˡ MONOID = eqMonoidMorphism refl
identityʳ MONOID = eqMonoidMorphism refl

FORGET : Functor MONOID SET
act FORGET = Carrier
fmap FORGET = fun
identity FORGET = refl
homomorphism FORGET = refl

{- Preorders -}

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
Obj PREORDER = Preorder
Hom PREORDER = MonotoneMap
fun (Category.id PREORDER) = λ x → x
monotone (Category.id PREORDER) x y x≤y = x≤y
fun (comp PREORDER f g) a = fun g (fun f a)
monotone (comp PREORDER f g) x y x≤y = monotone g _ _ (monotone f x y x≤y)
assoc PREORDER = eqMonotoneMap refl
identityˡ PREORDER = eqMonotoneMap refl
identityʳ PREORDER = eqMonotoneMap refl

{- Categories -}

idFunctor : {C : Category} -> Functor C C
act idFunctor X = X
fmap idFunctor f = f
identity idFunctor = refl
homomorphism idFunctor = refl

compFunctor : {A B C : Category} -> Functor A B → Functor B C → Functor A C
act (compFunctor F G) =  (act G) Fun.∘′ (act F)
fmap (compFunctor F G) f = fmap G (fmap F f)
identity (compFunctor F G) = trans (cong (fmap G) (identity F)) (identity G)
homomorphism (compFunctor F G) = trans (cong (fmap G) (homomorphism F)) (homomorphism G)

CAT : Category
Obj CAT = Category
Hom CAT = Functor
id CAT = idFunctor
comp CAT = compFunctor
assoc CAT = eqFunctor refl refl
identityˡ CAT = eqFunctor refl refl
identityʳ CAT = eqFunctor refl refl

