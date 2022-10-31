{-# OPTIONS --type-in-type #-}
module Common.Category where

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs.WithK
import Function as Fun

----------------------------
-- Function extensionality
----------------------------

postulate
  ext : Extensionality _ _

----------------------------
-- Categories
----------------------------

record Category : Set where
  eta-equality

  field
    Obj : Set
    Hom : Obj -> Obj -> Set

  field
    id  : ∀ {A} → Hom A A
    comp : ∀ {A B C} → Hom A B → Hom B C → Hom A C

  field -- laws
    assoc     : ∀ {A B C D} {f : Hom A B} {g : Hom B C}{h : Hom C D} →
                comp f (comp g h) ≡ (comp (comp f g) h)
    identityˡ : ∀ {A B} {f : Hom A B} → comp id f ≡ f
    identityʳ : ∀ {A B} {f : Hom A B} → comp f id ≡ f
open Category

----------------------------
-- Functors
----------------------------

record Functor (C D : Category) : Set where
  eta-equality
  private
    module C = Category C
    module D = Category D

  field
    act : C.Obj → D.Obj
    fmap : ∀ {X Y} (f : C.Hom X Y) → D.Hom (act X) (act Y)

  field -- laws
    identity     : ∀ {X} → fmap (C.id {X}) ≡ D.id {act X}
    homomorphism : ∀ {X Y Z} {f : C.Hom X Y}{g : C.Hom Y Z} →
                   fmap (C.comp f g) ≡ D.comp (fmap f) (fmap g)
open Functor


-- How to prove Functors equal
eqFunctor : {C D : Category}{F G : Functor C D} ->
            (p : act F ≡ act G) ->
            (∀ {A B} → subst (λ z → Hom C A B -> Hom D (z A) (z B)) p (fmap F) ≡ (fmap G {A} {B})) ->
            F ≡ G
eqFunctor {G = G} refl q with iext (λ {A} → iext (λ {B} → q {A} {B}))
  where   iext = implicit-extensionality ext
... | refl = eqFunctor' {G = G} (implicit-extensionality ext λ {A} → uip _ _) (iext (iext (iext (iext (iext (uip _ _)))))) where
  iext = implicit-extensionality ext
  eqFunctor' : ∀ {C} {D} {G : Functor C D}
               {identity' identity'' : {A : Obj C} → fmap G {A} (Category.id C) ≡ Category.id D}
               {homomorphism' homomorphism'' : {X Y Z : Obj C} {f : Hom C X Y} {g : Hom C Y Z} → fmap G (comp C f g) ≡ comp D (fmap G f) (fmap G g)} →
               (_≡_ {A = ∀ {A} → fmap G {A} (Category.id C) ≡ Category.id D} identity' identity'') ->
               (_≡_ {A = {X Y Z : Obj C} {f : Hom C X Y} {g : Hom C Y Z} → fmap G (comp C f g) ≡ comp D (fmap G f) (fmap G g)} homomorphism' homomorphism'') ->
             _≡_ {A = Functor C D} (record { act = act G; fmap = fmap G; identity = identity'; homomorphism = homomorphism' })
                                   (record { act = act G; fmap = fmap G; identity = identity''; homomorphism = homomorphism'' })
  eqFunctor' refl refl = refl














----------------------------
-- Natural transformations
----------------------------

record NaturalTransformation {C D : Category}
                             (F G : Functor C D) : Set where
  eta-equality
  private
    module F = Functor F
    module G = Functor G
    module C = Category C
    module D = Category D

  field
    transform   : ∀ X → D.Hom (F.act X) (G.act X)
    natural     : ∀ X Y (f : C.Hom X Y) →
                  D.comp (F.fmap f) (transform Y) ≡ D.comp (transform X) (G.fmap f)
open NaturalTransformation

-- How to prove natural transformations equal
eqNatTrans : {C D : Category}{F G : Functor C D} ->
             (η ρ : NaturalTransformation F G) ->
             ((X : Category.Obj C) -> transform η X ≡ transform ρ X) ->
             η ≡ ρ
eqNatTrans {C} η ρ p with ext p
... | refl = eqNatTrans' η ρ refl (ext λ X → ext λ Y → ext λ f → uip _ _) where
  eqNatTrans' : {C D : Category}{F G : Functor C D} ->
                (η ρ : NaturalTransformation F G) ->
                (p : transform η ≡ transform ρ) ->
                subst (λ z → (X Y : Category.Obj C)(f : Category.Hom C X Y) → Category.comp D (fmap F f) (z Y) ≡ Category.comp D (z X) (fmap G f)) p (natural η) ≡ (natural ρ) ->
               η ≡ ρ
  eqNatTrans' η ρ refl refl = refl

----------------------------
-- The category of Sets
----------------------------

SET : Category
Category.Obj SET = Set
Category.Hom SET A B = A -> B
Category.id SET = Fun.id
Category.comp SET f g = g Fun.∘′ f
Category.assoc SET = refl
Category.identityˡ SET = refl
Category.identityʳ SET = refl
