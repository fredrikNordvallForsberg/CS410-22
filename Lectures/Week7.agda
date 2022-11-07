{-# OPTIONS --type-in-type #-}
module Lectures.Week7 where

open import Data.Nat hiding (_≤_)
open import Function using (_∘_)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Common.Category

open import Lectures.Week6 hiding (SET)

---------------------------------------------------------------------------
-- Monads, categorically
---------------------------------------------------------------------------

record Monad (C : Category) : Set where
  open Category C
  open Functor

  field
    functor : Functor C C

  private
    M = functor

  field
    returnNT : NaturalTransformation idFunctor M
    joinNT   : NaturalTransformation (compFunctor M M) M

  return = NaturalTransformation.transform returnNT
  join   = NaturalTransformation.transform joinNT

  field
    returnJoin : {X : Obj}    -> comp (return (act M X)) (join X) ≡ id
    mapReturnJoin : {X : Obj} -> comp (fmap M (return X)) (join X) ≡ id
    joinJoin : {X : Obj} -> comp (join (act M X)) (join X) ≡ comp (fmap M (join X)) (join X)

  open Functor M public

---------------------------------------------------------------------------
-- Hutton's Razor is a monad
---------------------------------------------------------------------------

module _ where

  open Monad
  open NaturalTransformation

  data Expr (X : Set) : Set where
    var : X -> Expr X
    num : ℕ -> Expr X
    _+E_ : Expr X -> Expr X -> Expr X

  mapExpr : {X Y : Set} -> (X -> Y) -> Expr X -> Expr Y
  mapExpr f (var x) = var (f x)
  mapExpr f (num n) = num n
  mapExpr f (e +E e') = mapExpr f e +E mapExpr f e'

  EXPR : Functor SET SET
  Functor.act EXPR = Expr
  Functor.fmap EXPR = mapExpr
  Functor.identity EXPR = ext lemma where
    lemma : {A : Set} -> (x : Expr A) → mapExpr (λ x₁ → x₁) x ≡ x
    lemma (var x) = refl
    lemma (num n) = refl
    lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')
  Functor.homomorphism EXPR {X} {f = f} {g} = ext lemma where
    lemma : (x : Expr X) → mapExpr (λ x₁ → g (f x₁)) x ≡ mapExpr g (mapExpr f x)
    lemma (var x) = refl
    lemma (num n) = refl
    lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')

  joinExpr : {X : Set} -> Expr (Expr X) -> Expr X
  joinExpr (var e) = e
  joinExpr (num n) = num n
  joinExpr (e +E e') = joinExpr e +E joinExpr e'

  EXPR-MONAD : Monad SET
  functor EXPR-MONAD = EXPR
  transform (returnNT EXPR-MONAD) X = var
  natural (returnNT EXPR-MONAD) X Y f = refl
  transform (joinNT EXPR-MONAD) X = joinExpr
  natural (joinNT EXPR-MONAD) X Y f = ext lemma
    where
      lemma : (x : Expr (Expr X)) → joinExpr (mapExpr (mapExpr f) x) ≡ mapExpr f (joinExpr x)
      lemma (var e) = refl
      lemma (num n) = refl
      lemma (ee +E ee') rewrite lemma ee | lemma ee' = refl
  returnJoin EXPR-MONAD = refl
  mapReturnJoin EXPR-MONAD = ext lemma
    where
      lemma : {X : Set} → (x : Expr X) → joinExpr (mapExpr var x) ≡ x
      lemma (var x) = refl
      lemma (num n) = refl
      lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')
  joinJoin EXPR-MONAD = ext lemma
    where
      lemma : {X : Set} -> (x : Expr (Expr (Expr X))) → joinExpr (joinExpr x) ≡ joinExpr (mapExpr joinExpr x)
      lemma (var x) = refl
      lemma (num n) = refl
      lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')

  bindExpr : {X Y : Set} -> (X -> Expr Y) -> Expr X -> Expr Y
  bindExpr f = joinExpr ∘ mapExpr f






---------------------------------------------------------------------------
-- Adding a bottom is a monad
---------------------------------------------------------------------------

module _ where

  open Preorder
  open MonotoneMap
  open Functor
  open Monad
  open NaturalTransformation

  data Lift (P : Set) : Set where
    η : P -> Lift P
    ⊥' : Lift P

  data Lift≤ (P : Preorder) : Lift (Carrier P) -> Lift (Carrier P) -> Set where
    η< : ∀ {p p'} → _≤_ P p p' -> Lift≤ P (η p) (η p')
    bottom : ∀ {x} → Lift≤ P ⊥' x

  Lift-reflexive : (P : Preorder) -> (x : Lift (Carrier P)) → Lift≤ P x x
  Lift-reflexive P (η x) = η< (reflexive P {x})
  Lift-reflexive P ⊥' = bottom

  Lift-transitive : (P : Preorder) -> {x y z : Lift (Carrier P)} →
                    Lift≤ P x y -> Lift≤ P y z -> Lift≤ P x z
  Lift-transitive P (η< p) (η< q) = η< (transitive P p q)
  Lift-transitive P bottom q = bottom
--  Lift-transitive P bottom bottom = {!!}

  mapLift : {X Y : Set} -> (f : X -> Y) -> Lift X -> Lift Y
  mapLift f (η x) = η (f x)
  mapLift f ⊥' = ⊥'

  LIFT : Functor PREORDER PREORDER
  Carrier (act LIFT P) = Lift (Carrier P)
  _≤_ (act LIFT P) = Lift≤ P
  reflexive (act LIFT P) = Lift-reflexive P _
  transitive (act LIFT P) = Lift-transitive P
  propositional (act LIFT P) (η< p) (η< q) = cong η< (propositional P p q)
  propositional (act LIFT P) bottom bottom = refl
  fun (fmap LIFT f) = mapLift (fun f)
  monotone (fmap LIFT f) (η x) (η y) (η< p) = η< (monotone f x y p)
  monotone (fmap LIFT f) ⊥' y bottom = bottom
  identity LIFT = eqMonotoneMap (ext λ { (η x) → refl ; ⊥' → refl })
  homomorphism LIFT = eqMonotoneMap (ext λ { (η x) → refl ; ⊥' → refl })

  LIFT-MONAD : Monad PREORDER
  functor LIFT-MONAD = LIFT
  fun (transform (returnNT LIFT-MONAD) P) = η
  monotone (transform (returnNT LIFT-MONAD) P) x y p = η< p
  natural (returnNT LIFT-MONAD) X Y f = eqMonotoneMap refl
  fun (transform (joinNT LIFT-MONAD) P) (η x) = x
  fun (transform (joinNT LIFT-MONAD) P) ⊥' = ⊥'
  monotone (transform (joinNT LIFT-MONAD) P) (η x) (η y) (η< p) = p
  monotone (transform (joinNT LIFT-MONAD) P) ⊥' y bottom = bottom
  -- We left the following as exercises in the lecture:
  natural (joinNT LIFT-MONAD) X Y f = eqMonotoneMap (ext λ { (η x) → refl ; ⊥' → refl })
  returnJoin LIFT-MONAD = eqMonotoneMap refl
  mapReturnJoin LIFT-MONAD = eqMonotoneMap (ext λ { (η x) → refl ; ⊥' → refl })
  joinJoin LIFT-MONAD = eqMonotoneMap (ext λ { (η x) → refl ; ⊥' → refl })
