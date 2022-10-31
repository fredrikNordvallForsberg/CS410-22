{-# OPTIONS --type-in-type #-}
module Lectures.Week7 where

open import Data.Nat hiding (_≤_)
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality

open import Common.Category

open Category

open import Lectures.Week6 hiding (SET)

open Functor

{-

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
    returnJoin : {X : Obj C}    -> comp C (return (act M X)) (join X) ≡ id C
    mapReturnJoin : {X : Obj C} -> comp C (fmap M (return X)) (join X) ≡ id C
    joinJoin : {X : Obj C} -> comp C (join (act M X)) (join X) ≡ comp C (fmap M (join X)) (join X)

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
  mapExpr f (num x) = num x
  mapExpr f (e +E e') = mapExpr f e +E mapExpr f e'

  EXPR : Functor SET SET
  Functor.act EXPR = Expr
  Functor.fmap EXPR = mapExpr
  Functor.identity EXPR = ext lemma where
    lemma : {A : Set} -> (x : Expr A) → mapExpr (λ x₁ → x₁) x ≡ x
    lemma (var x) = refl
    lemma (num x) = refl
    lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')
  Functor.homomorphism EXPR {X} {f = f} {g} = ext lemma where
    lemma : (x : Expr X) → mapExpr (λ x₁ → g (f x₁)) x ≡ mapExpr g (mapExpr f x)
    lemma (var x) = refl
    lemma (num x) = refl
    lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')

  joinExpr : {X : Set} -> Expr (Expr X) -> Expr X
  joinExpr e = {!!}

  EXPR-MONAD : Monad SET
  EXPR-MONAD = {!!}

  bindExpr : {X Y : Set} -> (X -> Expr Y) -> Expr X -> Expr Y
  bindExpr f = joinExpr ∘ mapExpr f

---------------------------------------------------------------------------
-- Adding a bottom is a monad
---------------------------------------------------------------------------

module _ where

  open Preorder
  open MonotoneMap
  open Monad
  open NaturalTransformation

  data Lift (P : Set) : Set where
    η : P -> Lift P
    ⊥' : Lift P

  data Lift≤ (P : Preorder) : Lift (Carrier P) -> Lift (Carrier P) -> Set where
    η< : ∀ {p p'} → _≤_ P p p' -> Lift≤ P (η p) (η p')
    bottom : ∀ {x} → Lift≤ P ⊥' x

  Lift-reflexive : (P : Preorder) -> (x : Lift (Carrier P)) → Lift≤ P x x
  Lift-reflexive P = {!!}

  Lift-transitive : (P : Preorder) -> {x y z : Lift (Carrier P)} →  Lift≤ P x y -> Lift≤ P y z -> Lift≤ P x z
  Lift-transitive P = {!!}

  mapLift : {X Y : Set} -> (f : X -> Y) -> Lift X -> Lift Y
  mapLift f (η x) = η (f x)
  mapLift f ⊥' = ⊥'

  LIFT : Functor PREORDER PREORDER
  LIFT = {!!}

  LIFT-MONAD : Monad PREORDER
  LIFT-MONAD = {!!}
-}
