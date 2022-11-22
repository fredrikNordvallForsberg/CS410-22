{-# OPTIONS --type-in-type #-}
module Lectures.Week10 where

open import Axiom.UniquenessOfIdentityProofs.WithK
open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Common.Category
open import Common.Category.Adjunctions
open import Common.Category.Solver

open import Lectures.Week6 hiding (SET)
open import Lectures.Week7
open import Lectures.Week8
open import Lectures.Week9

open Category
open NaturalTransformation
open Monad
open Adjunction



---------------------------------------
-- Pure things are trivially effectful
---------------------------------------

EmbedKleisli : {C : Category}(M : Monad C) -> Functor C (Kleisli M)
Functor.act (EmbedKleisli {C} M) X = X
Functor.fmap (EmbedKleisli {C} M) f = comp C f (return M _)
Functor.identity (EmbedKleisli {C} M) = identityˡ C
Functor.homomorphism (EmbedKleisli {C} M) {f = f} {g = g} = C ⊧begin
     < return M _ > ∘Syn (< g > ∘Syn < f >)
       ≡⟦ solveCat refl ⟧
     -[ < return M _ > ∘Syn < g > ]- ∘Syn < f >
       ≡⟦ reduced (rq (natural (returnNT M) _ _ g) , rd) ⟧
     -[ fmapSyn (functor M) < g > ∘Syn < return M _ > ]- ∘Syn < f >
        ≡⟦ solveCat refl ⟧
     -[ idSyn ]- ∘Syn fmapSyn (functor M) < g > ∘Syn < return M _ > ∘Syn < f >
        ≡⟦ reduced (rq (sym (mapReturnJoin M)) , rd , rd , rd) ⟧
     -[ < join M _ > ∘Syn fmapSyn (functor M) < return M _ > ]- ∘Syn fmapSyn (functor M) < g > ∘Syn < return M _ > ∘Syn < f >
        ≡⟦ solveCat refl ⟧
    (< join M _ > ∘Syn fmapSyn (functor M) (< return M _ > ∘Syn < g > )) ∘Syn (< return M _ > ∘Syn < f > )
      ⟦∎⟧

-----------------------------------
-- The bind presentation of monads
-----------------------------------

module _ {C : Category} (M : Monad C) where

  open NaturalTransformation

  bind : ∀ {X Y} → Hom C X (act M Y) -> Hom C (act M X) (act M Y)
  bind f = comp C (fmap M f) (join M _)

  -- m >>= return ≡ m
  bindReturn : ∀ {X} → bind (return M X) ≡ Category.id C
  bindReturn = mapReturnJoin M

  -- return a >>= f ≡ f a
  returnBind : ∀ {X Y}{f : Hom C X (act M Y)} → comp C (return M _) (bind f) ≡ f
  returnBind {f = f} = C ⊧begin
    (< join M _ > ∘Syn fmapSyn (functor M) < f >) ∘Syn < return M _ >
      ≡⟦ solveCat refl ⟧
    < join M _ > ∘Syn -[ fmapSyn (functor M) < f > ∘Syn < return M _ > ]-
      ≡⟦ reduced (rd , rq (sym (natural (returnNT M) _ _ f))) ⟧
    < join M _ > ∘Syn -[ < return M _ > ∘Syn < f > ]-
      ≡⟦ solveCat refl ⟧
    -[ < join M _ > ∘Syn < return M _ > ]- ∘Syn < f >
      ≡⟦ reduced (rq (returnJoin M) , rd) ⟧
    -[ idSyn ]- ∘Syn < f >
      ≡⟦ solveCat refl ⟧
    < f >
      ⟦∎⟧

  -- (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)
  bindBind : ∀ {X Y Z}{f : Hom C X (act M Y)}{g : Hom C Y (act M Z)} →
             bind (comp C f (bind g)) ≡ comp C (bind f) (bind g)
  bindBind {f = f} {g} = C ⊧begin
    < join M _ > ∘Syn fmapSyn (functor M) ((< join M _ > ∘Syn fmapSyn (functor M) < g >) ∘Syn < f >)
      ≡⟦ solveCat refl ⟧
    -[ < join M _ > ∘Syn fmapSyn (functor M) < join M _ > ]- ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < g >) ∘Syn fmapSyn (functor M) < f >
      ≡⟦ reduced (rq (sym (joinJoin M)) , (rd , rd)) ⟧
    -[ < join M _ > ∘Syn  < join M _ > ]- ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < g >) ∘Syn fmapSyn (functor M) < f >
      ≡⟦ solveCat refl ⟧
    < join M _ > ∘Syn -[ < join M _ > ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < g >) ]- ∘Syn fmapSyn (functor M) < f >
      ≡⟦ reduced (rd , rq (natural (joinNT M) _ _ g) , rd) ⟧
    < join M _ > ∘Syn -[ fmapSyn (functor M) < g > ∘Syn < join M _ > ]- ∘Syn fmapSyn (functor M) < f >
      ≡⟦ solveCat refl ⟧
    (< join M _ > ∘Syn fmapSyn (functor M) < g >) ∘Syn (< join M _ > ∘Syn fmapSyn (functor M) < f >)
      ⟦∎⟧


----------------------
-- Getting back again
----------------------


ForgetKleisli : {C : Category}(M : Monad C) -> Functor (Kleisli M) C
Functor.act (ForgetKleisli {C} M) X = act M X
Functor.fmap (ForgetKleisli {C} M) f = bind M f
Functor.identity (ForgetKleisli {C} M) = bindReturn M
Functor.homomorphism (ForgetKleisli {C} M) = bindBind M


kleisliAdjunction : {C : Category}(M : Monad C) -> Adjunction (EmbedKleisli M) (ForgetKleisli M)
to (kleisliAdjunction M) f = f
from (kleisliAdjunction M) g = g
left-inverse-of (kleisliAdjunction M) h = refl
right-inverse-of (kleisliAdjunction M) h = refl
to-natural (kleisliAdjunction {C} M) f g = ext λ h → C ⊧begin
  compSyn < f > (compSyn < h > (compSyn (fmapSyn (functor M) < g >) < join M _ >))
    ≡⟦ solveCat refl ⟧
  -[ idSyn ]- ∘Syn < join M _ > ∘Syn fmapSyn (functor M) < g > ∘Syn < h > ∘Syn < f >
    ≡⟦ reduced (rq (sym (returnJoin M)) , rd , rd , rd , rd) ⟧
  -[ < join M _ > ∘Syn < return M _ > ]- ∘Syn < join M _ > ∘Syn fmapSyn (functor M) < g > ∘Syn < h > ∘Syn < f >
    ≡⟦ solveCat refl ⟧
  < join M _ > ∘Syn -[ < return M _ > ∘Syn < join M _ > ]- ∘Syn fmapSyn (functor M) < g > ∘Syn < h > ∘Syn < f >
    ≡⟦ reduced (rd , rq (natural (returnNT M) _ _ _) , rd , rd , rd) ⟧
  < join M _ > ∘Syn -[ fmapSyn (functor M) < join M _ > ∘Syn < return M _ > ]- ∘Syn fmapSyn (functor M) < g > ∘Syn < h > ∘Syn < f >
    ≡⟦ solveCat refl ⟧
  < join M _ > ∘Syn fmapSyn (functor M) < join M _ > ∘Syn -[ < return M _ > ∘Syn fmapSyn (functor M) < g > ]- ∘Syn < h > ∘Syn < f >
    ≡⟦ reduced (rd , rd , rq (natural (returnNT M) _ _ _) , rd , rd) ⟧
  < join M _ > ∘Syn fmapSyn (functor M) < join M _ > ∘Syn -[ fmapSyn (functor M) (fmapSyn (functor M) < g >) ∘Syn < return M _ > ]- ∘Syn < h > ∘Syn < f >
    ≡⟦ solveCat refl ⟧
  < join M _ > ∘Syn fmapSyn (functor M) < join M _ > ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < g >) ∘Syn -[ < return M _ > ∘Syn < h > ]- ∘Syn < f >
    ≡⟦ reduced (rd , rd , rd , rq (natural (returnNT M) _ _ _) , rd) ⟧
  < join M _ > ∘Syn fmapSyn (functor M) < join M _ > ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < g >) ∘Syn -[ fmapSyn (functor M) < h > ∘Syn < return M _ > ]- ∘Syn < f >
    ≡⟦ solveCat refl ⟧
  compSyn (compSyn < f > < return M _ >)
      (compSyn (fmapSyn (functor M) (compSyn < h > (compSyn (fmapSyn (functor M) < g >) < join M _ >))) < join M _ >)
    ⟦∎⟧

----------------------------------------------------------------
-- Every monad arises from (for example) its Kleisli adjunction
----------------------------------------------------------------

-- equality of monads
eqMonad : {C : Category} (M N : Monad C) →
          (p : act M ≡ act N) →
          (∀ {A B} → subst (λ z → Hom C A B -> Hom C (z A) (z B)) p (fmap M) ≡ (fmap N {A} {B})) →
          ((X : Obj C) → subst (λ z → Hom C (Functor.act {C = C} idFunctor X) (z X)) p (return M X) ≡ return N X) →
          ((X : Obj C) → subst (λ z → Hom C (z (z X)) (z X)) p (join M X) ≡ join N X) →
          M ≡ N
eqMonad {C} M N refl p q r with eqFunctor {C = C} {F = functor M} {G = functor N} refl p
eqMonad {C} M N refl p q r | refl with eqNatTrans (returnNT M) (returnNT N) q | eqNatTrans (joinNT M) (joinNT N) r
eqMonad {C} M N refl p q r | refl | refl | refl = eqMonad' (iext (uip _ _)) (iext (uip _ _)) (iext (uip _ _))
  where
    iext = implicit-extensionality ext
    eqMonad' :
             {returnNT : NaturalTransformation idFunctor (functor N)}
             {joinNT : NaturalTransformation (compFunctor (functor N) (functor N)) (functor N)}
             {returnJoin₁ : {X : Obj C} → comp C (transform returnNT (act N X)) (transform joinNT X) ≡ id C}
             {mapReturnJoin₁ : {X : Obj C} → comp C (fmap N (transform returnNT X)) (transform joinNT X) ≡ id C}
             {joinJoin₁ : {X : Obj C} → comp C (transform joinNT (act N X)) (transform joinNT X) ≡ comp C (fmap N (transform joinNT X)) (transform joinNT X)}
             {returnJoin₂ : {X : Obj C} → comp C (transform returnNT (act N X)) (transform joinNT X) ≡ id C}
             {mapReturnJoin₂ : {X : Obj C} → comp C (fmap N (transform returnNT X)) (transform joinNT X) ≡ id C}
             {joinJoin₂ : {X : Obj C} → comp C (transform joinNT (act N X)) (transform joinNT X) ≡ comp C (fmap N (transform joinNT X)) (transform joinNT X)} →
             _≡_ {A = {X : Obj C} → comp C (transform returnNT (act N X)) (transform joinNT X) ≡ id C} returnJoin₁ returnJoin₂ →
             _≡_ {A = {X : Obj C} → comp C (fmap N (transform returnNT X)) (transform joinNT X) ≡ id C} mapReturnJoin₁ mapReturnJoin₂ →
             _≡_ {A = {X : Obj C} → comp C (transform joinNT (act N X)) (transform joinNT X) ≡ comp C (fmap N (transform joinNT X)) (transform joinNT X)} joinJoin₁ joinJoin₂ →
           record
           { functor = functor N
           ; returnNT = returnNT
           ; joinNT = joinNT
           ; returnJoin = returnJoin₂
           ; mapReturnJoin = mapReturnJoin₂
           ; joinJoin = joinJoin₂
           }
           ≡
           record
           { functor = functor N
           ; returnNT = returnNT
           ; joinNT = joinNT
           ; returnJoin = returnJoin₁
           ; mapReturnJoin = mapReturnJoin₁
           ; joinJoin = joinJoin₁
           }
    eqMonad' refl refl refl = refl



completeness : {C : Category}(M : Monad C) →
               M ≡ (monadFromAdj _ _ _ _ (kleisliAdjunction M))
completeness {C} M = eqMonad _ _ refl (ext (completenessFmap M)) (completenessReturn M) (completenessJoin M)
  where
    completenessFmap : {C : Category}(M : Monad C) →
                       {X Y : Obj C}(h : Hom C X Y) → fmap M h ≡ fmap (monadFromAdj _ _ _ _ (kleisliAdjunction M)) h
    completenessFmap {C} M {X} h = C ⊧begin
      fmapSyn (functor M) < h >
        ≡⟦ solveCat refl ⟧
      fmapSyn (functor M) < h > ；Syn -[ idSyn ]-
        ≡⟦ reduced (rq (sym (mapReturnJoin M)) , rd) ⟧
      fmapSyn (functor M) < h > ；Syn -[ fmapSyn (functor M) < return M _ > ；Syn < join M _ > ]-
        ≡⟦ solveCat refl ⟧
      compSyn (fmapSyn (functor M) (compSyn < h > < return M _ >)) < join M _ >
        ⟦∎⟧

    completenessReturn : {C : Category}(M : Monad C) → (X : Obj C) →
                         return M X ≡ return (monadFromAdj _ _ _ _ (kleisliAdjunction M)) X
    completenessReturn {C} M X = refl


