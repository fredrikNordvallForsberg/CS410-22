{-# OPTIONS --type-in-type #-}
module Common.Category.Adjunctions where

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Function as Fun using (_∘′_)

open import Common.Category
open import Common.Category.Solver

----------------------------
-- Adjunctions
----------------------------

record Adjunction {C D : Category}
                  (F : Functor C D)
                  (G : Functor D C) : Set where

  open Category
  open Functor
  open NaturalTransformation

  field
    to   : {X : Obj C}{B : Obj D} -> Hom D (act F X)        B  -> Hom C X         (act G B)
    from : {X : Obj C}{B : Obj D} -> Hom C X         (act G B) -> Hom D (act F X)        B
    left-inverse-of : ∀ {X B} →  (h : Hom D (act F X) B) -> from (to h) ≡ h
    right-inverse-of : ∀ {X B} → (k : Hom C X (act G B)) -> to (from k) ≡ k

    to-natural : {X X' : Obj C}{B B' : Obj D} (f : Hom C X' X)(g : Hom D B B') ->
                   (λ h → comp C f (comp C h (fmap G g))) ∘′ (to {X} {B})
                     ≡
                   (to {X'} {B'}) ∘′ (λ k → comp D (fmap F f) (comp D k g))

  from-natural : {X X' : Obj C}{B B' : Obj D} (f : Hom C X' X)(g : Hom D B B') ->
                 (λ k → comp D (fmap F f) (comp D k g)) ∘′ (from {X} {B})
                   ≡
                 (from {X'} {B'}) ∘′ (λ h → comp C f (comp C h (fmap G g)))
  from-natural f g = SET ⊧begin
    < (λ k → comp D (fmap F f) (comp D k g)) > ∘Syn < from >
      ≡⟦ solveCat refl ⟧
    -[ idSyn ]- ∘Syn < (λ k → comp D (fmap F f) (comp D k g)) > ∘Syn < from >
      ≡⟦ reduced (rq (sym (ext left-inverse-of)) , rd , rd) ⟧
   -[ < from > ∘Syn < to > ]- ∘Syn < (λ k → comp D (fmap F f) (comp D k g)) >  ∘Syn < from >
      ≡⟦ solveCat refl ⟧
    < from > ∘Syn -[ < to > ∘Syn < (λ k → comp D (fmap F f) (comp D k g)) > ]- ∘Syn < from >
      ≡⟦ reduced (rd , rq (sym (to-natural f g)) , rd) ⟧
    < from > ∘Syn -[ < (λ h → comp C f (comp C h (fmap G g))) > ∘Syn < to > ]- ∘Syn < from >
      ≡⟦ solveCat refl ⟧
    < from > ∘Syn < (λ h → comp C f (comp C h (fmap G g))) > ∘Syn -[ < to > ∘Syn < from > ]-
      ≡⟦ reduced (rd , rd , rq (ext right-inverse-of))  ⟧
    < from > ∘Syn < (λ h → comp C f (comp C h (fmap G g))) > ∘Syn -[ idSyn ]-
      ≡⟦ solveCat refl ⟧
    < from > ∘Syn < (λ h → comp C f (comp C h (fmap G g))) >
      ⟦∎⟧

---------------------------------------------------------------------------
-- Special cases of naturality (not very insightful)
---------------------------------------------------------------------------

open Category
open Functor
open Adjunction

to-natural₁ : {C D : Category}{F : Functor C D}{G : Functor D C} -> (adj : Adjunction F G) ->
              {X X' : Obj C}(f : Hom C X' X) ->
             comp C f (to adj (id D)) ≡ to adj (fmap F f)
to-natural₁ {C} {D} {F} {G} adj f = C ⊧begin
  < to adj (id D) > ∘Syn < f >
    ≡⟦ solveCat refl ⟧
  -[ (fmapSyn G idSyn ∘Syn < to adj (id D) >) ∘Syn < f > ]-
    ≡⟦ reduced (rq (cong-app (to-natural adj f (id D)) (id D))) ⟧
  < to adj (comp D (fmap F f) (comp D (id D) (id D))) >
    ≡⟦ reduced (rq (cong (to adj) (eqArr (solveCat {d = compSyn (fmapSyn F < f >) (compSyn idSyn idSyn)} {d' = fmapSyn F < f >} refl)))) ⟧
  < to adj (fmap F f) >
    ⟦∎⟧

to-natural₂ : {C D : Category}{F : Functor C D}{G : Functor D C} -> (adj : Adjunction F G) ->
                 {X : Obj C}{B' : Obj D}(g : Hom D (act F X) B') ->
                   comp C (to adj (id D)) (fmap G g) ≡ to adj g
to-natural₂ {C} {D} {F} {G} adj g = C ⊧begin
  fmapSyn G < g > ∘Syn < to adj (id D) >
    ≡⟦ solveCat refl ⟧
  (fmapSyn G < g > ∘Syn < to adj (id D) >) ∘Syn idSyn
    ≡⟦ reduced (rq (cong-app (to-natural adj (id C) g) (id D))) ⟧
  < to adj (comp D (fmap F (id C)) (comp D (id D) g)) >
    ≡⟦ reduced (rq (cong (to adj) ((eqArr (solveCat {d = compSyn (fmapSyn F idSyn) (compSyn idSyn < g >)} {d' = < g >} refl))))) ⟧
  < to adj g >
    ⟦∎⟧

from-natural₁ : {C D : Category}{F : Functor C D}{G : Functor D C} -> (adj : Adjunction F G) ->
                {X : Obj C}{B' : Obj D}(f : Hom C X (act G B')) ->
                 comp D (fmap F f) (from adj (id C)) ≡ from adj f
from-natural₁ {C} {D} {F} {G} adj f = D ⊧begin
   < from adj (id C) > ∘Syn fmapSyn F < f >
     ≡⟦ solveCat refl ⟧
  -[ (idSyn ∘Syn  < from adj (id C) >) ∘Syn fmapSyn F < f > ]-
     ≡⟦ reduced (rq (cong-app (from-natural {C} {D} {F} {G} adj f (id D)) (id C))) ⟧
   < from adj (comp C f (comp C (id C) (fmap G (id D)))) >
     ≡⟦ reduced (rq (cong (from adj) (eqArr (solveCat {d = compSyn < f > (compSyn idSyn (fmapSyn G idSyn))} {< f >} refl) ))) ⟧
   < from adj f >
     ⟦∎⟧

from-natural₂ : {C D : Category}{F : Functor C D}{G : Functor D C} -> (adj : Adjunction F G) ->
                {B B' : Obj D}(g : Hom D B B') ->
                 comp D (from adj (id C)) g ≡ from adj (fmap G g)
from-natural₂ {C} {D} {F} {G} adj g = D ⊧begin
  < g > ∘Syn < from adj (id C) >
    ≡⟦ solveCat refl ⟧
  -[ (< g > ∘Syn < from adj (id C) >) ∘Syn fmapSyn F idSyn ]-
    ≡⟦ reduced (rq (cong-app (from-natural adj (id C) g) (id C))) ⟧
  < from adj (comp C (id C) (comp C (id C) (fmap G g))) >
    ≡⟦ reduced (rq (cong (from adj) (eqArr (solveCat {d = compSyn idSyn (compSyn idSyn (fmapSyn G < g >))} {fmapSyn G < g >} refl)))) ⟧
  < from adj (fmap G g) >
    ⟦∎⟧
