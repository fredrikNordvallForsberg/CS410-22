{-# OPTIONS --type-in-type #-}
module Lectures.Week9 where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Axiom.Extensionality.Propositional

open import Lectures.Week6 hiding (SET)
open import Lectures.Week7
open import Lectures.Week8


open import Common.Category
open import Common.Category.Adjunctions
open import Common.Category.Solver

---------------------------------------------------------------------------
-- Free categories
---------------------------------------------------------------------------

open Category
open Functor
open Adjunction

REL : Category
Obj REL = Σ[ A ∈ Set ] (A → A → Set)
Hom REL (A , R) (A' , R')= Σ[ f ∈ (A → A') ] (∀{a b} → R a b → R' (f a) (f b))
id REL = (id SET) , λ p → p
comp REL (f , p) (g , q)  = (comp SET f g) , λ x → q (p x)
assoc REL = refl
identityˡ REL = refl
identityʳ REL = refl



forgetCategory : Functor CAT REL
act forgetCategory C = (Obj C) , (Hom C)
fmap forgetCategory F = (act F) , (fmap F)
identity forgetCategory = refl
homomorphism forgetCategory = refl



data Star {A : Set}(R : A -> A -> Set) : A -> A -> Set where
  ε : ∀ {a} → Star R a a
  _∷_ : ∀ {a b c} → R a b -> Star R b c -> Star R a c

_++S_ : {A : Set}{R : A -> A -> Set} -> {a b c  : A} -> Star R a b -> Star R b c -> Star R a c
ε ++S ys = ys
(x ∷ xs) ++S ys = x ∷ (xs ++S ys)

assoc-++S : {A : Set}{R : A -> A -> Set} ->
          ∀{a b c d}(f : Star R a b)(g : Star R b c)(h : Star R c d) ->
          f ++S (g ++S h) ≡ (f ++S g) ++S h
assoc-++S ε g h = refl
assoc-++S (x ∷ f) g h = cong (x ∷_) (assoc-++S f g h)

++S-identityʳ : {A : Set}{R : A -> A -> Set}{a b : A}(f : Star R a b) → f ++S ε ≡ f
++S-identityʳ ε = refl
++S-identityʳ (x ∷ f) = cong (x ∷_) (++S-identityʳ f)

mapS : {A B : Set}{R : A -> A -> Set}{Q : B -> B -> Set} ->
       (f : A -> B)(p : ∀ a a' → R a a' -> Q (f a) (f a')) ->
       {a a' : A} -> Star R a a' -> Star Q (f a) (f a')
mapS f p ε = ε
mapS f p (x ∷ xs) = p _ _ x ∷ mapS f p xs

mapS-++ : {A B : Set}{R : A -> A -> Set}{Q : B -> B -> Set} ->
          (f : A -> B)(p : ∀ a a' → R a a' -> Q (f a) (f a')) ->
          {a b c : A} -> (xs : Star R a b)(ys : Star R b c) ->
          mapS {Q = Q} f p (xs ++S ys) ≡ mapS f p xs ++S mapS f p ys
mapS-++ f p ε ys = refl
mapS-++ f p (x ∷ xs) ys = cong (p _ _ x ∷_) (mapS-++ f p xs ys)

mapS-id : ∀ {A R}{a b : A}(xs : Star R a b) -> mapS (id SET) (λ a b r → r) xs ≡ xs
mapS-id ε = refl
mapS-id (x ∷ xs) = cong (x ∷_) (mapS-id xs)

mapS-∘ : {A A' A'' : Set}
         {R : A -> A -> Set}{R' : A' -> A' -> Set}{R'' : A'' -> A'' -> Set} ->
         (f : A -> A')(p : ∀ a a' → R a a' -> R' (f a) (f a')) ->
         (f' : A' -> A'')(p' : ∀ a a' → R' a a' -> R'' (f' a) (f' a')) ->
         {a b : A} -> (xs : Star R a b) ->
         mapS {Q = R''} (comp SET f f') (λ a b r → p' _ _ (p _ _ r)) xs ≡ mapS f' p' (mapS f p xs)
mapS-∘ f p f' p' ε = refl
mapS-∘ f p f' p' (x ∷ xs) = cong (p' (f _) (f _) (p _ _ x) ∷_) (mapS-∘ f p f' p' xs)



freeCategory : Functor REL CAT
Obj (act freeCategory (A , R)) = A
Hom (act freeCategory (A , R)) = Star R
id (act freeCategory (A , R)) = ε
comp (act freeCategory (A , R)) = _++S_
assoc (act freeCategory (A , R)) {f = f} {g} {h} = assoc-++S f g h
identityˡ (act freeCategory (A , R)) = refl
identityʳ (act freeCategory (A , R)) = ++S-identityʳ _
act (fmap freeCategory (f , p)) = f
fmap (fmap freeCategory (f , p)) = mapS f (λ _ _ → p)
identity (fmap freeCategory (f , p)) = refl
homomorphism (fmap freeCategory (f , p)) {g = g} = mapS-++ f _ _ g
identity freeCategory = eqFunctor refl (ext mapS-id)
homomorphism freeCategory = eqFunctor refl (ext (mapS-∘ _ _ _ _ ))

foldStar : {A : Set}{R : A → A → Set}(B : Category) →
           (f : A → Obj B)(p :{a b : A} → R a b → Hom B (f a) (f b)) →
           {X Y : A} → Star R X Y → Hom B (f X) (f Y)
foldStar B f p ε = id B
foldStar B f p (r ∷ rs) = comp B (p r) (foldStar B f p rs)

freeCatisFree : Adjunction freeCategory forgetCategory
to freeCatisFree {A , R} {B} F = act F , λ r → fmap F (r ∷ ε)
act (from freeCatisFree {A , R} (f , p)) = f
fmap (from freeCatisFree {A , R} {B} (f , p)) = foldStar B f p
identity (from freeCatisFree (f , p)) = refl
homomorphism (from freeCatisFree {A , R} {B} (f , p)) {f = ε} = sym (identityˡ B)
homomorphism (from freeCatisFree {A , R} {B} (f , p)) {f = r ∷ rs} =
  trans (cong (comp B (p r)) (homomorphism (from freeCatisFree {A , R} {B} (f , p)) {f = rs})) (assoc B)
left-inverse-of freeCatisFree {A , R} {B}  F = eqFunctor refl (ext lemma)
  where
    lemma : ∀ {A₁ B₁} → (x : Star R A₁ B₁) → foldStar B (act F) (λ r → fmap F (r ∷ ε)) x ≡ fmap F x
    lemma ε = sym (identity F)
    lemma (x ∷ rs) rewrite lemma rs = sym (homomorphism F)
right-inverse-of freeCatisFree {A , R} {B}  (f , p) = cong (f ,_) (iext (iext (ext λ r → identityʳ B)))
 where
   iext = implicit-extensionality ext
to-natural freeCatisFree {A , R} {B} f g = refl

---------------------------------------------------------------------------
-- Monads from adjunctions
---------------------------------------------------------------------------

open Monad
open NaturalTransformation


monadFromAdj : (C D : Category)(F : Functor C D)(G : Functor D C) ->
               Adjunction F G -> Monad C
functor (monadFromAdj C D F G adj) = comp CAT F G
transform (returnNT (monadFromAdj C D F G adj)) X = to adj (id D)
natural (returnNT (monadFromAdj C D F G adj)) X Y f = trans (to-natural₁ adj f) (sym (to-natural₂ adj (fmap F f)))
transform (joinNT (monadFromAdj C D F G adj)) X = fmap G (from adj (id C))
natural (joinNT (monadFromAdj C D F G adj)) X Y f = C ⊧begin
 fmapSyn G < from adj (id C) >  ∘Syn fmapSyn G (fmapSyn F (fmapSyn G (fmapSyn F < f > )))
   ≡⟦ solveCat refl ⟧
 fmapSyn G (< from adj (id C) > ∘Syn fmapSyn F (fmapSyn G (fmapSyn F < f > )))
   ≡⟦ reduced (rq (cong (fmap G) (trans (from-natural₁ adj (fmap G (fmap F f))) (sym (from-natural₂ adj (fmap F f)))))) ⟧
 fmapSyn G (fmapSyn F < f > ∘Syn < from adj (id C) >)
   ≡⟦ solveCat refl ⟧
 fmapSyn G (fmapSyn F < f >) ∘Syn fmapSyn G < from adj (id C) >
   ⟦∎⟧
returnJoin (monadFromAdj C D F G adj) = C ⊧begin
  -[ fmapSyn G < from adj (id C) > ∘Syn < to adj (id D) > ]-
    ≡⟦ reduced (rq (to-natural₂ adj (from adj (id C)))) ⟧
  < to adj (from adj (id C)) >
    ≡⟦ reduced (rq (right-inverse-of adj (id C))) ⟧
  idSyn
    ⟦∎⟧
mapReturnJoin (monadFromAdj C D F G adj) = C ⊧begin
  fmapSyn G < from adj (id C) > ∘Syn fmapSyn G (fmapSyn F < to adj (id D) >)
    ≡⟦ solveCat refl ⟧
  fmapSyn G (< from adj (id C) > ∘Syn fmapSyn F < to adj (id D) >)
    ≡⟦ reduced (rq (cong (fmap G) (trans (from-natural₁ adj (to adj (id D))) (left-inverse-of adj (id D))))) ⟧
  fmapSyn G idSyn
    ≡⟦ solveCat refl ⟧
  idSyn
    ⟦∎⟧
joinJoin (monadFromAdj C D F G adj) = C ⊧begin
  fmapSyn G < from adj (id C) > ∘Syn fmapSyn G < from adj (id C) >
    ≡⟦ solveCat refl ⟧
  fmapSyn G (< from adj (id C) > ∘Syn < from adj (id C) >)
    ≡⟦ reduced (rq (cong (fmap G) (D ⊧begin
         -[ < from adj (id C) > ∘Syn < from adj (id C) > ]-
           ≡⟦ reduced (rq (from-natural₂ adj (from adj (id C)))) ⟧
         < from adj (fmap G (from adj (id C))) >
            ≡⟦ reduced (rq (sym (from-natural₁ adj (fmap G (from adj (id C)))))) ⟧
         < from adj (id C) > ∘Syn fmapSyn F (fmapSyn G < from adj (id C) >)
           ⟦∎⟧))) ⟧
  fmapSyn G (< from adj (id C) > ∘Syn fmapSyn F (fmapSyn G < from adj (id C) >))
      ≡⟦ solveCat refl ⟧
  fmapSyn G < from adj (id C) > ∘Syn fmapSyn G (fmapSyn F (fmapSyn G < from adj (id C) >))
    ⟦∎⟧

