module Common.Category.Solver where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
open import Function hiding (id)

open import Common.Category

open Category
open Functor


-- "syntactic" morphisms
data SynHom (C : Category) : Obj C -> Obj C -> Set
  where
    <_> : forall {S T} -> Hom C S T -> SynHom C S T
    idSyn : ∀ {T} -> SynHom C T T
    compSyn : ∀ {R S T} -> SynHom C R S -> SynHom C S T -> SynHom C R T
    fmapSyn : ∀ {C' S' T'} → (F : Functor C' C) -> SynHom C' S' T' ->
               SynHom C (act F S') (act F T')
    -[_]- : ∀ {S T} -> SynHom C S T -> SynHom C S T

_∘Syn_ : ∀ {C R S T} -> SynHom C S T -> SynHom C R S -> SynHom C R T
f ∘Syn g = compSyn g f

_；Syn_ : ∀ {C R S T} -> SynHom C R S -> SynHom C S T -> SynHom C R T
_；Syn_ = compSyn

infixl 4 _；Syn_
infixr 9 _∘Syn_


-- the morphisms the syntax denotes
⟦_⟧Sy : ∀ {C S T} → SynHom C S T -> Hom C S T
⟦ < f > ⟧Sy = f
⟦_⟧Sy {C = C} idSyn = id C
⟦_⟧Sy {C = C} (compSyn f g) = comp C ⟦ f ⟧Sy ⟦ g ⟧Sy
⟦ fmapSyn F f ⟧Sy = fmap F ⟦ f ⟧Sy
⟦ -[ f ]- ⟧Sy = ⟦ f ⟧Sy

-- iterated functor application
data MapPile (C : Category) : Obj C -> Obj C -> Set
  where
    <_> : forall {S T} -> Hom C S T -> MapPile C S T
    fmapSyn : ∀ {C' S' T'} → (F : Functor C' C) -> MapPile C' S' T' ->
               MapPile C (act F S') (act F T')

⟦_⟧MP : ∀ {C S T} → MapPile C S T -> Hom C S T
⟦ < f > ⟧MP = f
⟦ fmapSyn F m ⟧MP = fmap F ⟦ m ⟧MP

⟦_⟧MPs : ∀ {C S T} → Star (MapPile C) S T -> Hom C S T
⟦_⟧MPs {C} ε = id C
⟦_⟧MPs {C} (m ◅ ms) = comp C ⟦ m ⟧MP ⟦ ms ⟧MPs

-- normalise a syntactic morphism
normSyn : ∀ {C S T} → SynHom C S T -> Star (MapPile C) S T
normSyn < f > = return < f >
normSyn idSyn = ε
normSyn (compSyn d d') = normSyn d ◅◅ normSyn d'
normSyn (fmapSyn F d) = kleisliStar (act F) (return ∘′ fmapSyn F) (normSyn d)
normSyn -[ d ]- = normSyn d

normSynSound : ∀ {C S T} → (d : SynHom C S T) -> ⟦ d ⟧Sy ≡ ⟦ normSyn d ⟧MPs
normSynSound {C} < f > = sym (identityʳ C {f = f})
normSynSound idSyn = refl
normSynSound {C} (compSyn d d') = begin
  comp C ⟦ d ⟧Sy ⟦ d' ⟧Sy
    ≡⟨ cong₂ (comp C) (normSynSound d) (normSynSound d') ⟩
  comp C ⟦ normSyn d ⟧MPs ⟦ normSyn d' ⟧MPs
    ≡˘⟨ MPsLemma (normSyn d) (normSyn d') ⟩
  ⟦ normSyn d ◅◅ normSyn d' ⟧MPs
    ∎ where
        open ≡-Reasoning
        MPsLemma : ∀ {C S T U} →
                   (xs : Star (MapPile C) S T)(ys : Star (MapPile C) T U) ->
                   ⟦ xs ◅◅ ys ⟧MPs ≡ comp C ⟦ xs ⟧MPs ⟦ ys ⟧MPs
        MPsLemma {C} ε ys = sym (identityˡ C)
        MPsLemma {C} (x ◅ xs) ys rewrite MPsLemma xs ys = assoc C

normSynSound {C} (fmapSyn F d) = begin
  fmap F ⟦ d ⟧Sy
    ≡⟨ cong (fmap F) (normSynSound d) ⟩
  fmap F ⟦ normSyn d ⟧MPs
    ≡⟨ kleisliStarLemma F (normSyn d) ⟩
  ⟦ kleisliStar (act F) (return ∘′ fmapSyn F) (normSyn d) ⟧MPs
    ∎ where
        open ≡-Reasoning
        kleisliStarLemma : ∀ {C C' S' T'} (F : Functor C' C) ->
                           (ms : Star (MapPile C') S' T') ->
                           fmap F ⟦ ms ⟧MPs ≡
                             ⟦ kleisliStar (act F) (return ∘′ fmapSyn F) ms ⟧MPs
        kleisliStarLemma F ε = identity F
        kleisliStarLemma F (m ◅ ms) rewrite sym (kleisliStarLemma F ms)
          = homomorphism F
normSynSound -[ d ]- = normSynSound d

-- to help with type inference
record _≡Hom_ {C S T} (f g : SynHom C S T) : Set where
    constructor homEq
    field
      eqArr : ⟦ f ⟧Sy ≡ ⟦ g ⟧Sy
open _≡Hom_ public

solveCat : ∀ {C S T} → {d d' : SynHom C S T} ->
           normSyn d ≡ normSyn d' -> d ≡Hom d'
eqArr (solveCat {d = d} {d' = d'} q) = begin
    ⟦ d ⟧Sy
      ≡⟨ normSynSound d ⟩
    ⟦ normSyn d ⟧MPs
      ≡⟨ cong ⟦_⟧MPs q ⟩
    ⟦ normSyn d' ⟧MPs
      ≡˘⟨ normSynSound d' ⟩
    ⟦ d' ⟧Sy
      ∎ where open ≡-Reasoning


HomEq : ∀ {C S T S' T'} → (d : SynHom C S T)(d' : SynHom C S' T') -> Set
HomEq {C} {S} {T} {S'} {T'} d d' =
  Σ (S ≡ S') λ { refl → Σ (T ≡ T') λ { refl → d ≡Hom d' } }

Reduced : ∀ {C S T S' T'} → (d : SynHom C S T)(d' : SynHom C S' T') -> Set
Reduced (idSyn {T}) (idSyn {T'}) = T ≡ T'
Reduced (compSyn f g) (compSyn f' g') = Reduced g g' × Reduced f f'
Reduced d d' = HomEq d d'

-- Reduced obligations are enough
reduced' : ∀ {C S T S' T'} → (d : SynHom C S T)(d' : SynHom C S' T') ->
           Reduced d d' -> HomEq d d'
reduced' idSyn idSyn refl = refl , refl , homEq refl
reduced' {C} (compSyn f g) (compSyn f' g') (rg , rf)
  with refl , refl , homEq qf ← reduced' f f' rf
     | refl , refl , homEq qg ← reduced' g g' rg
     = refl , refl , homEq (cong₂ (comp C) qf qg)
reduced' {C} (compSyn f g) < x > r = r
reduced' {C} (compSyn f g) idSyn r = r
reduced' {C} (compSyn f g) (fmapSyn F d') r = r
reduced' {C} (compSyn f g) -[ d' ]- r = r
reduced' < x > d' r = r
reduced' idSyn < x > r = r
reduced' idSyn (compSyn d' d'') r = r
reduced' idSyn (fmapSyn F d') r = r
reduced' idSyn -[ d' ]- r = r
reduced' (fmapSyn F d) d' r = r
reduced' -[ d ]- d' r = r

reduced : ∀ {C S T} → {d d' : SynHom C S T} -> Reduced d d' -> d ≡Hom d'
reduced {d = d} {d'} r with refl , refl , q ← reduced' d d' r = q


-- convenience constructors
rd : ∀ {C S T} → {d : SynHom C S T} -> HomEq d d
rd = refl , refl , homEq refl

rq : ∀ {C S T} → {d d' : SynHom C S T} -> ⟦ d ⟧Sy ≡ ⟦ d' ⟧Sy -> HomEq d d'
rq q = refl , refl , homEq q

-- "semantic" equational reasoning

open ≡-Reasoning

_⊧begin_ : ∀ C {S T} → {d d' : SynHom C S T} ->
            d ≡Hom d' -> ⟦ d ⟧Sy ≡ ⟦ d' ⟧Sy
C ⊧begin q = eqArr q

_≡⟦_⟧_ : ∀ {C S T}(d0 : SynHom C S T){d1 d2} ->
           d0 ≡Hom d1 -> d1 ≡Hom d2 -> d0 ≡Hom d2
eqArr (d0 ≡⟦ q1 ⟧ q2) = ⟦ d0 ⟧Sy ≡⟨ eqArr q1 ⟩ eqArr q2

_≡˘⟦_⟧_ : ∀ {C S T}(d0 : SynHom C S T){d1 d2} ->
            d1 ≡Hom d0 -> d1 ≡Hom d2 -> d0 ≡Hom d2
eqArr (d0 ≡˘⟦ q1 ⟧ q2) = ⟦ d0 ⟧Sy ≡˘⟨ eqArr q1 ⟩ eqArr q2

_⟦∎⟧ : ∀ {C S T}(d : SynHom C S T) -> d ≡Hom d
eqArr (d ⟦∎⟧) = refl


infix  3 _⟦∎⟧
infixr 2 _≡⟦_⟧_ _≡˘⟦_⟧_
infix  1 _⊧begin_
