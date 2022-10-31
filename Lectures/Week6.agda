{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --type-in-type #-}
module Lectures.Week6 where

open import Data.Unit hiding (_≤_)
open import Data.Product
open import Data.Maybe

open import Function as Fun

open import Relation.Binary.PropositionalEquality
open import Axiom.UniquenessOfIdentityProofs.WithK

open import Common.Category hiding (SET)

open Category

---------------------------------------------------------------------------
-- The category of sets
---------------------------------------------------------------------------

SET : Category
Obj SET = Set
Hom SET A B = A -> B
Category.id SET = λ x → x
comp SET f g = λ x → g (f x)
assoc SET = refl
identityˡ SET = refl
identityʳ SET = refl


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
Obj MONOID = Monoid
Hom MONOID A B = MonoidMorphism A B
fun (Category.id MONOID) x = x
preserves-ε (Category.id MONOID) = refl
preserves-∙ (Category.id MONOID) x y = refl
fun (comp MONOID f g) a = fun g (fun f a)
preserves-ε (comp MONOID f g) rewrite preserves-ε f = preserves-ε g
preserves-∙ (comp MONOID f g) x y rewrite preserves-∙ f x y = preserves-∙ g (fun f x) (fun f y)
assoc MONOID = eqMonoidMorphism refl
identityˡ MONOID = eqMonoidMorphism refl
identityʳ MONOID = eqMonoidMorphism refl


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
Obj PREORDER = Preorder
Hom PREORDER = MonotoneMap
fun (Category.id PREORDER) = λ x → x
monotone (Category.id PREORDER) x y x≤y = x≤y
fun (comp PREORDER f g) a = fun g (fun f a)
monotone (comp PREORDER f g) x y x≤y = monotone g _ _ (monotone f x y x≤y)
assoc PREORDER = eqMonotoneMap refl
identityˡ PREORDER = eqMonotoneMap refl
identityʳ PREORDER = eqMonotoneMap refl


---------------------------------------------------------------------------
-- Discrete categories (not covered in the lecture)
---------------------------------------------------------------------------

-- Every set can be seen as a category where there are only identity morphisms

discrete : Set -> Category
Obj (discrete X) = X
Hom (discrete X) x y = x ≡ y
Category.id (discrete X) = refl
comp (discrete X) refl refl = refl
assoc (discrete X) {f = refl} {refl} {refl} = refl
identityˡ (discrete X) {f = refl} = refl
identityʳ (discrete X) {f = refl} = refl


---------------------------------------------------------------------------
-- Monoids as categories (only alluded to in the lecture)
---------------------------------------------------------------------------

-- Every monoid can be seen as a boring category with exactly one
-- object

monoid : Monoid -> Category
Obj (monoid M) = ⊤
Hom (monoid M) tt tt = Carrier M
Category.id (monoid M) = ε M
comp (monoid M) = _∙_ M
assoc (monoid M) = assoc M
identityˡ (monoid M) = identityˡ M
identityʳ (monoid M) = identityʳ M


---------------------------------------------------------------------------
-- Preorders as categories (only alluded to in the lecture)
---------------------------------------------------------------------------

-- Every preorder can be seen as a boring category where there is at
-- most one morphism between any two objects

porder : Preorder -> Category
Obj (porder P) = Carrier P
Hom (porder P) = _≤_ P
Category.id (porder P) = reflexive P
comp (porder P) = transitive P
assoc (porder P) = propositional P _ _
identityˡ (porder P) = propositional P _ _
identityʳ (porder P) = propositional P _ _






---------------------------------------------------------------------------
-- Tree is a functor
---------------------------------------------------------------------------

-- an excursion to Haskell

open Functor

data Tree (X : Set) : Set where
  leaf : Tree X
  _<[_]>_ : Tree X -> X -> Tree X -> Tree X

tree-map : {X Y : Set} → (X → Y) → Tree X → Tree Y
tree-map f leaf = leaf
tree-map f (l <[ x ]> r) = tree-map f l <[ f x ]> tree-map f r

TREE : Functor SET SET
act TREE = Tree
fmap TREE = tree-map
identity TREE = ext identity-treemap
 where
 identity-treemap : ∀ {X} (x : Tree X) →
                   tree-map (Category.id SET) x ≡ Category.id SET x
 identity-treemap leaf = refl
 identity-treemap (l <[ x ]> r) rewrite identity-treemap l | identity-treemap r = refl

homomorphism TREE {X} {Y} {Z} {f} {g} = ext helper
 where
  helper : (x : act TREE X) →
         fmap TREE (comp SET f g) x ≡ comp SET (fmap TREE f) (fmap TREE g) x
  helper leaf = refl
  helper (l <[ x ]> r) rewrite helper l | helper r = refl

--------------------------------------------------------------------------
-- Forgetful mappings are functors
---------------------------------------------------------------------------

forgetMonoid : Functor MONOID SET
act forgetMonoid = Carrier
fmap forgetMonoid h = fun h
identity forgetMonoid = refl
homomorphism forgetMonoid = refl

--------------------------------------------------------------------------
-- "Canonical" constructions are often functors
---------------------------------------------------------------------------

smallestOrder : Functor SET PREORDER
Carrier (act smallestOrder X) = X
_≤_ (act smallestOrder X) x y = x ≡ y
reflexive (act smallestOrder X) = refl
transitive (act smallestOrder X) p q = trans p q
propositional (act smallestOrder X) = uip
fun (fmap smallestOrder f) = f
monotone (fmap smallestOrder f) x y x=y = cong f x=y
identity smallestOrder = eqMonotoneMap refl
homomorphism smallestOrder = eqMonotoneMap refl

-- Exercise: is there a greatest order? ("chaotic")

--------------------------------------------------------------------------
-- The category of categories
---------------------------------------------------------------------------

compFunctor : {C D E : Category} -> Functor C D → Functor D E → Functor C E
compFunctor F G = {!!}












idFunctor : {C : Category} -> Functor C C
idFunctor = {!!}

CAT : Category
CAT = {!!}




















--------------------------------------------------------------------------
-- root is a natural transformation
---------------------------------------------------------------------------
open NaturalTransformation

{-
MAYBE : Functor SET SET
act MAYBE = Maybe
fmap MAYBE = {!!}
identity MAYBE = {!!}
homomorphism MAYBE = {!!}

root : NaturalTransformation TREE MAYBE
root = ?
-}
