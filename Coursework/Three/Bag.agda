{-# OPTIONS --allow-unsolved-metas #-}
module Coursework.Three.Bag where

open import Data.List
  using (List; []; _∷_; _++_; map; foldr)
open import Data.List.Properties
  using (++-assoc; ++-identityˡ; ++-identityʳ;
         map-++-commute; map-id; map-compose;
         foldr-universal)
open import Relation.Binary.PropositionalEquality

open import Common.Category
open import Common.Category.Adjunctions

open import Coursework.Three.Categories

open Monoid
open MonoidMorphism
open Functor

{- ??? 3.8 Implement bags as /free monoids/: given a set A, we want
           Bag A to be the smallest monoid containing the elements of
           A. I've given you the first move: the carrier of the monoid
           can be taken as lists of elements from A (you can think of
           them as a "formal" multiplication of all the elements in
           the list). In fact, show that this construction of a monoid
           from every set extends to a functor from SET to MONOID.

           In order to not rely on implementation details in the rest
           of the library, we construct this functor in an `abstract`
           block. This means that outside of abstract blocks in this
           file, equations will not reduce; hence in theory we could
           in secret supply a more efficient implementation, as long
           as we provide the same interface to the outside world.
   (3 MARKS) -}

-- NOTE: Arguably, a better representation of bags would be as free
--       /commutative/ monoids, that is monoids where the order does
--       not matter.

-- HINT: The import lists for this file are carefully curated.


abstract

  BAG : Functor SET MONOID
  Carrier (act BAG A) = List A
  _∙_ (act BAG A) = {!!}
  ε (act BAG A) = {!!}
  assoc (act BAG A) {x} {y} {z} = {!!}
  identityˡ (act BAG A) {x} = {!!}
  identityʳ (act BAG A) {x} = {!!}
  fun (fmap BAG f) = {!!}
  preserves-ε (fmap BAG f) = {!!}
  preserves-∙ (fmap BAG f) = {!!}
  identity BAG = {!!}
  homomorphism BAG = {!!}

-- For convenience, let us name the carrier of the constructed monoid
Bag : Set → Set
Bag A = Carrier (act BAG A)

{- ??? 3.9 Show that your construction is the right one by showing
           that BAG is left adjoint to the forgetful functor from
           MONOID to SET. We will see soon that this adjunction will
           give rise to most of the constructions and properties
           needed to build a proof-of-concept database system.
   (7 MARKS) -}

{- MARKING: to 1, from 2, left-inverse-of 3 (with partial credit for partial success), right-inverse-of 1-}

open Adjunction

abstract
  BagAdjunction : Adjunction BAG FORGET
  BagAdjunction = {!!}


  -- For data entry, we break the abstraction barrier to
  -- provide an efficient way to create bags:
  fromList : {A : Set} → List A → Carrier (act BAG A)
  fromList xs = xs

