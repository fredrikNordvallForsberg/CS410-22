{-# OPTIONS --type-in-type #-}
module Lectures.Week9 where

open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Lectures.Week6 hiding (SET)


open import Common.Category
open import Common.Category.Adjunctions

---------------------------------------------------------------------------
-- Free categories
---------------------------------------------------------------------------

open Category
open Functor
open Adjunction

REL : Category
REL = {!!}

forgetCategory : Functor CAT REL
forgetCategory = {!!}













data Star {A : Set}(R : A -> A -> Set) : A -> A -> Set where
  ε : ∀ {a} → Star R a a
  _∷_ : ∀ {a b c} → R a b -> Star R b c -> Star R a c

freeCategory : Functor REL CAT
freeCategory = {!!}

freeCatisFree : Adjunction freeCategory forgetCategory
freeCatisFree = {!!}


