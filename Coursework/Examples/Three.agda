module Coursework.Examples.Three where

open import Data.List
open import Data.Nat using (ℕ; _≤″_; less-than-or-equal)
open import Data.Fin
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality

open import Data.Unit
open import Reflection using (TC; Term; unify; unquoteTC; _>>=_)

open import Coursework.Three.Bag

Identifier : Set
Identifier = Fin 16

pattern !! = less-than-or-equal refl
! = fromℕ<″

-- Buyer seller database

record Specialty : Set where
  constructor mkSpecialty
  field
    specialty-id : Identifier
    description : String
open Specialty

record Buyer : Set where
  constructor mkBuyer
  field
    buyer-id : Identifier
    name : String
    specialty-id : Identifier
open Buyer

record Order : Set where
  constructor mkOrder
  field
    order-id : Identifier
    item-name : String
    price : ℕ
    buyer-id : Identifier
    seller-id : Identifier
open Order

record Seller : Set where
  constructor mkSeller
  field
    seller-id : Identifier
    name : String
    city : String
open Seller

specialties : Bag Specialty
specialties = fromList
  (
   (mkSpecialty (! 0 !!) "Computer Science") ∷
   (mkSpecialty (! 1 !!) "Business Manegement") ∷
   (mkSpecialty (! 2 !!) "English Literature") ∷
   [])

buyers : Bag Buyer
buyers = fromList
  (
   (mkBuyer (! 0 !!) "Kevin Lee"      (! 0 !!)) ∷
   (mkBuyer (! 1 !!) "Edward Johnson" (! 1 !!)) ∷
   (mkBuyer (! 2 !!) "Jane King"      (! 0 !!)) ∷
   (mkBuyer (! 3 !!) "William Lewis"  (! 0 !!)) ∷
   (mkBuyer (! 4 !!) "Anne Carroll"   (! 1 !!)) ∷
   (mkBuyer (! 5 !!) "George Roberts" (! 1 !!)) ∷
   (mkBuyer (! 6 !!) "Clemens Klever" (! 2 !!)) ∷
   [])

sellers : Bag Seller
sellers = fromList
  (
   (mkSeller (! 0 !!) "John Lewis" "Edinburgh") ∷
   (mkSeller (! 1 !!) "Argos"      "London") ∷
   (mkSeller (! 2 !!) "Argos"      "Glasgow") ∷
   (mkSeller (! 3 !!) "Currys"     "Manchester") ∷
   (mkSeller (! 4 !!) "Currys"     "Glasgow") ∷
   (mkSeller (! 5 !!) "IKEA"       "Edinburgh") ∷
   [])

orders : Bag Order
orders = fromList
  (
   (mkOrder (! 0 !!) "Apple AirPods"           20 (! 2 !!) (! 0 !!)) ∷
   (mkOrder (! 1 !!) "iPhone 11"             1300 (! 4 !!) (! 4 !!)) ∷
   (mkOrder (! 2 !!) "iPhone 11"             1100 (! 1 !!) (! 0 !!)) ∷
   (mkOrder (! 3 !!) "iPhone 11"             1259 (! 1 !!) (! 4 !!)) ∷
   (mkOrder (! 4 !!) "Samsung Galaxy Note 10" 550 (! 1 !!) (! 4 !!)) ∷
   (mkOrder (! 5 !!) "iPhone 11"             2000 (! 3 !!) (! 0 !!)) ∷
   (mkOrder (! 6 !!) "Laptop HP Elitebook"   1000 (! 5 !!) (! 3 !!)) ∷
   (mkOrder (! 7 !!) "iPhone 11"              999 (! 5 !!) (! 2 !!)) ∷
   (mkOrder (! 8 !!) "Laptop HP Elitebook"     10 (! 2 !!) (! 2 !!)) ∷
   (mkOrder (! 9 !!) "Samsung Galaxy Note 10" 550 (! 3 !!) (! 4 !!)) ∷
   (mkOrder (! 10 !!) "Laptop HP Elitebook"   550 (! 0 !!) (! 3 !!)) ∷
   (mkOrder (! 11 !!) "Apple AirPods"          22 (! 6 !!) (! 2 !!)) ∷
   [])
