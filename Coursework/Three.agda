------------------------------------------------------------------------
-- CS410 Advanced Functional Programming 2022
--
-- Coursework 3
------------------------------------------------------------------------

module Coursework.Three where

----------------------------------------------------------------------------
-- COURSEWORK 3 -- TERMINAL OBJECTS AND DATABASES USING ADJUNCTIONS
--
-- VALUE:     40% (divided over 80 marks, ie each mark is worth 0.5%)
-- DEADLINE:  5pm, Monday 5 December (Week 12)
--
-- SUBMISSION: Push your solutions to your own repo. Your last commit
-- before the deadline is your submitted version. However do get in
-- touch if you want to negotiate about extensions.
----------------------------------------------------------------------------

-- HINT: your tasks are labelled with the very searchable tag '???'

-- TIP: It remains a good idea to comment out parts of the file you
-- currently are not working on.

open import Data.String
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat as Nat using (ℕ; zero; suc; _<ᵇ_; _≡ᵇ_; _⊔_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
open import Data.Vec as Vec hiding (filter; splitAt; count; sum)
open import Data.Vec.Properties
open import Data.Fin
open import Data.Fin.Properties
open import Data.Unit hiding (total)
open import Data.Empty
open import Data.Sum hiding (reduce)
open import Data.Sum.Properties
open import Data.Product
open import Function using () renaming (_∘′_ to _∘_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Common.Category
open import Common.Category.Adjunctions
open import Common.Category.Solver

open import Coursework.Three.Categories

open Category
open Functor
open Adjunction

open Monoid
open MonoidMorphism


------------------------------------------------------------------------
-- TERMINAL OBJECTS AND GLOBAL ELEMENTS (15 MARKS in total)
------------------------------------------------------------------------

-- Often concepts in category theory can be phrased as so-called
-- universal properties: we can describe an object as the "best"
-- object with a certain property, in the sense that all other objects
-- with the same property uniquely maps into the given object. A simple example
-- is the notion of a *terminal* object: this is an object such that
-- every other object has a unique morphism into it. We can describe
-- this as follows:

record IsTerminal (C : Category)(X : Obj C) : Set where
  field
    mediate : (Y : Obj C) → Hom C Y X
    mediateUnique : {Y : Obj C} → (h : Hom C Y X) → h ≡ mediate Y
open IsTerminal

-- This says that an object X is terminal if for every object Y, there
-- is a morphism `mediate Y` from Y to X, and this is the only
-- morphism from Y to X. Some categories have terminal objects, others
-- don't. For example, SET has ⊤ as a terminal object, because any
-- there is exactly one way to give a function Y → ⊤: it must send
-- everything to the only element tt : ⊤.

⊤-is-terminal : IsTerminal SET ⊤
mediate ⊤-is-terminal Y = λ y → tt
mediateUnique ⊤-is-terminal h = refl

{- ??? 3.1 Show that MONOID has a terminal object.
  (2 MARKS) -}

-- HINT: Since morphisms in MONOID are morphisms in SET with extra
-- structure, it might be a good idea to take the terminal object in
-- SET and give it Monoid structure in order to create the terminal
-- object in Monoid.

⊤-Monoid : Monoid
⊤-Monoid = {!!}

MONOID-has-terminal-object : IsTerminal MONOID ⊤-Monoid
MONOID-has-terminal-object = {!!}

{- ??? 3.2 Similarly, show that PREORDER has a terminal object.
  (2 MARKS) -}

open Preorder
open MonotoneMap

⊤-Preorder : Preorder
⊤-Preorder = {!!}

PREORDER-has-terminal-object : IsTerminal PREORDER ⊤-Preorder
PREORDER-has-terminal-object = {!!}

{- ??? 3.3 Show that there is a terminal category, too.
  (2 MARKS) -}

⊤-Cat : Category
⊤-Cat = {!!}

CAT-has-terminal-object : IsTerminal CAT ⊤-Cat
CAT-has-terminal-object = {!!}

-- Objects in an arbitrary category might not have elements, but we
-- can use a terminal object, if there is one, to talk about so-called
-- /global elements/ instead: a global element of X is a morphism from
-- the terminal object into X. This definition is motivated by the
-- following fact: in the category SET, the elements and global
-- elements of a set are "the same", in the sense that the two
-- concepts are isomorphic, as in Coursework.Two:

record _↔_ (A B : Set) : Set where
  field
    to         : A -> B
    from       : B -> A
    left-inverse-of : (x : A) -> from (to x) ≡ x
    right-inverse-of : (y : B) -> to (from y) ≡ y
open _↔_

infix 3 _↔_

{- ??? 3.4 Prove that elements and global elements are the same thing
           in SET.
  (1 MARK) -}

global-elements-in-SET : (X : Set) → Hom SET ⊤ X ↔ X
global-elements-in-SET X = {!!}

{- ??? 3.5 What are the global elements in PREORDER? Fill in your answer,
           and prove it.
  (2 MARKS) -}

global-elements-in-PREORDER : (P : Preorder) →
                              Hom PREORDER ⊤-Preorder P ↔ {!!}
global-elements-in-PREORDER P = {!!}

{- ??? 3.6 And what are the global elements in CAT?
  (3 MARKS) -}

global-elements-in-CAT : (C : Category) →
                         Hom CAT ⊤-Cat C ↔ {!!}
global-elements-in-CAT C = {!!}

{- ??? 3.7 Just as we are starting to see a pattern, let us see a
           perhaps unexpected example: what are the global elements
           in MONOID?
   (3 MARKS) -}

global-elements-in-MONOID : (M : Monoid) →
                            Hom MONOID ⊤-Monoid M ↔ {!!}
global-elements-in-MONOID M = {!!}






------------------------------------------------------------------------
-- RELATIONAL ALGEBRA BY WAY OF ADJUNCTIONS (65 MARKS in total)
------------------------------------------------------------------------

-- In the rest of this coursework, we will develop a database library
-- based on a fundamental adjunction between sets and monoids. Much of
-- this is taken from the paper
--
--   Relational Algebra by Way of Adjunctions
--   Jeremy Gibbons, Fritz Henglein, Ralf Hinze, and Nicolas Wu
--   International Conference on Functional Programming 2018
--   https://www.cs.ox.ac.uk/jeremy.gibbons/publications/reladj.pdf

---------------------------------------------
-- The Bag adjunction (10 MARKS in total)
---------------------------------------------

-- We want to represent a database as a "bag" of values, so our first
-- task is to define such bags. In order to be able to import this
-- definition in the separate examples file below, we do this in
-- another imported file:


{- ??? 3.8--3.9 in Coursework.Three.Bag; solve them there!
   (10 MARKS) -}
open import Coursework.Three.Bag

---------------------------------------------
-- Using the adjunction (15 MARKS in total)
---------------------------------------------

-- Without looking at how we implemented things in the abstract block,
-- we will now extract some useful constructions and properties from
-- the Bag adjunction constructed.

{- ??? 3.10 First, show that there is an empty bag, and a way to
           combine two bags. (This is just using the functor BAG.)
   (1 MARK) -}

empty : {A : Set} → Bag A
empty {A} = {!!}

_∪_ : {A : Set} → Bag A → Bag A → Bag A
_∪_ {A} = {!!}

{- ??? 3.11 Next, use the adjunction to construct singleton bags.
   (1 MARK) -}

single : {A : Set} → A → Bag A
single {A} a = {!!}

{- ??? 3.12 Again using the adjunction, we also get a method for
            crushing down a whole bag of monoid elements into a single
            element. It is good to remember that this is operation
            preserves monoid structure, so derive it as a monoid
            morphism before extracting its underlying function.
   (1 MARK) -}

reduceMonoid : (M : Monoid) → MonoidMorphism (act BAG (Carrier M)) M
reduceMonoid M = {!!}

reduce : (M : Monoid) → Bag (Carrier M) → Carrier M
reduce M = {!!}

{- ??? 3.13 Prove that reduce preserves empty bags, and unions of bags.
   (1 MARK) -}

reduce-empty : (M : Monoid) → reduce M empty ≡ ε M
reduce-empty = {!!}

reduce-∪ : (M : Monoid) → (s t : Bag (Carrier M)) →
           reduce M (s ∪ t) ≡ _∙_ M (reduce M s) (reduce M t)
reduce-∪ M = {!!}

{- ??? 3.14 Also prove that if we reduce a singleton, we get the
            element back.
   (3 MARKS) -}

reduce-single : (M : Monoid) → (m : Carrier M) → reduce M (single m) ≡ m
reduce-single = {!!}

{- ??? 3.15 Show that *any* monoid morphism out of Bag A can be
            written using reduce and single, and that as a result two
            such morphisms are equal if and only if they agree on
            singletons.
   (5 MARKS) -}

morphism-out-of-Bag-unique : {A : Set}(M : Monoid) →
                             (h : MonoidMorphism (act BAG A) M) →
                             h ≡ comp MONOID (fmap BAG (fun h ∘ single)) (reduceMonoid M)
morphism-out-of-Bag-unique = {!!}

equal-from-Bag : {A : Set}(B : Monoid) →
                 (f g : MonoidMorphism (act BAG A) B) →
                 ((fun f) ∘ single ≡ (fun g) ∘ single) →
                 f ≡ g
equal-from-Bag = {!!}

{- ??? 3.16 Let's make some monoids to reduce with!
   (3 MARKS) -}

sum : Monoid
Carrier sum = ℕ
_∙_ sum = Nat._+_
ε sum = {!!}
assoc sum {x} {y} {z} = {!!}
identityˡ sum = {!!}
identityʳ sum = {!!}

max : Monoid
Carrier max = ℕ
_∙_ max = _⊔_
ε max = {!!}
assoc max {x} {y} {z} = {!!}
identityˡ max = {!!}
identityʳ max {x} = {!!}

all : Monoid
Carrier all = Bool
_∙_ all = _∧_
ε all = {!!}
assoc all {x} {y} {z} = {!!}
identityˡ all = {!!}
identityʳ all {x} = {!!}

---------------------------------------------
-- Relational algebra (20 MARKS in total)
---------------------------------------------

{- ??? 3.17 Recall that Bag also has an action on functions, which
            preserves empty bags and unions of bags.
   (2 MARKS) -}

Bagmap : {A B : Set} → (A → B) → Bag A → Bag B
Bagmap = {!!}

Bagmap-id : {A : Set} → Bagmap (λ (x : A) → x) ≡ Category.id SET
Bagmap-id = {!!}

Bagmap-comp : {A B C : Set} → (f : A → B)(g : B → C) →
              Bagmap (g ∘ f) ≡ comp SET (Bagmap f) (Bagmap g)
Bagmap-comp = {!!}

Bagmap-empty : {A B : Set} → (f : A → B) → Bagmap f empty ≡ empty
Bagmap-empty = {!!}

Bagmap-∪ : {A B : Set} → (f : A → B) → (s t : Bag A) →
           Bagmap f (s ∪ t) ≡ Bagmap f s ∪ Bagmap f t
Bagmap-∪ = {!!}

{- ??? 3.18 Using more of the adjunction, we can also show that Bagmap
            preserves singletons, and commutes with reduce in an
            appropriate sense.
   (4 MARKS) -}

Bagmap-single : {A B : Set} → (f : A → B) → (a : A) →
                Bagmap f (single a) ≡ single (f a)
Bagmap-single = {!!}

reduce-natural : {A B : Set} → (f : A → B) → (reduce (act BAG B)) ∘ (Bagmap (Bagmap f))  ≡ Bagmap f ∘ (reduce (act BAG A))
reduce-natural = {!!}

-- Using Bagmap, we can now implement projection, ie "SELECT field₁, ..., fieldₙ FROM table":
--   the fields are given by a function `A → B`, and the table by a Bag A:

project : {A B : Set} → (A → B) → Bag A → Bag B
project = Bagmap

{- ??? 3.19 Selection. Implement `guard p`, which turns a : A into a
            singleton bag if `p a` holds, and an empty bag otherwise.
            Use guard, reduce and Bagmap to implement filter, which
            should only keep the elements in the bag which satisfies p.

            This corresponds to the SQL construct "... WHERE p".
   (2 MARKS) -}

guard : {A : Set} → (A → Bool) → A → Bag A
guard = {!!}

flattenBag : {A : Set} → Bag (Bag A) → Bag A
flattenBag = {!!}

filter : {A : Set} → (A → Bool) → Bag A → Bag A
filter = {!!}

{- ??? 3.20 Show that filter preserves empty bags and unions of bags.
   (2 MARKS) -}

-- HINT: You've done the hard work for this already.

filter-empty : {A : Set} → (p : A → Bool) → filter p empty ≡ empty
filter-empty = {!!}

filter-∪ : {A : Set} → (p : A → Bool) → (s t : Bag A) →
           filter p (s ∪ t) ≡ filter p s ∪ filter p t
filter-∪ = {!!}

{- ??? 3.21 Further show that filter interacts sensibly with
            singletons, and commutes with Bagmap in an appropriate
            sense.
   (4 MARKS) -}

filter-single : {A : Set} → (p : A → Bool) → (a : A) →
                filter p (single a) ≡ guard p a
filter-single = {!!}

filter-Bag : {A B : Set} → (p : B → Bool) → (f : A → B) →
             (filter p) ∘ (Bagmap f) ≡ (Bagmap f) ∘ (filter (p ∘ f))
filter-Bag = {!!}

{- ??? 3.22 Use reduce and Bagmap to implement the "cartesian product"
            of two bags, containing all combinations of elements from
            each bag. Then use the Cartesian product and filter to
            implement a the join of two tables on a common field,
            assuming this field has decidable equality.
   (3 MARKS) -}

Bag× : {A B : Set} → Bag A × Bag B → Bag (A × B)
Bag× = {!!}

joinOn : ∀ {K V₁ V₂ : Set} → (eq : (x y : K) → Dec (x ≡ y)) → (f : V₁ → K)(g : V₂ → K) → Bag V₁ → Bag V₂ → Bag (V₁ × V₂)
joinOn = {!!}

{- ??? 3.23 Examples. Making use of the schemata (= records) and
            database instances (= terms of record type) in the
            `Coursework.Examples.Three` file, write expressions for
            computing the following queries:
   (3 MARKS) -}

open import Coursework.Examples.Three

eqFin : {n : ℕ} → (x y : Fin n) → Dec (x ≡ y)
eqFin = Data.Fin._≟_

_Str≟_ : (s s' : String) → Bool
s Str≟ s' = does (s Data.String.≟ s')

-- Display the name and price of all orders with a price above £600
-- "SELECT item-name, price FROM orders WHERE 600 < price"

costs-over-600 : Bag (String × ℕ)
costs-over-600 = {!!}

-- Retrieve the names of all sellers of Apple AirPods in Glasgow
-- "SELECT name FROM sellers JOIN orders ON seller-id WHERE item-name = 'Apple AirPods' AND city = 'Glasgow'"

airpod-sellers : Bag String
airpod-sellers = {!!}

-- Calculate the total spend of purchases that has happened in Edinburgh
-- "SELECT sum(price) FROM sellers JOIN orders where Seller.city = 'Edinburgh'"

total-spend-in-Edinburgh : ℕ
total-spend-in-Edinburgh = {!!}

---------------------------------------------
-- Indexed tables (20 MARKS in total)
---------------------------------------------

-- The above implementation of join works, but is rather inefficient:
-- we compute all possible combinations of elements, then throw away
-- all those pairs where the keys do not match. It would be more
-- efficient to first /index/ the bags by their keys, and then just
-- compute small Cartesian products for each key.

-- Step 1 to achieve this is to build machinery for maps from keys to
-- values. By restricting the possible keys, we can ensure an
-- efficient implementation. We hence consider the following universe
-- of keys:

data Key : Set where
  0' 1' : Key
  Word' : Key
  _+'_ _×'_ : Key → Key → Key

-- Each key has a given size:

size : Key → ℕ
size 0' = 0
size 1' = 1
size Word' = 16 -- some fixed size
size (p +' q) = size p Nat.+ size q
size (p ×' q) = size p Nat.* size q

-- ...and a key represents a number smaller than its size.

⟦_⟧ : Key → Set
⟦ k ⟧ = Fin (size k)

eqKey : (k : Key) → (x y : ⟦ k ⟧) → Dec (x ≡ y)
eqKey k x y = x Data.Fin.≟ y

-- We can now give a first-order representation of functions ⟦ k ⟧ → V:

Map : Key → (V : Set) → Set
Map 0' V = ⊤
Map 1' V = V
Map Word' V = Vec V (size Word')
Map (k +' k') V = Map k V × Map k' V
Map (k ×' k') V = Map k (Map k' V)

Map' : Key → (V : Set) → Set
Map' k V = ⟦ k ⟧ → V

{- ??? 3.24 Prove that indeed `Map k V` is isomorphic to `Map' k V`.
   (3 MARKS) -}

Map-to : (k : Key) (V : Set) → Map k V -> Map' k V
Map-to = {!!}

Map-from : (k : Key) (V : Set) → Map' k V -> Map k V
Map-from = {!!}

Map-to-from : (k : Key) (V : Set) → (x : Map k V) → Map-from k V (Map-to k V x) ≡ x
Map-to-from = {!!}

Map-from-to : (k : Key) (V : Set) → (x : Map' k V) → Map-to k V (Map-from k V x) ≡ x
Map-from-to = {!!}


Map↔Map' : (k : Key) → (V : Set) → Map k V ↔ Map' k V
Map↔Map' k V = {!!}

{- ??? 3.25 Use the isomorphism Map↔Map' to get an easy proof that
            `Map k` has an action on functions.
   (1 MARK) -}

Mapmap : (k : Key) → {V V' : Set} → (f : V → V') → Map k V → Map k V'
Mapmap = {!!}

{- ??? 3.26 Use the isomorphism again to construct constant maps.
   (1 MARK) -}

constMap : (k : Key) → (V : Set) → (v : V) → Map k V
constMap = {!!}

{- ??? 3.27 Show that maps into V₁ × V₂ are the same as a pair of maps
            into V₁ and V₂ separately.
   (2 MARKS) -}

mergeMap : (k : Key) → (V₁ V₂ : Set) → Map k V₁ × Map k V₂ → Map k (V₁ × V₂)
mergeMap = {!!}

mergeMap-inverse : (k : Key) → (V₁ V₂ : Set) → Map k (V₁ × V₂) → Map k V₁ × Map k V₂
mergeMap-inverse = {!!}

mergeMap-to-from : (k : Key) → (V₁ V₂ : Set) → (h : Map k V₁ × Map k V₂) → mergeMap-inverse k V₁ V₂ (mergeMap k V₁ V₂ h) ≡ h
mergeMap-to-from = {!!}

mergeMap-from-to : (k : Key) → (V₁ V₂ : Set) → (h : Map k (V₁ × V₂)) → mergeMap k V₁ V₂ (mergeMap-inverse k V₁ V₂ h) ≡ h
mergeMap-from-to = {!!}

mergeMap-iso : (k : Key) → (V₁ V₂ : Set) → (Map k V₁ × Map k V₂) ↔ Map k (V₁ × V₂)
mergeMap-iso = {!!}

-- We are now ready to introduce our indexed notion of Bags: a table
-- is a map from keys to bags of values.

Table : Key → (V : Set) → Set
Table k V = Map k (Bag V)

{- ??? 3.28 Use the constructions on maps above to reimplement the
            basic relational algebra operations on tables.
   (6 MARKS) -}

emptyTable : ∀ {k} {V} → Table k V
emptyTable = {!!}

singleTable : ∀ {k} {V} → (v : V) → Table k V
singleTable = {!!}

unionTable : ∀ {k} {V} → Table k V → Table k V → Table k V
unionTable = {!!}

projectTable : ∀ {k} {V V'} → (f : V → V') → Table k V → Table k V'
projectTable = {!!}

filterTable : ∀ {k} {V} → (p : V → Bool) → Table k V → Table k V
filterTable = {!!}

reduceTable : ∀ {k} (M : Monoid) → Table k (Carrier M) → Map k (Carrier M)
reduceTable = {!!}

{- ??? 3.29 Use Map-from, project and filter to implement indexing ix,
            which given a bag of key-value pairs should return a table
            where keys are mapped to the bag of all values associated
            to the key.

            Use ix to implement indexBy, the work horse of fast joining.
   (3 MARKS) -}

ix : ∀ {k} {V} → Bag (⟦ k ⟧ × V) → Table k V
ix = {!!}

indexBy : (k : Key){V : Set} → (V → ⟦ k ⟧) → Bag V → Table k V
indexBy = {!!}

{- ??? 3.30 We also need a way to turn a table back into a bag again,
            by collecting all the values for all the different keys.
            Implement this for both maps and tables.
   (2 MARKS) -}

elemsMap : {k : Key} {V : Set} → Map k V → Bag V
elemsMap = {!!}

elems : {k : Key} {V : Set} → Table k V → Bag V
elems = {!!}

{- ??? 3.31 Finally we can use indexBy to implement an efficient join on keys.
   (1 MARKS) -}

fastJoinOn : ∀ {k} {V₁ V₂} → (f : V₁ → ⟦ k ⟧)(g : V₂ → ⟦ k ⟧) → Bag V₁ → Bag V₂ → Bag (V₁ × V₂)
fastJoinOn = {!!}

{- ??? 3.32 An example again. Use indexBy and other table operations to
            compute the most expensive purchase for each buyer.
            "SELECT name, max(price) FROM buyers JOIN orders ON Buyer.buyer-id = Order.buyer-id"
   (1 MARK) -}

most-expensive-per-buyer : Bag (String × ℕ)
most-expensive-per-buyer = {!!}
