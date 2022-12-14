module Lectures.Week2 where

-- What kind of things can we put into our types, so that they are
-- checked by Agda?

----------------------------------------------------------------------
-- Propositions-as-booleans?
----------------------------------------------------------------------

data Bool : Set where -- can be found in Data.Bool
  false true : Bool

-- We can define for example `and` by pattern matching:

_&_ : Bool -> Bool -> Bool
false & y = false
true & y = y

-- but how do we represent eg `(∀ n : ℕ) P(n)`?

----------------------------------------------------------------------
-- Propositions-as-types
----------------------------------------------------------------------

-- Record *evidence* using types instead

{- Conjunction -}

-- Q: What is a proof of `A ∧ B`?

-- A: A proof of A and a proof of B -- a tuple!

open import Data.Product -- _×_ \times

-- find definition by clicking above

_∧_ : Set -> Set -> Set
A ∧ B = A × B

ex1 : {A B : Set} → A × B → A
ex1 = proj₁ 

ex2 : {A : Set} → A -> A ∧ A
ex2 a = a , a

{- Implication -}

-- Q: What is a proof of `A → B`?

-- A: A method for converting proofs of A into proofs of B -- a function!

ex3 : {A : Set} → A -> A
ex3 a = a

ex4 : {A B C D : Set} -> ((A -> B -> C) -> D) -> (A -> C) -> D
ex4 f g = f (λ a _ → g a)

{- True and False -}

-- the unit type represents a true proposition

open import Data.Unit -- ⊤ \top

-- again find definition by clicking

ex5 : {B : Set} -> B -> ⊤
ex5 = _

-- the empty type represents a false proposition

open import Data.Empty -- ⊥ \bot

ex6 : {B : Set} -> ⊥ -> B
ex6 = λ ()    -- `⊥-elim` in the library

{- Disjunction -}

-- Q: What is a proof of `A ∨ B`?

-- A: A proof of A, or a proof of B -- a disjoint union

open import Data.Sum -- _⊎_ \uplus

_∨_ : Set -> Set -> Set
A ∨ B = A ⊎ B

ex7 : {A B : Set} -> A ⊎ B -> B ⊎ A
ex7 (inj₁ a) = inj₂ a
ex7 (inj₂ b) = inj₁ b

{- Negation -}

-- Q: What is a proof of `¬ A`?

-- A: A method to show that all proofs of A are impossible -- a function A → ⊥

¬_ : Set -> Set
¬ A = A -> ⊥

ex8 : ¬ (⊤ -> ⊥)
ex8 f = f tt

ex9 : {A B : Set} -> A -> ¬ A -> B
ex9 a ¬a with ¬a a
... | ()

----------------------------------------------------------------------
-- Predicates in type theory
----------------------------------------------------------------------

-- What is a predicate?

Pred : Set -> Set1
Pred A = A -> Set

open import Data.Nat

isEven : ℕ -> Set
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n

test : isEven 4 --(suc (suc .... zero))
test = tt

test' : ¬ isEven 5
test' ()

_>1 : ℕ -> Set
zero >1 = ⊥
suc zero >1 = ⊥
suc (suc x) >1 = ⊤

_<3 : ℕ -> Set
zero <3 = ⊤
suc zero <3 = ⊤
suc (suc zero) <3 = ⊤
suc (suc (suc n)) <3 = ⊥

fact : 1 <3 × 2 >1
fact = _

{- Equality -}

{-
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
-}
open import Agda.Builtin.Equality

ex10 : 5 + 3 ≡ 8
ex10 = refl

ex11 : {x : ℕ} → (p : x ≡ 2) → x + 4 ≡ 6
ex11 refl = refl

ex11' : {x y : ℕ} → (p : x + y ≡ 2) → (x + y) + 4 ≡ 6
ex11' p rewrite p = refl -- rewrite

open import Relation.Binary.PropositionalEquality using (cong)

ex11'' : {A B : Set} → (f : A → B) → {x y : A} → (p : x ≡ y) → f x ≡ f y
ex11'' f refl = refl  -- same as `cong`
