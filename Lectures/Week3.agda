module Lectures.Week3 where

open import Data.Nat
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Lectures.Week2

----------------------------------------------------------------------
-- Classical logic
----------------------------------------------------------------------

-- You might remember the following principles from mathematics. What
-- would a program of such a type look like?

-- the law of excluded middle

LEM : Set1
LEM = {P : Set} -> P ⊎ ¬ P

lem : LEM
lem {P} = {!!}

-- double negation elimination

DNE : Set1
DNE = {P : Set} -> ¬ ¬ P -> P

dne : DNE
dne {P} ¬¬p = {!!}

LEM→DNE : LEM -> DNE
LEM→DNE lem {P} = {!!}













----------------------------------------------------------------------
-- Quantifiers: for every, for some
----------------------------------------------------------------------


{- Universal quantification ∀ -}

-- Q: What is a proof of (∀ x : A) P(x)?

























-- A: A method which produces a proof of P(a) for any given a : A -- a dependent function!

ex12 : (n : ℕ) -> isEven n ⊎ isEven (suc n)
ex12 = {!!}


















-- Note: `A → B` is "just" (_ : A) -> B

{- Existential quantification ∃ -}

-- Q: What is a proof of (∃ x : A) P(x)?




















-- A: A method which produces a proof of P(a) for any given a : A -- a dependent function!

ex13 : Σ ℕ isEven
ex13 = {!!}

ex13' : Σ ℕ isEven
ex13' = {!!}

ex14 : Σ ℕ isEven -> Σ ℕ (λ n → ¬ (isEven n))
ex14 = {!!}

















-- Note: A × B is "just" Σ[ _ ∈ A ] B





















----------------------------------------------------------------------
-- Equality, again
----------------------------------------------------------------------

-- "why is it stuck?"

+-assoc : (n m k : ℕ) -> ((n + m) + k) ≡ (n + (m + k))
+-assoc n m k = {!!}

open ≡-Reasoning

*-distribʳ-+ : (m n o : ℕ) -> (n + o) * m ≡ n * m + o * m
*-distribʳ-+ m n o = {!!}






