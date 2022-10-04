module Lectures.Week3 where

open import Data.Nat
open import Data.Empty
open import Data.Unit
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
lem {P} = {!!} -- not implementable! If it was, we could solve the halting problem

-- double negation elimination

DNE : Set1
DNE = {P : Set} -> ¬ ¬ P -> P

dne : DNE
dne {P} nnp with nnp (\ p -> nnp \ p' -> {!!}) -- does not seem to be implementable either
... | ()

-- this shows that DNE is as unimplementable as LEM
DNE→LEM : DNE -> LEM
DNE→LEM dne {P} = dne {P ⊎ ¬ P} (λ npnp → npnp (inj₂ \ p -> npnp (inj₁ p)))

-- ...and vice versa
LEM→DNE : LEM -> DNE
LEM→DNE lem {P} nnp with lem {P}
LEM→DNE lem {P} nnp | inj₁ p = p
LEM→DNE lem {P} nnp | inj₂ np with nnp np
LEM→DNE lem {P} nnp | inj₂ np | ()


----------------------------------------------------------------------
-- Quantifiers: for every, for some
----------------------------------------------------------------------


{- Universal quantification ∀ -}

-- Q: What is a proof of (∀ x : A) P(x)?

-- A: A method which produces a proof of P(a) for any given a : A -- a dependent function!

ex12 : (n : ℕ) -> isEven n ⊎ isEven (suc n)
ex12 zero = inj₁ tt
ex12 (suc zero) = inj₂ tt
ex12 (suc (suc n)) = ex12 n

-- Note: `A → B` is "just" (_ : A) -> B

{- Existential quantification ∃ -}

-- Q: What is a proof of (∃ x : A) P(x)?


-- A: A pair of an a : A and a proof of P(a) -- a dependent pair!

ex13 : Σ ℕ isEven
ex13 = 42 , tt

ex13' : Σ ℕ isEven
ex13' = 18 , tt

ex14 : Σ ℕ (\ n -> isEven n) -> Σ ℕ (λ n → ¬ (isEven n))
ex14 (zero , _) = 1 , λ x → x
ex14 (suc zero , ())
ex14 (suc (suc n) , en) = ex14 (n , en)

















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






