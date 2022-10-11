module Lectures.Week4 where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

---------------------------------------------------------------------------
-- Inductively defined predicates
---------------------------------------------------------------------------

---------------------------------------------------------------------
module ByRecursion where
---------------------------------------------------------------------

  -- In Week 3, we defined special cases of < by recursion. Here is
  -- the general definition:

  _≤_ : ℕ -> ℕ -> Set
  zero ≤ m = ⊤
  suc n ≤ zero = ⊥
  suc n ≤ suc m = n ≤ m

  -- It is easy to prove concrete instances:

  2≤4 : 2 ≤ 4
  2≤4 = tt

  -- And to disprove concrete instances:

  ¬12≤3 : ¬ 12 ≤ 3
  ¬12≤3 ()

  -- For proving general facts, we resort to "why is it stuck?", as
  -- usual:

  n≤1+n : (n : ℕ) -> n ≤ suc n
  n≤1+n zero = tt
  n≤1+n (suc n) = n≤1+n n

  -- However this can become tedious when we have to "unstick" an
  -- assumption given to us, as well as a goal we are trying to prove:

  n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
  n≤0⇒n≡0 {zero} _ = refl
  n≤0⇒n≡0 {suc n} ()

  -- Sometimes it is nicer if we can just pattern match on the proof...

---------------------------------------------------------------------
module ByInduction where
---------------------------------------------------------------------

  -- Here is an alternative definition

  data _≤_ : ℕ -> ℕ -> Set where
    z≤n : {n : ℕ} -> zero  ≤ n
    s≤s : {m n : ℕ} -> m ≤ n -> suc m ≤ suc n

  -- Concrete cases are still easy, but requires a little bit more
  -- manual work:

  2≤4 : 2 ≤ 4
  2≤4 = s≤s (s≤s z≤n)

  ¬12≤3 : ¬ 12 ≤ 3
  ¬12≤3 (s≤s (s≤s (s≤s ())))

  -- constructing evidence is basically the same as before

  n≤1+n : (n : ℕ) -> n ≤ suc n
  n≤1+n zero = z≤n
  n≤1+n (suc n) = s≤s (n≤1+n n)

  n≤m+n : (n : ℕ){m : ℕ} -> n ≤ (n + m)
  n≤m+n zero = z≤n
  n≤m+n (suc n) = s≤s (n≤m+n n)

  -- but when given evidence, we can now pattern match!

  n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
  n≤0⇒n≡0 z≤n = refl


  -------------------------------------------------------------------
  -- ≤ is a partial order
  -------------------------------------------------------------------

  ≤-reflexive : (n : ℕ) -> n ≤ n
  ≤-reflexive zero = z≤n
  ≤-reflexive (suc n) = s≤s (≤-reflexive n)

  ≤-trans : {n m k : ℕ} -> n ≤ m -> m ≤ k -> n ≤ k
  ≤-trans z≤n q = z≤n
  ≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

  ≤-antisym : {n m : ℕ} -> n ≤ m -> m ≤ n -> n ≡ m
  ≤-antisym z≤n z≤n = refl
  ≤-antisym (s≤s p) (s≤s q) = cong suc (≤-antisym p q)

  -------------------------------------------------------------------
  -- Other properties of ≤
  -------------------------------------------------------------------

  ≤-propositional : {n m : ℕ} -> isPropositional (n ≤ m)
  ≤-propositional z≤n z≤n = refl
  ≤-propositional (s≤s p) (s≤s q) = cong s≤s (≤-propositional p q)

  ≤-decidable : (n m : ℕ) -> Dec (n ≤ m)
  ≤-decidable zero m = yes z≤n
  ≤-decidable (suc n) zero = no λ ()
  ≤-decidable (suc n) (suc m) with ≤-decidable n m
  ... | yes n≤m = yes (s≤s n≤m)
  ... | no ¬n≤m = no λ { (s≤s p) → ¬n≤m p }
