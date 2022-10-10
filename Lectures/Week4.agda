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
  2≤4 = {!!}

  -- And to disprove concrete instances:

  ¬12≤3 : ¬ 12 ≤ 3
  ¬12≤3 = {!!}

  -- For proving general facts, we resort to "why is it stuck?", as
  -- usual:

  n≤1+n : (n : ℕ) -> n ≤ suc n
  n≤1+n n = {!!}

  -- However this can become tedious when we have to "unstick" an
  -- assumption given to us, as well as a goal we are trying to prove:

  n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
  n≤0⇒n≡0 = {!!}

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
  2≤4 = {!!}

  ¬12≤3 : ¬ 12 ≤ 3
  ¬12≤3 = {!!}

  -- constructing evidence is basically the same as before

  n≤1+n : (n : ℕ) -> n ≤ suc n
  n≤1+n n = {!!}

  -- but when given evidence, we can now pattern match!

  n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
  n≤0⇒n≡0 {n} p = {!!}


  -------------------------------------------------------------------
  -- ≤ is a partial order
  -------------------------------------------------------------------

  ≤-reflexive : (n : ℕ) -> n ≤ n
  ≤-reflexive n = {!!}

  ≤-trans : {n m k : ℕ} -> n ≤ m -> m ≤ k -> n ≤ k
  ≤-trans p q = {!!}

  ≤-antisym : {n m : ℕ} -> n ≤ m -> m ≤ n -> n ≡ m
  ≤-antisym p q = {!!}

  -------------------------------------------------------------------
  -- Other properties of ≤
  -------------------------------------------------------------------

  ≤-propositional : {n m : ℕ} -> isPropositional (n ≤ m)
  ≤-propositional p q = {!!}

  ≤-decidable : (n m : ℕ) -> Dec (n ≤ m)
  ≤-decidable p q = {!!}
































---------------------------------------------------------------------------
-- Bonus: Derivabiliity as an inductively defined relation
---------------------------------------------------------------------------

open import Data.String

-- Formulas

data Formula : Set where
  Atom : String -> Formula
  _⇒_ : Formula -> Formula -> Formula

-- Contexts

data Context : Set where
  ε : Context
  _·_ : Context -> Formula -> Context -- \cdot

-- A proof system

data _⊢_ : Context -> Formula -> Set where -- \vdash
  hyp : ∀ {Γ A} → Γ · A ⊢ A
  weak : ∀ {Γ A B } → Γ ⊢ A → Γ · B ⊢ A
  abs : ∀ {Γ A B } → Γ · A ⊢ B →  Γ ⊢ A ⇒ B
  app : ∀ {Γ A B } → Γ ⊢ A ⇒ B →  Γ ⊢ A → Γ ⊢ B

infix 3 _⊢_
infixl 4 _·_
infixr 6 _⇒_

-- example1 : ε · Atom "A" ⊢ Atom "A"
-- example1 = ?

-- example2 : ε · Atom "A" · (Atom "A" ⇒ Atom "B") ⊢ Atom "B"
-- example2 = ?

-- How do we show that some formulas are *not* derivable?

-- example3 : ¬ (ε ⊢ (Atom "A" ⇒ Atom "B") ⇒ Atom "A")
-- example3 p = ?
