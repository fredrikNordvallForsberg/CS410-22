module Lectures.Week3 where

open import Data.Nat
open import Data.List as List using (List; []; _∷_; _++_; [_])
open import Data.Vec as Vec hiding (reverse)
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
  hiding (sym; trans; subst)

open import Lectures.Week2

----------------------------------------------------------------------
-- Classical logic
----------------------------------------------------------------------

-- You might remember the following principles from mathematics. What
-- would a program of such a type look like?

-- the law of excluded middle

LEM : Set1
LEM = {P : Set} -> P ⊎ ¬ P

{-
lem : LEM
lem {P} = {!!} -- not implementable! If it was, we could solve the halting problem
-}

-- double negation elimination

DNE : Set1
DNE = {P : Set} -> ¬ ¬ P -> P

{-
dne : DNE
dne {P} nnp with nnp (\ p -> nnp \ p' -> {!!}) -- does not seem to be implementable either
... | ()
-}

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

-- Useful/expected properties of ≡:

sym : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl q = q
-- trans p refl = p
-- trans refl refl = refl

subst : {A : Set} -> (P : A -> Set) -> {x y : A} -> x ≡ y -> P x -> P y
subst P refl px = px


-- FUN EXERCISE: basically everything is a special case of subst

-- "why is it stuck?"

+-assoc : (n m k : ℕ) -> ((n + m) + k) ≡ (n + (m + k))
+-assoc zero m k = refl
+-assoc (suc n) m k rewrite (+-assoc n m k) = refl

open ≡-Reasoning

*-distribʳ-+ : (m n k : ℕ) -> (n + k) * m ≡ n * m + k * m
*-distribʳ-+ m zero k = refl
*-distribʳ-+ m (suc n) k = begin
  (suc n + k) * m
    ≡⟨⟩
  m + ((n + k) * m)
    ≡⟨ cong (m +_) (*-distribʳ-+ m n k) ⟩      -- \==\< ? \>
  m + (n * m + k * m)
    ≡⟨ sym (+-assoc m (n * m) (k * m)) ⟩      -- \==\< ? \>
  (m + n * m) + k * m
    ∎ -- \qed
-- C-u C-u C-c C-s "solve everything you can, with as much normalisation as possible"


-- Reversing vectors with an accumulator

-- we can reverse lists naively (complexity O(n²))

revList : {A : Set} -> List A -> List A
revList [] = []
revList (x ∷ xs) = revList xs List.++ List.[ x ]

-- we can also reverse lists in a fast way (complexity O(n)):

revListFast : {A : Set} -> List A -> List A -> List A
revListFast acc [] = acc
revListFast acc (x ∷ xs) = revListFast (x ∷ acc) xs

-- let's do the same for vectors!

revAcc : {A : Set}{acc-length m : ℕ} -> Vec A acc-length -> Vec A m -> Vec A (acc-length + m)
revAcc {A} {n} acc [] = subst (Vec A) (lemma n) acc where
  lemma : (n : ℕ) → n ≡ n + 0
  lemma zero = refl
  lemma (suc n) = cong suc (lemma n)
revAcc {A} {n} acc (x ∷ xs) = subst (Vec A) (lemma n _) (revAcc (x ∷ acc) xs)
  where
    lemma : (n m : ℕ) → suc (n + m) ≡ n + suc m
    lemma zero m = refl
    lemma (suc n) m = cong suc (lemma n m)

reverse : {A : Set}{m : ℕ} -> Vec A m -> Vec A m
reverse = revAcc []


t = reverse (1 ∷ 2 ∷ 3 ∷ [])
-- C-c C-n t "normalise"



----------------------------------------------------------------------
-- Structural equalities (not covered in lecture)
---------------------------------------------------------------------

-----------------------------
-- When are two pairs equal?
-----------------------------

pair-≡ : {A B : Set} {a a' : A}{b b' : B} ->
         a ≡  a' -> b ≡ b' -> (a , b) ≡ (a' , b')
pair-≡ refl refl = refl -- if components are equal

pair-≡-inverse : {A B : Set} {a a' : A}{b b' : B} ->
                 (a , b) ≡ (a' , b') -> (a ≡  a') × (b ≡ b')
pair-≡-inverse p = (cong proj₁ p , cong proj₂ p) -- *only* if components are equal

-- So equality of pairs is a pair of equalities

-----------------------------------
-- When are dependent pairs equal?
-----------------------------------

-- Similarly for dependent pairs: we need to use `subst` and the first
-- equality p to fix up the type of the second equality

dpair-≡ : {A : Set}{B : A -> Set} {a a' : A}{b : B a}{b' : B a'}  ->
          (p : a ≡ a') -> (q : subst B p b ≡ b') ->
          (a , b) ≡ (a' , b')
dpair-≡ refl refl = refl -- when we pattern match on `p`, the type of `q` gets simplified

-----------------------------
-- When are functions equal?
-----------------------------

postulate
  -- not provable
  funext : {A : Set}{B : A -> Set}{f f' : (x : A) -> B x} ->
            ((x : A) -> f x ≡ f' x) -> f ≡ f'

  -- We often make use of this assumed fact, since we want to consider
  -- functions that have the same "input-output behaviour" as the same

-----------------------------------
-- When are equality proofs equal?
-----------------------------------

UIP : {A : Set}{x y : A}(p q : x ≡ y) -> p ≡ q
UIP refl refl = refl

-- "uniqueness of identity proofs"; interesting things possible if we
-- don't insist on this!
