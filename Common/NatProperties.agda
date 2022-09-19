module Common.NatProperties where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Properties of ⌊_/2⌋ and ⌈_/2⌉
------------------------------------------------------------------------

n≡⌊n+n/2⌋ : ∀ n → n ≡ ⌊ n + n /2⌋
n≡⌊n+n/2⌋ zero          = refl
n≡⌊n+n/2⌋ (suc zero)    = refl
n≡⌊n+n/2⌋ (suc (suc n)) =
  cong suc (trans (n≡⌊n+n/2⌋ _) (cong ⌊_/2⌋ (sym (+-suc n (suc n)))))

n≡⌈n+n/2⌉ : ∀ n → n ≡ ⌈ n + n /2⌉
n≡⌈n+n/2⌉ zero          = refl
n≡⌈n+n/2⌉ (suc zero)    = refl
n≡⌈n+n/2⌉ (suc (suc n)) =
  cong suc (trans (n≡⌈n+n/2⌉ _) (cong ⌈_/2⌉ (sym (+-suc n (suc n)))))
