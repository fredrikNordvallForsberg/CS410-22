module Lectures.Week5 where

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

---------------------------------------------------------------------------
-- Expressions
---------------------------------------------------------------------------

data Expr : Set where
  num : ℕ -> Expr
  bit : Bool -> Expr
  _+E_ : Expr -> Expr -> Expr
  ifE_then_else_ : Expr -> Expr -> Expr -> Expr

infixl 4 _+E_
infix 0 ifE_then_else_

ex1 : Expr
ex1 = num 5 +E num 7

ex2 : Expr
ex2 = bit true +E num 7

ex3 : Expr
ex3 = ifE bit false then ex2 else num 2

---------------
-- Evaluation
---------------

data Val : Set where
  num : ℕ -> Val
  bit : Bool -> Val

_+V_ : Val -> Val -> Maybe Val
num n +V num n' = just (num (n + n'))
_ +V _ = nothing

eval : Expr → Maybe Val
eval (num n) = just (num n)
eval (bit b) = just (bit b)
eval (e +E e') = do
  v <- eval e
  v' <- eval e'
  v +V v'
eval (ifE e then et else ef) = do
  (bit b) <- eval e where _ → nothing
  if b then eval et else eval ef

eex1 : Maybe Val
eex1 = eval ex1

eex2 : Maybe Val
eex2 = eval ex2

---------------------------------------------------------------------------
-- Typed expressions
---------------------------------------------------------------------------

data Ty : Set where
  Num : Ty
  Bit : Ty

data TExpr : Ty -> Set where
  num : ℕ -> TExpr Num
  bit : Bool -> TExpr Bit
  _+E_ : TExpr Num -> TExpr Num -> TExpr Num
  ifE_then_else_ : {T : Ty} -> TExpr Bit -> TExpr T -> TExpr T -> TExpr T

tex1 : TExpr Num
tex1 = num 5 +E num 7

-- tex2 : TExpr Num
-- tex2 = {!bit true!} +E num 7

tex3 : TExpr Num
tex3 = ifE bit false then tex1 else num 2


---------------
-- Evaluation
---------------

TVal : Ty -> Set
TVal Num = ℕ
TVal Bit = Bool

teval : {T : Ty} -> TExpr T -> TVal T
teval (num n) = n
teval (bit b) = b
teval (e +E e') = teval e + teval e'
teval (ifE e then et else ef) = if teval e then teval et else teval ef

--------------------------------------------------------------------------
-- Relating typed and untyped expressions
---------------------------------------------------------------------------

∣_∣  : ∀ {t} → TExpr t -> Expr
∣ num n ∣ = num n
∣ bit b ∣ = bit b
∣ e +E e' ∣ = ∣ e ∣ +E ∣ e' ∣
∣ ifE e then et else ef ∣ = ifE ∣ e ∣ then ∣ et ∣ else ∣ ef ∣

record Welltyped (e : Expr) : Set where
  constructor okay
  field
    τ : Ty
    t : TExpr τ
    is-same : ∣ t ∣ ≡ e

tyEq? : (S T : Ty) -> Maybe (S ≡ T)
tyEq? Num Num = just refl
tyEq? Bit Bit = just refl
tyEq? _ _ = nothing

infer : (e : Expr) -> Maybe (Welltyped e)
infer (num n) = just (okay Num (num n) refl)
infer (bit b) = just (okay Bit (bit b) refl)
infer (e +E e') = do
  okay Num t refl <- infer e where _ -> nothing
  okay Num t' refl <- infer e' where _ -> nothing
  just (okay Num (t +E t') refl)
infer (ifE e then et else ef) = do
  okay Bit b refl <- infer e where _ -> nothing
  okay T t refl <- infer et
  okay F f refl <- infer ef
  refl <- tyEq? T F
  just (okay T (ifE b then t else f) refl)

---------------------------------------------------------------------------
-- Optimising expressions
---------------------------------------------------------------------------

reduce-if : ∀ {t} → TExpr t -> TExpr t
reduce-if (num n) = num n
reduce-if (bit b) = bit b
reduce-if (e +E e') = reduce-if e +E reduce-if e'
reduce-if (ifE e then et else ef) with reduce-if e
... | bit true = reduce-if et
... | bit false = reduce-if ef
... | oe@(ifE _ then _ else _) = ifE oe then reduce-if et else reduce-if ef

reduce-if-correct : ∀ {t} → (e : TExpr t) → teval (reduce-if e) ≡ teval e
reduce-if-correct (num n) = refl
reduce-if-correct (bit b) = refl
reduce-if-correct (e +E e')
  rewrite reduce-if-correct e | reduce-if-correct e' = refl
reduce-if-correct (ifE e then et else ef)
  with reduce-if e | reduce-if-correct e
... | bit false | qqq rewrite sym qqq = reduce-if-correct ef
... | bit true | qqq rewrite sym qqq = reduce-if-correct et
... | ifE qq then qq₁ else qq₂ | qqq
  rewrite qqq | reduce-if-correct et | reduce-if-correct ef = refl
