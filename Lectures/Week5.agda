module Lectures.Week5 where

open import Data.Nat hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Maybe hiding (decToMaybe)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

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

















---------------------------------------------------------------------------
-- Relating typed and untyped expressions
---------------------------------------------------------------------------

-- ∣_∣  : ∀ {t} → TExpr t -> Expr


{-
record Welltyped (e : Expr) : Set where
  constructor okay
  field
    τ : Ty
    t : TExpr τ
    is-same : ∣ t ∣ ≡ e
-}









{-
_≟'_ : (τ : Ty) -> (τ' : Ty) -> Dec (τ ≡ τ')
nat ≟' nat = yes refl
nat ≟' bool = no (λ ())
bool ≟' nat = no (λ ())
bool ≟' bool = yes refl

decToMaybe : {P : Set} -> Dec P -> Maybe P
decToMaybe (yes p) = just p
decToMaybe (no p)  = nothing

_≟_ : (τ : Ty) -> (τ' : Ty) -> Maybe (τ ≡ τ')
x ≟ y = decToMaybe (x ≟' y)
-}


-- infer : (e : Expr) -> Maybe (Welltyped e)















---------------------------------------------------------------------------
-- Optimising expressions
---------------------------------------------------------------------------

-- reduce-if : ∀ {t} → TExpr t -> TExpr t
