module Agda-MATH135.Integer.Integer where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _≤_ to _ℕ≤_)

infix  8 -_
infixl 7 _*_
infixl 6 _+_ _-_ _ℕ-_

data ℤ : Set where
  pos : ℕ → ℤ
  neg-suc : ℕ → ℤ


-- Unary Minus
-_ : ℤ → ℤ
- pos zero = pos zero
- pos (suc n) = neg-suc n
- neg-suc n = pos (suc n)

-- Absolute Value
∣_∣ : ℤ → ℕ
∣ pos n ∣ = n
∣ neg-suc n ∣ = suc n

-- Natural Subtraction
_ℕ-_ : ℕ → ℕ → ℤ
m ℕ- zero = pos m
zero ℕ- suc n = neg-suc n
suc m ℕ- suc n = m ℕ- n

-- Integer Addition
_+_ : ℤ → ℤ → ℤ
pos m + pos n = pos (m ℕ+ n)
neg-suc m + neg-suc n = neg-suc (suc (m ℕ+ n))
pos m + neg-suc n = m ℕ- suc n
neg-suc m + pos n = n ℕ- suc m

-- Integer Subtraction
_-_ : ℤ → ℤ → ℤ
m - n = m + (- n)

-- Integer Multiplication
_*_ : ℤ → ℤ → ℤ
pos m * pos n = pos (m ℕ* n)
neg-suc m * neg-suc n = pos (suc m ℕ* suc n)
pos m * neg-suc n = - pos (m ℕ* suc n)
neg-suc m * pos n = - pos (suc m ℕ* n)
