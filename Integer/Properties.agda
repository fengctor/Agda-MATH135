module Agda-MATH135.Integer.Properties where

open import Agda-MATH135.Integer.Integer
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _≤_ to _ℕ≤_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

0-n≡-n : ∀ (n : ℤ) → pos 0 - n ≡ - n
0-n≡-n (pos zero) = refl
0-n≡-n (pos (suc n)) = refl
0-n≡-n (neg-suc n) = refl


{------------------
  _ℕ+_ properties
------------------}


ℕ+-identityʳ : ∀ (m : ℕ) → m ℕ+ 0 ≡ m
ℕ+-identityʳ zero = refl
ℕ+-identityʳ (suc m) rewrite ℕ+-identityʳ m = refl

ℕ+-suc : ∀ (m n : ℕ) → m ℕ+ suc n ≡ suc (m ℕ+ n)
ℕ+-suc zero n = refl
ℕ+-suc (suc m) n rewrite ℕ+-suc m n = refl

ℕ+-assoc : ∀ (m n p : ℕ) → (m ℕ+ n) ℕ+ p ≡ m ℕ+ (n ℕ+ p)
ℕ+-assoc m n p = {!!}

ℕ+-comm : ∀ (m n : ℕ) → m ℕ+ n ≡ n ℕ+ m
ℕ+-comm zero n rewrite ℕ+-identityʳ n = refl
ℕ+-comm (suc m) n rewrite ℕ+-suc n m | ℕ+-comm m n = refl

{------------------
  _+_ properties
------------------}


ℕ--identityʳ : ∀ (n : ℤ) → n - pos 0 ≡ n
ℕ--identityʳ (pos zero) = refl
ℕ--identityʳ (pos (suc n)) rewrite ℕ+-identityʳ n = refl
ℕ--identityʳ (neg-suc n) = refl

0ℕ--as-unary : ∀ (n : ℕ) → 0 ℕ- n ≡ - (pos n)
0ℕ--as-unary zero = refl
0ℕ--as-unary (suc n) = refl

+-identityʳ : ∀ (m : ℤ) → m + pos 0 ≡ m
+-identityʳ (pos zero) = refl
+-identityʳ (pos (suc m)) rewrite ℕ+-identityʳ m = refl
+-identityʳ (neg-suc zero) = refl
+-identityʳ (neg-suc (suc m)) = refl

+-identityˡ : ∀ (n : ℤ) → pos 0 + n ≡ n
+-identityˡ (pos n) = refl
+-identityˡ (neg-suc n) = refl

pos-minus-pos : ∀ (m n : ℕ) → pos m - pos n ≡ m ℕ- n
pos-minus-pos m zero = ℕ--identityʳ (pos m)
pos-minus-pos m (suc n) = refl

pos0--as-unary : ∀ (n : ℤ) → pos 0 - n ≡ - n
pos0--as-unary (pos zero) = refl
pos0--as-unary (pos (suc n)) = refl
pos0--as-unary (neg-suc n) = refl

pos--to-ℕ- : ∀ (m n : ℕ) → m ℕ- n ≡ pos m - pos n
pos--to-ℕ- m zero rewrite ℕ+-identityʳ m = refl
pos--to-ℕ- m (suc n) = refl

ℕ--neg-comm : ∀ (m n : ℕ) → m ℕ- n ≡ - (n ℕ- m)
ℕ--neg-comm zero zero = refl
ℕ--neg-comm zero (suc n) = refl
ℕ--neg-comm (suc m) zero = refl
ℕ--neg-comm (suc m) (suc n) = ℕ--neg-comm m n

ℕ--distribˡ-+pos : ∀ (m n p : ℕ) → (m ℕ- n) + pos p ≡ (m ℕ+ p) ℕ- n
ℕ--distribˡ-+pos m zero p = refl
ℕ--distribˡ-+pos zero (suc n) p rewrite +-identityˡ (p ℕ- suc n) = refl
ℕ--distribˡ-+pos  (suc m) (suc n) p = ℕ--distribˡ-+pos m n p

ℕ--distribʳ-+pos : ∀ (m n p : ℕ) → pos m + (n ℕ- p) ≡ (m ℕ+ n) ℕ- p
ℕ--distribʳ-+pos m n zero = refl
ℕ--distribʳ-+pos m zero (suc p) rewrite ℕ+-identityʳ m = refl
ℕ--distribʳ-+pos m (suc n) (suc p) rewrite ℕ--distribʳ-+pos m n p | ℕ+-suc m n = refl

ℕ--distribˡ-+neg-suc : ∀ (m n p : ℕ) → (m ℕ- n) + neg-suc p ≡ m ℕ- (suc (n ℕ+ p))
ℕ--distribˡ-+neg-suc m zero p = refl
ℕ--distribˡ-+neg-suc zero (suc n) p = refl
ℕ--distribˡ-+neg-suc (suc m) (suc n) p = ℕ--distribˡ-+neg-suc m n p

ℕ--distribʳ-+neg-suc : ∀ (m n p : ℕ) → neg-suc m + (n ℕ- p) ≡ n ℕ- ((suc m) ℕ+ p)
ℕ--distribʳ-+neg-suc m n zero rewrite ℕ+-identityʳ m = refl
ℕ--distribʳ-+neg-suc m zero (suc p) rewrite ℕ+-suc m p = refl
ℕ--distribʳ-+neg-suc m (suc n) (suc p) rewrite ℕ--distribʳ-+neg-suc m n p | ℕ+-suc m p = refl

+-assoc : ∀ (m n p : ℤ) → (m + n) + p ≡ m + (n + p)
+-assoc (pos zero) n p rewrite +-identityˡ n | +-identityˡ (n + p) = refl
+-assoc m (pos zero) p rewrite +-identityʳ m | +-identityˡ p = refl
+-assoc m n (pos zero) rewrite +-identityʳ n | +-identityʳ (m + n) = refl
+-assoc (pos (suc m)) (neg-suc n) (neg-suc p)   = ℕ--distribˡ-+neg-suc m n p
+-assoc (neg-suc m) (pos (suc n)) (pos (suc p)) = ℕ--distribˡ-+pos n m (suc p)
+-assoc (pos (suc m)) (pos (suc n)) (pos (suc p))
  rewrite ℕ+-assoc m (suc n) (suc p)
        = refl
+-assoc (neg-suc m) (neg-suc n) (neg-suc p)
  rewrite ℕ+-suc m (n ℕ+ p)
        | ℕ+-assoc m n p
        = refl
+-assoc (pos (suc m)) (pos (suc n)) (neg-suc p)
  rewrite ℕ--distribʳ-+pos (suc m) n p 
        | ℕ+-suc m n
        = refl
+-assoc (neg-suc m) (neg-suc n) (pos (suc p))
  rewrite ℕ--distribʳ-+neg-suc m p n
        = refl
+-assoc (pos (suc m)) (neg-suc n) (pos (suc p))
  rewrite ℕ--distribˡ-+pos m n (suc p)
        | ℕ--distribʳ-+pos (suc m) p n
        | ℕ+-suc m p
        = refl
+-assoc (neg-suc m) (pos (suc n)) (neg-suc p)
  rewrite ℕ--distribʳ-+neg-suc m n p
        | ℕ--distribˡ-+neg-suc n m p
        = refl

-- needed?
+-suc : ∀ (m n : ℤ) → m + (pos 1 + n) ≡ pos 1 + (m + n)
+-suc (pos zero) n rewrite +-identityˡ (pos 1 + n) | +-identityˡ n = refl
+-suc (pos (suc m)) (pos n) rewrite ℕ+-suc m n = refl
+-suc (pos (suc m)) (neg-suc n) = {!!}
+-suc (neg-suc x) n = {!!}

+-comm : ∀ (m n : ℤ) → m + n ≡ n + m
+-comm m n = {!!}
