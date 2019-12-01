module Agda-MATH135.Integer.Properties where

open import Agda-MATH135.Integer.Integer
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _≤_ to _ℕ≤_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

0-n≡-n : ∀ (n : ℤ) → pos 0 - n ≡ - n
0-n≡-n (pos zero) = refl
0-n≡-n (pos (suc n)) = refl
0-n≡-n (neg-suc n) = refl

ℕ+-identityʳ : ∀ (m : ℕ) → m ℕ+ 0 ≡ m
ℕ+-identityʳ zero = refl
ℕ+-identityʳ (suc m) rewrite ℕ+-identityʳ m = refl

+-identityʳ : ∀ (m : ℤ) → m + pos 0 ≡ m
+-identityʳ (pos zero) = refl
+-identityʳ (pos (suc m)) rewrite ℕ+-identityʳ m = refl
+-identityʳ (neg-suc zero) = refl
+-identityʳ (neg-suc (suc m)) = refl

+-identityˡ : ∀ (n : ℤ) → pos 0 + n ≡ n
+-identityˡ (pos n) = refl
+-identityˡ (neg-suc n) = refl

ℕ+-suc : ∀ (m n : ℕ) → m ℕ+ suc n ≡ suc (m ℕ+ n)
ℕ+-suc zero n = refl
ℕ+-suc (suc m) n rewrite ℕ+-suc m n = refl

+-assoc : ∀ (m n p) → (m + n) + p ≡ m + (n + p)
+-assoc (pos zero) n p rewrite +-identityˡ n | +-identityˡ (n + p) = refl
+-assoc m (pos zero) p rewrite +-identityʳ m | +-identityˡ p = refl
+-assoc m n (pos zero) rewrite +-identityʳ n | +-identityʳ (m + n) = refl
+-assoc (pos (suc m)) (pos (suc n)) p = {!!}
+-assoc (pos (suc m)) (neg-suc x) p = {!!}
+-assoc (neg-suc x) n p = {!!}
+-suc : ∀ (m n : ℤ) → m + (pos 1 + n) ≡ pos 1 + (m + n)
+-suc m n = {!!}

ℕ+-comm : ∀ (m n : ℕ) → m ℕ+ n ≡ n ℕ+ m
ℕ+-comm zero n rewrite ℕ+-identityʳ n = refl
ℕ+-comm (suc m) n rewrite ℕ+-suc n m | ℕ+-comm m n = refl

+-comm : ∀ (m n : ℤ) → m + n ≡ n + m
+-comm m n = {!!}
