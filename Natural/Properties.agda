module Agda-MATH135.Natural.Properties where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

{------------------
  _+_ properties
------------------}

+-identityʳ : ∀ (m : ℕ) → m + 0 ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) rewrite +-identityʳ m = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n rewrite +-identityʳ n = refl
+-comm (suc m) n rewrite +-suc n m | +-comm m n = refl

{------------------
  _*_ properties
------------------}


*-identityʳ : ∀ (m : ℕ) → m * 1 ≡ m
*-identityʳ zero = refl
*-identityʳ (suc m) rewrite *-identityʳ m = refl

*-zeroʳ : ∀ (n : ℕ) → n * 0 ≡ 0
*-zeroʳ zero = refl
*-zeroʳ (suc n) = *-zeroʳ n

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n
  rewrite Eq.sym (+-assoc m n (m * n))
        | +-comm m n
        | +-assoc n m (m * n)
        | *-suc m n
        = refl

+-*-distribʳ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
+-*-distribʳ zero n p = refl
+-*-distribʳ (suc m) n p
  rewrite +-*-distribʳ m n p
        | +-assoc p (m * p) (n * p)
        = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite +-*-distribʳ n (m * n) p
        | *-assoc m n p
        = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zeroʳ n = refl
*-comm (suc m) n rewrite *-suc n m | *-comm n m = refl
