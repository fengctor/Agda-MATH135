module Agda-MATH135.Integer.Properties where

open import Agda-MATH135.Integer
import Agda-MATH135.Natural.Properties as ℕ

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _≤_ to _ℕ≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

ℕ--comm : ∀ (m n : ℕ) → m ℕ- n ≡ - (n ℕ- m)
ℕ--comm zero zero = refl
ℕ--comm zero (suc n) = refl
ℕ--comm (suc m) zero = refl
ℕ--comm (suc m) (suc n) = ℕ--comm m n

ℕ--as-minus : ∀ (m n : ℕ) → m ℕ- n ≡ pos m - pos n
ℕ--as-minus m zero rewrite ℕ.+-identityʳ m = refl
ℕ--as-minus m (suc n) = refl

neg-cancel : ∀ (n : ℤ) → - (- n) ≡ n
neg-cancel (pos zero) = refl
neg-cancel (pos (suc n)) = refl
neg-cancel (neg-suc n) = refl

neg-distrib-* : ∀ (m n : ℤ) → - (m * n) ≡ (- m) * n
neg-distrib-* (pos zero) (pos n) = refl
neg-distrib-* (pos (suc m)) (pos n) = refl
neg-distrib-* (pos zero) (neg-suc n) = refl
neg-distrib-* (pos (suc m)) (neg-suc n) = refl
neg-distrib-* (neg-suc m) (pos n) = neg-cancel (pos (n ℕ+ m ℕ* n))
neg-distrib-* (neg-suc m) (neg-suc n) = refl

{------------------
  ∣ _ ∣ properties
------------------}

abs-neg : ∀ (n : ℤ) → ∣ - n ∣ ≡ ∣ n ∣
abs-neg (pos zero) = refl
abs-neg (pos (suc n)) = refl
abs-neg (neg-suc n) = refl

abs-* : ∀ (m n : ℤ) → ∣ m * n ∣ ≡ ∣ m ∣ ℕ* ∣ n ∣
abs-* (pos m) (pos n) = refl
abs-* (pos m) (neg-suc n) = abs-neg (pos (m ℕ* suc n))
abs-* (neg-suc m) (pos n) = abs-neg (pos (n ℕ+ m ℕ* n))
abs-* (neg-suc m) (neg-suc n) = refl

abs-+-either : ∀ (m n : ℤ) → ∣ m + n ∣ ≡ ∣ m ∣ ℕ+ ∣ n ∣ ⊎ ∣ m + n ∣ ≡ ∣ ∣ m ∣ ℕ- ∣ n ∣ ∣
abs-+-either (pos m) (pos n) = inj₁ refl
abs-+-either (pos m) (neg-suc n) = inj₂ refl
abs-+-either (neg-suc m) (pos n)
  rewrite ℕ--comm n (suc m)
        = inj₂ (abs-neg (suc m ℕ- n))
abs-+-either (neg-suc m) (neg-suc n)
  rewrite ℕ.+-suc m n
        = inj₁ refl

{------------------
  _+_ properties
------------------}

ℕ--identityʳ : ∀ (n : ℤ) → n - pos 0 ≡ n
ℕ--identityʳ (pos n) rewrite ℕ.+-identityʳ n = refl
ℕ--identityʳ (neg-suc n) = refl

+-identityʳ : ∀ (n : ℤ) → n + pos 0 ≡ n
+-identityʳ (pos n) rewrite ℕ.+-identityʳ n = refl
+-identityʳ (neg-suc n) = refl

+-identityˡ : ∀ (n : ℤ) → pos 0 + n ≡ n
+-identityˡ (pos n) = refl
+-identityˡ (neg-suc n) = refl

ℕ--inv : ∀ (n : ℕ) → n ℕ- n ≡ pos 0
ℕ--inv zero = refl
ℕ--inv (suc n) = ℕ--inv n

+-invʳ : ∀ (n : ℤ) → n + (- n) ≡ pos 0
+-invʳ (pos zero) = refl
+-invʳ (pos (suc n)) = ℕ--inv n
+-invʳ (neg-suc n) = ℕ--inv n

+-invˡ : ∀ (n : ℤ) → (- n) + n ≡ pos 0
+-invˡ (pos zero) = refl
+-invˡ (pos (suc n)) = ℕ--inv n
+-invˡ (neg-suc n) = ℕ--inv n

ℕ--distribˡ-+pos : ∀ (m n p : ℕ) → (m ℕ- n) + pos p ≡ (m ℕ+ p) ℕ- n
ℕ--distribˡ-+pos m zero p = refl
ℕ--distribˡ-+pos zero (suc n) p rewrite +-identityˡ (p ℕ- suc n) = refl
ℕ--distribˡ-+pos  (suc m) (suc n) p = ℕ--distribˡ-+pos m n p

ℕ--distribʳ-+pos : ∀ (m n p : ℕ) → pos m + (n ℕ- p) ≡ (m ℕ+ n) ℕ- p
ℕ--distribʳ-+pos m n zero = refl
ℕ--distribʳ-+pos m zero (suc p) rewrite ℕ.+-identityʳ m = refl
ℕ--distribʳ-+pos m (suc n) (suc p) rewrite ℕ--distribʳ-+pos m n p | ℕ.+-suc m n = refl

ℕ--distribˡ-+neg-suc : ∀ (m n p : ℕ) → (m ℕ- n) + neg-suc p ≡ m ℕ- (suc (n ℕ+ p))
ℕ--distribˡ-+neg-suc m zero p = refl
ℕ--distribˡ-+neg-suc zero (suc n) p = refl
ℕ--distribˡ-+neg-suc (suc m) (suc n) p = ℕ--distribˡ-+neg-suc m n p

ℕ--distribʳ-+neg-suc : ∀ (m n p : ℕ) → neg-suc m + (n ℕ- p) ≡ n ℕ- ((suc m) ℕ+ p)
ℕ--distribʳ-+neg-suc m n zero rewrite ℕ.+-identityʳ m = refl
ℕ--distribʳ-+neg-suc m zero (suc p) rewrite ℕ.+-suc m p = refl
ℕ--distribʳ-+neg-suc m (suc n) (suc p) rewrite ℕ--distribʳ-+neg-suc m n p | ℕ.+-suc m p = refl

+-assoc : ∀ (m n p : ℤ) → (m + n) + p ≡ m + (n + p)
+-assoc (pos zero) n p rewrite +-identityˡ n | +-identityˡ (n + p) = refl
+-assoc m (pos zero) p rewrite +-identityʳ m | +-identityˡ p = refl
+-assoc m n (pos zero) rewrite +-identityʳ n | +-identityʳ (m + n) = refl
+-assoc (pos (suc m)) (neg-suc n) (neg-suc p)   = ℕ--distribˡ-+neg-suc m n p
+-assoc (neg-suc m) (pos (suc n)) (pos (suc p)) = ℕ--distribˡ-+pos n m (suc p)
+-assoc (pos (suc m)) (pos (suc n)) (pos (suc p))
  rewrite ℕ.+-assoc m (suc n) (suc p)
        = refl
+-assoc (neg-suc m) (neg-suc n) (neg-suc p)
  rewrite ℕ.+-suc m (n ℕ+ p)
        | ℕ.+-assoc m n p
        = refl
+-assoc (pos (suc m)) (pos (suc n)) (neg-suc p)
  rewrite ℕ--distribʳ-+pos (suc m) n p 
        | ℕ.+-suc m n
        = refl
+-assoc (neg-suc m) (neg-suc n) (pos (suc p))
  rewrite ℕ--distribʳ-+neg-suc m p n
        = refl
+-assoc (pos (suc m)) (neg-suc n) (pos (suc p))
  rewrite ℕ--distribˡ-+pos m n (suc p)
        | ℕ--distribʳ-+pos (suc m) p n
        | ℕ.+-suc m p
        = refl
+-assoc (neg-suc m) (pos (suc n)) (neg-suc p)
  rewrite ℕ--distribʳ-+neg-suc m n p
        | ℕ--distribˡ-+neg-suc n m p
        = refl

+-comm : ∀ (m n : ℤ) → m + n ≡ n + m
+-comm (pos m) (pos n) rewrite ℕ.+-comm m n = refl
+-comm (pos m) (neg-suc n) = refl
+-comm (neg-suc m) (pos n) = refl
+-comm (neg-suc m) (neg-suc n) rewrite ℕ.+-comm m n = refl

{------------------
  _*_ properties
------------------}

*-identityʳ : ∀ (n : ℤ) → n * (pos 1) ≡ n
*-identityʳ (pos n) rewrite ℕ.*-identityʳ n = refl
*-identityʳ (neg-suc n) rewrite ℕ.*-identityʳ n = refl

*-identityˡ : ∀ (n : ℤ) → (pos 1) * n ≡ n
*-identityˡ (pos n) rewrite ℕ.+-identityʳ n = refl
*-identityˡ (neg-suc n) rewrite ℕ.+-identityʳ n = refl

*-zeroˡ : ∀ (n : ℤ) → (pos 0) * n ≡ pos 0
*-zeroˡ (pos n) = refl
*-zeroˡ (neg-suc n) = refl

*-zeroʳ : ∀ (n : ℤ) → n * (pos 0) ≡ pos 0
*-zeroʳ (pos n) rewrite ℕ.*-zeroʳ n = refl
*-zeroʳ (neg-suc n) rewrite ℕ.*-zeroʳ n = refl

private
  pos-*--pos : ∀ (m n : ℕ) → pos m * (- pos n) ≡ - pos (m ℕ* n)
  pos-*--pos zero n = *-zeroˡ (- pos n)
  pos-*--pos (suc m) zero rewrite ℕ.*-zeroʳ m = refl
  pos-*--pos (suc m) (suc n) = refl

  -pos-*-pos : ∀ (m n : ℕ) → (- pos m) * pos n ≡ - pos (m ℕ* n)
  -pos-*-pos zero n = refl
  -pos-*-pos (suc m) zero = refl
  -pos-*-pos (suc m) (suc n) = refl

  neg-suc-*--pos : ∀ (m n : ℕ) → neg-suc m * (- pos n) ≡ pos (suc m ℕ* n)
  neg-suc-*--pos m zero rewrite ℕ.*-zeroʳ m = refl
  neg-suc-*--pos m (suc n) = refl

  -pos-*-neg-suc : ∀ (m n : ℕ) → (- pos m) * neg-suc n ≡ pos (m ℕ* suc n)
  -pos-*-neg-suc zero n = refl
  -pos-*-neg-suc (suc m) n = refl

*-assoc : ∀ (m n p : ℤ) → (m * n) * p ≡ m * (n * p)
*-assoc (pos m) (pos n) (pos p) rewrite ℕ.*-assoc m n p = refl
*-assoc (pos m) (pos n) (neg-suc p)
  rewrite pos-*--pos m (n ℕ* suc p)
        | ℕ.*-assoc m n (suc p)
        = refl
*-assoc (pos m) (neg-suc n) (pos p)
  rewrite pos-*--pos m (p ℕ+ n ℕ* p)
        | -pos-*-pos (m ℕ* suc n) p
        | ℕ.*-assoc m (suc n) p = refl
*-assoc (pos m) (neg-suc n) (neg-suc p)
  rewrite -pos-*-neg-suc (m ℕ* suc n) p
        | ℕ.*-assoc m (suc n) (suc p)
        = refl
*-assoc (neg-suc m) (pos n) (pos p)
  rewrite -pos-*-pos (n ℕ+ m ℕ* n) p
        | ℕ.+-*-distribʳ n (m ℕ* n) p
        | ℕ.*-assoc m n p
        = refl
*-assoc (neg-suc m) (pos n) (neg-suc p)
  rewrite neg-suc-*--pos m (n ℕ* suc p)
        | -pos-*-neg-suc (n ℕ+ m ℕ* n) p
        | ℕ.+-*-distribʳ n (m ℕ* n) (suc p)
        | ℕ.*-assoc m n (suc p)
        = refl
*-assoc (neg-suc m) (neg-suc n) (pos p)
  rewrite neg-suc-*--pos m (p ℕ+ n ℕ* p)
        | ℕ.+-*-distribʳ n (m ℕ* suc n) p
        | Eq.sym (ℕ.+-assoc p (n ℕ* p) (m ℕ* suc n ℕ* p))
        | ℕ.*-assoc m (suc n) p
        = refl
*-assoc (neg-suc m) (neg-suc n) (neg-suc p)
  rewrite ℕ.+-*-distribʳ n (m ℕ* suc n) (suc p)
        | Eq.sym (ℕ.+-assoc p (n ℕ* suc p) (m ℕ* suc n ℕ* suc p))
        | ℕ.*-assoc m (suc n) (suc p)
        = refl

*-comm : ∀ (m n : ℤ) → m * n ≡ n * m
*-comm (pos m) (pos n) rewrite ℕ.*-comm m n = refl
*-comm (pos m) (neg-suc n) rewrite ℕ.*-suc m n | ℕ.*-comm m n = refl
*-comm (neg-suc m) (pos n) rewrite ℕ.*-suc n m | ℕ.*-comm n m = refl
*-comm (neg-suc m) (neg-suc n)
  rewrite ℕ.*-suc m n
        | ℕ.*-suc n m
        | Eq.sym (ℕ.+-assoc n m (m ℕ* n))
        | Eq.sym (ℕ.+-assoc m n (n ℕ* m))
        | ℕ.+-comm m n
        | ℕ.*-comm n m
        = refl

--abs-*-ℕˡ : ∀ (m : ℤ) (n : ℕ) → ∣ m ∣ * n ≡ pos (

ℕ--from-pos : ∀ (m n : ℕ) → pos m - pos n ≡ m ℕ- n
ℕ--from-pos m zero rewrite ℕ.+-identityʳ m = refl
ℕ--from-pos m (suc n) = refl

ℕ--ℕ+-cancelʳ : ∀ (m n : ℕ) → (m ℕ+ n) ℕ- m ≡ pos n
ℕ--ℕ+-cancelʳ zero n = refl
ℕ--ℕ+-cancelʳ (suc m) n = ℕ--ℕ+-cancelʳ m n

ℕ--ℕ+-cancelˡ : ∀ (m n : ℕ) → m ℕ- (m ℕ+ n) ≡ - pos n
ℕ--ℕ+-cancelˡ zero zero = refl
ℕ--ℕ+-cancelˡ zero (suc n) = refl
ℕ--ℕ+-cancelˡ (suc m) n = ℕ--ℕ+-cancelˡ m n

factor-neg : ∀ (m n : ℤ) → (- m) + (- n) ≡ (- (m + n))
factor-neg (pos zero) n rewrite +-identityˡ (- n) | +-identityˡ n = refl
factor-neg (pos (suc m)) (pos zero) rewrite ℕ.+-identityʳ m  = refl
factor-neg (pos (suc m)) (pos (suc n)) rewrite ℕ.+-suc m n = refl
factor-neg (pos (suc m)) (neg-suc n) = ℕ--comm n m
factor-neg (neg-suc m) (pos zero) rewrite ℕ.+-identityʳ m = refl
factor-neg (neg-suc m) (pos (suc n)) = ℕ--comm m n
factor-neg (neg-suc m) (neg-suc n) rewrite ℕ.+-suc m n = refl

*-suc-pos : ∀ (m : ℕ) (n : ℤ) → pos (suc m) * n ≡ n + (pos m * n)
*-suc-pos zero n rewrite *-identityˡ n | *-zeroˡ n | +-identityʳ n = refl
*-suc-pos (suc m) (pos n) = refl
*-suc-pos (suc m) (neg-suc n) rewrite ℕ.+-suc n (n ℕ+ m ℕ* suc n) = refl

*-suc-neg-suc : ∀ (m : ℕ) (n : ℤ) → neg-suc (suc m) * n ≡ (- n) + (neg-suc m * n)
*-suc-neg-suc zero (pos n) rewrite ℕ.+-identityʳ n | factor-neg (pos n) (pos n) = refl
*-suc-neg-suc zero (neg-suc n) = refl
*-suc-neg-suc (suc m) (pos n) rewrite factor-neg (pos n) (pos (n ℕ+ (n ℕ+ m ℕ* n))) = refl
*-suc-neg-suc (suc m) (neg-suc n) = refl

ℕ--distribʳ-* : ∀ (m n : ℕ) (p : ℤ) → (m ℕ- n) * p ≡ (pos m) * p - (pos n) * p
ℕ--distribʳ-* m zero p rewrite *-zeroˡ p | +-identityʳ (pos m * p) = refl
ℕ--distribʳ-* zero (suc n) p rewrite *-zeroˡ p | +-identityˡ (- (pos (suc n) * p)) | neg-distrib-* (pos (suc n)) p = refl
ℕ--distribʳ-* (suc m) (suc n) p
  rewrite *-suc-pos m p
        | *-suc-pos n p
        | Eq.sym (factor-neg p (pos n * p))
        | +-comm p (pos m * p)
        | +-assoc (pos m * p) p (- p + - (pos n * p))
        | Eq.sym (+-assoc p (- p) (- (pos n * p)))
        | +-invʳ p
        | +-identityˡ (- (pos n * p))
        = ℕ--distribʳ-* m n p

ℕ--distribˡ : ∀ (m n : ℕ) (p : ℤ) → (m ℕ- suc n) * p ≡ (pos m * p) + (neg-suc n * p)
ℕ--distribˡ zero n p rewrite *-zeroˡ p | +-identityˡ (neg-suc n * p) = refl
ℕ--distribˡ (suc m) zero (pos p)
  rewrite ℕ.+-identityʳ p
        | ℕ--from-pos (p ℕ+ m ℕ* p) p
        | ℕ--ℕ+-cancelʳ p (m ℕ* p)
        = refl
ℕ--distribˡ (suc m) zero (neg-suc p)
  rewrite ℕ.+-identityʳ p
        | ℕ--ℕ+-cancelˡ p (m ℕ* suc p)= refl
ℕ--distribˡ (suc m) (suc n) p
  rewrite ℕ--distribˡ m n p
        | *-suc-pos m p
        | *-suc-neg-suc n p
        | +-comm p (pos m * p)
        | Eq.sym (+-assoc ((pos m * p) + p) (- p) (neg-suc n * p))
        | +-assoc (pos m * p) p (- p)
        | +-invʳ p
        | +-identityʳ (pos m * p)
        = refl

+-*-distribʳ : ∀ (m n p : ℤ) → (m + n) * p ≡ (m * p) + (n * p)
+-*-distribʳ (pos m) (pos n) (pos p) rewrite ℕ.+-*-distribʳ m n p = refl
+-*-distribʳ (pos m) (pos n) (neg-suc p)
  rewrite factor-neg (pos (m ℕ* suc p)) (pos (n ℕ* suc p))
        | ℕ.+-*-distribʳ m n (suc p)
        = refl
+-*-distribʳ (pos m) (neg-suc n) p = ℕ--distribˡ m n p
+-*-distribʳ (neg-suc m) (pos n) p
  rewrite ℕ--distribˡ n m p
        = +-comm (pos n * p) (neg-suc m * p)
+-*-distribʳ (neg-suc m) (neg-suc n) (pos p)
  rewrite factor-neg (pos (p ℕ+ m ℕ* p)) (pos (p ℕ+ n ℕ* p))
        | ℕ.+-*-distribʳ m n p
        | ℕ.+-assoc p (m ℕ* p) (p ℕ+ n ℕ* p)
        | Eq.sym (ℕ.+-assoc p (m ℕ* p) (n ℕ* p))
        | ℕ.+-comm p (m ℕ* p)
        | ℕ.+-assoc (m ℕ* p) p (n ℕ* p)
        = refl
+-*-distribʳ (neg-suc m) (neg-suc n) (neg-suc p)
  rewrite ℕ.+-*-distribʳ m n (suc p)
        | ℕ.+-assoc p (m ℕ* suc p) (suc p ℕ+ n ℕ* suc p)
        | Eq.sym (ℕ.+-assoc (m ℕ* suc p) (suc p) (n ℕ* suc p))
        | ℕ.+-comm (m ℕ* suc p) (suc p)
        | ℕ.+-assoc p (m ℕ* suc p) (n ℕ* suc p)
        = refl
