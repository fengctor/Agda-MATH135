module Agda-MATH135.Natural.Divisibility where

open import Agda-MATH135.Natural.Properties

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Nullary using (¬_)

infix 4 _∣_ _∤_

data _∣_ (m n : ℕ) : Set where
  divs : (k : ℕ) → k * m ≡ n → m ∣ n

_∤_ : (m n : ℕ) → Set
m ∤ n = ¬ (m ∣ n)

div-trans : ∀ {m n p : ℕ} → m ∣ n → n ∣ p → m ∣ p
div-trans {m = m} (divs k refl) (divs l refl) = divs (l * k) (*-assoc l k m)

div-* : ∀ {m n p : ℕ} → (m ∣ n) ⊎ (m ∣ p) → m ∣ (n * p)
div-* {m = m} {p = p} (inj₁ (divs k refl))
  rewrite *-assoc k m p
        | *-comm m p
        | Eq.sym (*-assoc k p m)
        = divs (k * p) refl
div-* {m = m} {n = n} (inj₂ (divs k refl)) = divs (n * k) (*-assoc n k m)

DNC : ∀ {m n p a b : ℕ} → m ∣ n → m ∣ p → m ∣ ((a * n) + (b * p))
DNC {m} {n} {p} {a} {b} (divs k refl) (divs l refl)
  with +-*-distribʳ (a * k) (b * l) m
...  | dist rewrite *-assoc a k m
                  | *-assoc b l m
                  = divs (a * k + b * l) dist
