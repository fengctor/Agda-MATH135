module Agda-MATH135.Divisibility where

open import Agda-MATH135.Integer.Integer
open import Agda-MATH135.Integer.Properties

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

infix 4 _∣_ _∤_

data _∣_ (m n : ℤ) : Set where
  divs : (k : ℤ) → k * m ≡ n → m ∣ n

_∤_ : (m n : ℤ) → Set
m ∤ n = ¬ (m ∣ n)

div-trans : ∀ {m n p : ℤ} → m ∣ n → n ∣ p → m ∣ p
div-trans {m} (divs k refl) (divs l refl) = divs (l * k) (*-assoc l k m)

div-* : ∀ {m n p : ℤ} → (m ∣ n) ⊎ (m ∣ p) → m ∣ (n * p)
div-* {m} {n} {p} (inj₁ (divs k refl))
  rewrite *-assoc k m p
        | *-comm m p
        | Eq.sym (*-assoc k p m)
        = divs (k * p) refl
div-* {m} {n} {p} (inj₂ (divs k refl))
  rewrite Eq.sym (*-assoc n k m)
        = divs (n * k) refl

DIC : ∀ {m n p a b : ℤ} → m ∣ n → m ∣ p → m ∣ ((a * n) + (b * p))
DIC {m} {a = a} {b = b} (divs k refl) (divs l refl) with +-*-distribʳ (a * k) (b * l) m
... | [a*k+b*l]*m≡a*k*m+b*l*m
  rewrite *-assoc a k m
        | *-assoc b l m
        = divs ((a * k) + (b * l)) [a*k+b*l]*m≡a*k*m+b*l*m
