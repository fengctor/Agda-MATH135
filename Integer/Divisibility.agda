module Agda-MATH135.Integer.Divisibility where

open import Agda-MATH135.Integer
open import Agda-MATH135.Integer.Properties
import Agda-MATH135.Natural.Divisibility as ℕ

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

infix 4 _∣_ _∤_

_∣_ : (m n : ℤ) → Set
m ∣ n = ∣ m ∣ ℕ.∣ ∣ n ∣

_∤_ : (m n : ℤ) → Set
m ∤ n = ∣ m ∣ ℕ.∤ ∣ n ∣

div-trans : ∀ {m n p : ℤ} → m ∣ n → n ∣ p → m ∣ p
div-trans = ℕ.div-trans

div-* : ∀ {m n p : ℤ} → (m ∣ n) ⊎ (m ∣ p) → m ∣ (n * p)
div-* {n = n} {p = p} rewrite abs-* n p = ℕ.div-*

DIC : ∀ {m n p a b : ℤ} → m ∣ n → m ∣ p → m ∣ (a * n + b * p)
DIC {m} {n} {p} {a} {b} with abs-+-either (a * n) (b * p)
... | inj₁ x rewrite x
                   | abs-* a n
                   | abs-* b p
                   = ℕ.DNC {∣ m ∣} {∣ n ∣} {∣ p ∣} {∣ a ∣} {∣ b ∣}
... | inj₂ y rewrite y = lemma
  where
    import Data.Nat as ℕ
    import Agda-MATH135.Natural.Properties as ℕ
    lemmaHelp : ∀ (k l : ℕ.ℕ)
              → ∣ a ∣ ℕ.* k ℕ.* ∣ m ∣ ℕ- ∣ b ∣ ℕ.* l ℕ.* ∣ m ∣
              ≡ ((∣ a ∣ ℕ.* k) ℕ- (∣ b ∣ ℕ.* l)) * pos ∣ m ∣
    lemmaHelp k l
      rewrite ℕ--distribʳ-* (∣ a ∣ ℕ.* k) (∣ b ∣ ℕ.* l) (pos ∣ m ∣)
            = ℕ--as-minus (∣ a ∣ ℕ.* k ℕ.* ∣ m ∣) (∣ b ∣ ℕ.* l ℕ.* ∣ m ∣)
            
    lemma : m ∣ n → m ∣ p → m ∣ (∣ a * n ∣ ℕ- ∣ b * p ∣)
    lemma (ℕ.divs k x) (ℕ.divs l y)
      rewrite abs-* a n
            | abs-* b p
            | Eq.sym x
            | Eq.sym y
            | Eq.sym (ℕ.*-assoc (∣ a ∣) k (∣ m ∣))
            | Eq.sym (ℕ.*-assoc (∣ b ∣) l (∣ m ∣))
            | ℕ--distribʳ-* (∣ a ∣ ℕ.* k) (∣ b ∣ ℕ.* l) (pos ∣ m ∣)
            | lemmaHelp k l
            | abs-* (∣ a ∣ ℕ.* k ℕ- ∣ b ∣ ℕ.* l) (pos ∣ m ∣)
            = ℕ.divs ∣ ∣ a ∣ ℕ.* k ℕ- ∣ b ∣ ℕ.* l ∣ refl
