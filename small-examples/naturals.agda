module naturals where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; _+_; zero)
open import small-cat

open Nat

variable
  k l m n : Nat

-- Type of the arrows
data _≤_ : Nat → Nat  → Set where
  ≤-zero :          zero ≤ n
  ≤-suc  : m ≤ n → suc m ≤ suc n

-- Identity
≤-refl : n ≤ n
≤-refl {n = zero}  = ≤-zero
≤-refl {n = suc k} = ≤-suc ≤-refl

-- Composition
≤-trans : l ≤ m → k ≤ l → k ≤ m
≤-trans k≤l         ≤-zero     = ≤-zero
≤-trans (≤-suc l≤m)(≤-suc k≤l) = ≤-suc (≤-trans l≤m k≤l)

-- Identity left law
≤-IdL : {m n : Nat}(f : m ≤ n) → (≤-trans ≤-refl f) ≡ f
≤-IdL ≤-zero    = refl
≤-IdL (≤-suc f) = cong ≤-suc (≤-IdL f)

-- Identity right law
≤-IdR : {m n : Nat}(f : m ≤ n) →  (≤-trans f ≤-refl) ≡ f
≤-IdR ≤-zero    = refl
≤-IdR (≤-suc f) = cong ≤-suc (≤-IdR f)

-- Associativity law
≤-trans-assoc : {k l m n : Nat} → (f : k ≤ l) (g : l ≤ m ) (h : m ≤ n)
                → ≤-trans h (≤-trans g f) ≡ ≤-trans (≤-trans h g) f
≤-trans-assoc ≤-zero g h                  = refl
≤-trans-assoc (≤-suc f)(≤-suc g)(≤-suc h) = cong ≤-suc (≤-trans-assoc f g h)

-- Natural numbers as a category
naturalsCategory : Category
naturalsCategory = record
                 { Obj   = Nat
                 ; _⇒_   = λ A B → A ≤ B
                 ; id    = ≤-refl
                 ; _∘_   = ≤-trans
                 ; idL   = ≤-IdL _
                 ; idR   = ≤-IdR _
                 ; assoc = ≤-trans-assoc _ _ _
                 }
