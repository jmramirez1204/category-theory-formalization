module new-nat where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; _+_; zero)
open import hom-cat

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
≤-trans : k ≤ l → l ≤ m → k ≤ m
≤-trans  ≤-zero l≤m     = ≤-zero
≤-trans (≤-suc k≤l)(≤-suc l≤m) = ≤-suc (≤-trans k≤l l≤m)

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
              → ≤-trans f (≤-trans g h) ≡ ≤-trans (≤-trans f g) h
≤-trans-assoc ≤-zero g h                  = refl
≤-trans-assoc (≤-suc f)(≤-suc g)(≤-suc h) = cong ≤-suc (≤-trans-assoc f g h)

natCat : Category
natCat = record
         { Obj   = Nat
         ; Hom   = _≤_
         ; id    = ≤-refl
         ; comp  = ≤-trans
         ; assoc = ≤-trans-assoc
         ; idL   = ≤-IdL
         ; idR   = ≤-IdR
         }
