module monoid where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; _+_; zero)
open import hom-cat

open Nat

record Monoid : Set₁ where
  field
    Carrier : Set
    _*_     : Carrier → Carrier → Carrier
    ε       : Carrier

  field
    monAssoc : ∀ {x y z} → x * (y * z) ≡ (x * y) * z
    monIdL   : ∀ {x} → ε * x ≡ x
    monIdR   : ∀ {x} → x * ε ≡ x

record ⊤ : Set where


