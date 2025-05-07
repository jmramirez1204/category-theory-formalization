module mon2-cat where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import hom-cat
open Category

-- (ℕ, *, 1)

-- Definition of ℕ
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

-- Definition of + for ℕ
_+_ : Nat → Nat → Nat
zero + n    = n
(suc m) + n = suc (m + n)

-- Definition of * for ℕ
_*_ : Nat → Nat → Nat
zero    * n = zero
(suc m) * n = n + (m * n)

-- Object of the category
record ⊤ : Set where

-- Hom sets
monHom : (⊤ ⊤ : ⊤) → Set
monHom ⊤ ⊤ = Nat

-- Identity
monId : {⊤ : ⊤} → monHom ⊤ ⊤
monId = suc zero

-- Composition
monComp : {⊤ : ⊤} → monHom ⊤ ⊤ → monHom ⊤ ⊤ → monHom ⊤ ⊤
monComp m n = m * n

-- Associativity of +
+-assoc : ∀ (m n p : Nat) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- Distribitivity of * over +
+*-dist : ∀ (m n p : Nat) → (m + n) * p ≡ (m * p) + (n * p)
+*-dist zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
    n * p
  ∎
+*-dist (suc m) n p =
  begin
    ((suc m) + n) * p
  ≡⟨⟩
    (suc (m + n)) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (_+_ p) (+*-dist m n p)⟩ -- cong (_+_ p) aplica parcialmente la suma
    p + ((m * p) + (n * p))
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + (m * p)) + (n * p)
  ≡⟨⟩
    ((suc m) * p) + (n * p)
  ∎

-- Associativity of the monoid
monAssoc : {⊤ : ⊤} → (m : monHom ⊤ ⊤) → (n : monHom ⊤ ⊤) → (l : monHom ⊤ ⊤)
           → m * (n * l) ≡ (m * n) * l
monAssoc zero n l    = refl
monAssoc (suc m) n l =
  begin
    (suc m) * (n * l)
  ≡⟨⟩
    (n * l) + (m * (n * l))
  ≡⟨ cong (_+_ (n * l)) (monAssoc m n l)⟩
    (n * l) + ((m * n) * l)
  ≡⟨ sym (+*-dist n (m * n) l) ⟩
    (n + (m * n)) * l
  ≡⟨⟩
    ((suc m) * n) * l
  ∎

-- Left identity law
monIdL : {⊤ : ⊤} → (m : monHom ⊤ ⊤) → monComp monId m ≡ m
monIdL zero    = refl
monIdL (suc m) = cong suc (monIdL m)

-- Right identity law
monIdR : {⊤ : ⊤} → (m : monHom ⊤ ⊤) → monComp m monId ≡ m
monIdR zero    = refl
monIdR (suc m) = cong suc (monIdR m)

-- Monoid as a category
monCat : Category
monCat = record
       { Obj   = ⊤
       ; Hom   = monHom
       ; id    = monId
       ; comp  = monComp
       ; assoc = monAssoc
       ; idL   = monIdL
       ; idR   = monIdR
       }
