module monoids where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import hom-cat

open Category

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero + m  = m
suc n + m = suc (n + m)

-- Object
record ⊤ : Set where

-- Hom
monHom : (⊤ ⊤ : ⊤) → Set
monHom ⊤ ⊤ = Nat

-- Id
monId : {⊤ : ⊤} → monHom ⊤ ⊤
monId  = zero

-- Comp
monComp : {⊤ : ⊤} → monHom ⊤ ⊤ → monHom ⊤ ⊤ → monHom ⊤ ⊤
monComp m n = m + n

-- Assoc
monAssoc : {⊤ : ⊤} → (m : monHom ⊤ ⊤) → (n : monHom ⊤ ⊤) → (l : monHom ⊤ ⊤)
           → monComp m (monComp n l) ≡ monComp (monComp m n) l
monAssoc zero n l    = refl
monAssoc (suc m) n l = cong suc (monAssoc m n l)

-- IdL
monIdL : {⊤ : ⊤} → (m : monHom ⊤ ⊤) → monComp monId m ≡ m
monIdL zero    = refl
monIdL (suc m) = cong suc (monIdL m)

-- IdR
monIdR : {⊤ : ⊤} → (m : monHom ⊤ ⊤) → monComp m monId ≡ m
monIdR zero    = refl
monIdR (suc m) = cong suc (monIdR m)

-----------------------------------------------------
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
