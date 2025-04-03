module monoids where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; _+_; zero)
open import hom-cat

open Category
open Nat

-- Object
record ⊤ : Set where

-- Hom sets
monHom : (⊤ ⊤ : ⊤) → Set
monHom ⊤ ⊤ = Nat

-- Identity
monId : {⊤ : ⊤} → monHom ⊤ ⊤
monId  = zero

-- Composition
monComp : {⊤ : ⊤} → monHom ⊤ ⊤ → monHom ⊤ ⊤ → monHom ⊤ ⊤
monComp m n = m + n

-- Associativity
monAssoc : {⊤ : ⊤} → (m : monHom ⊤ ⊤) → (n : monHom ⊤ ⊤) → (l : monHom ⊤ ⊤)
           → monComp m (monComp n l) ≡ monComp (monComp m n) l
monAssoc zero n l    = refl
monAssoc (suc m) n l = cong suc (monAssoc m n l)

-- Identity left law
monIdL : {⊤ : ⊤} → (m : monHom ⊤ ⊤) → monComp monId m ≡ m
monIdL zero    = refl
monIdL (suc m) = cong suc (monIdL m)

-- Identity right law
monIdR : {⊤ : ⊤} → (m : monHom ⊤ ⊤) → monComp m monId ≡ m
monIdR zero    = refl
monIdR (suc m) = cong suc (monIdR m)

-- Monoid as a Category
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
