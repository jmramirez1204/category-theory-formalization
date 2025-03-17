module hom-cat where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

record Category : Set₁ where

  field
    Obj : Set
    Hom : Obj → Obj → Set

    id   : ∀ {A} → Hom A A
    comp : ∀ {A B C} → Hom A B → Hom B C → Hom A C

    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D) →
            comp f (comp g h) ≡ (comp (comp f g) h)
    idL   : ∀ {A B} (f : Hom A B) → comp id f ≡ f
    idR   : ∀ {A B} (f : Hom A B) → comp f id ≡ f

