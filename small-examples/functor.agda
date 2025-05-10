module functor where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import hom-cat

record Functor (C₁ D₁ : Category) : Set₁ where
  -- eta-equality
  private
   module C = Category C₁
   module D = Category D₁

  field
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {A B} (f : C.Hom A B) → D.Hom (F₀ A) (F₀ B)

    id   : ∀ {A} → C.Hom A A ≡ D.Hom (F₀ A) (F₀ A)
    comp : ∀ {A B C} (f : C.Hom A B) (g : C.Hom B C) → F₁ (C.comp f g)
           ≡ D.comp (F₁ f) (F₁ g)
