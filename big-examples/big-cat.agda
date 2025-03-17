module big-cat where

open import Relation.Binary.PropositionalEquality using (_≡_)

record Category : Set₂ where
  field
    Obj      : Set₁
    _⇒_      : (A B : Obj) → Set
    _∘_      : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
    id       : ∀ {A : Obj} → A ⇒ A
    id-left  : ∀ {A B : Obj} {f : A ⇒ B} → (id ∘ f) ≡ f
    id-right : ∀ {A B : Obj} {f : A ⇒ B} → (f ∘ id) ≡ f
    assoc    : ∀ {A B C D : Obj} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
               → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
