module small-cat where

open import Relation.Binary.PropositionalEquality using (_≡_)

record Category : Set₁ where
  field
    Obj   : Set
    _⇒_   : (A B : Obj) → Set
    _∘_   : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
    id    : ∀ {A : Obj} → A ⇒ A
    idL   : ∀ {A B : Obj} {f : A ⇒ B} → (id ∘ f) ≡ f
    idR   : ∀ {A B : Obj} {f : A ⇒ B} → (f ∘ id) ≡ f
    assoc : ∀ {A B C D : Obj} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
               → h ∘ (g ∘ f)  ≡ (h ∘ g) ∘ f
