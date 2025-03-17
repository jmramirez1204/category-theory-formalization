module set where

open import big-cat
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

setCategory : Category
setCategory = record
            { Obj      = Set
            ; _⇒_      = λ A B → A → B
            ; id       = λ x → x
            ; _∘_      = λ f g x → f (g x)
            ; id-left  = refl
            ; id-right = refl
            ; assoc    = refl
            }
