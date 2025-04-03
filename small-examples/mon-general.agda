module mon-general where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import hom-cat
open import monoid

open Category
open Monoid

cat : ∀ (M : Monoid) → Category
cat M = record
      { Obj   = mObj
      ; Hom   = mHom
      ; id    = mId
      ; comp  = _*_ M
      ; assoc = mAssoc
      ; idL   = mIdL
      ; idR   = mIdR
      }
      where
            mObj : Set
            mObj = ⊤

            mHom : ⊤ → ⊤ → Set
            mHom _ _ = Carrier M

            mComp : Carrier M →  Carrier M → Carrier M
            mComp = _*_ M

            mId : Carrier M
            mId = ε M

            mAssoc : (a b c : Carrier M) → _*_ M a (_*_ M b c) ≡ _*_ M (_*_ M a b) c
            mAssoc a b c = monAssoc M

            mIdL : (a : Carrier M) → _*_ M mId a ≡ a
            mIdL a = monIdL M

            mIdR : (a : Carrier M) → _*_ M a mId ≡ a
            mIdR a = monIdR M

{- It is possible to define the Objects, Homs, ect... of the category outside the
record as follows:

mObj : ∀ (M : Monoid) → Set
mObj M = ⊤

mHom : ∀ (M : Monoid) → ⊤ → ⊤ → Set
mHom M _ _ = Carrier M

mComp : ∀ (M : Monoid) → (a b : Carrier M) → Carrier M
mComp M = _*_ M

mId : ∀ (M : Monoid) → Carrier M
mId M = ε M

mAssoc : ∀ (M : Monoid) → (a b c : Carrier M) → _*_ M a (_*_ M b c) ≡ _*_ M (_*_ M a b) c
mAssoc M a b c = monAssoc M

mIdL : ∀ (M : Monoid) → (a : Carrier M) → _*_ M (mId M) a ≡ a
mIdL M f = monIdL M

mIdR : ∀ (M : Monoid) → (a : Carrier M) → _*_ M a (mId M) ≡ a
mIdR M a = monIdR M
-}
