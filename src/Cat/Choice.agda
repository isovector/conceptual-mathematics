{-# OPTIONS --type-in-type #-}

open import Cat.Raw

module Cat.Choice {C : Category} (L : LawfulCategory C) where

open Category C
open LawfulCategory L

record Choice {a b c : Obj} (h : a ⇒ c) (f : b ⇒ c) : Set where
  field
    section : a ⇒ b
    commutes : f ∘ section ≈ h

Section : {b c : Obj} → (h : b ⇒ c) → Set
Section = Choice id

