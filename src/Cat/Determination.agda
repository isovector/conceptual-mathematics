{-# OPTIONS --type-in-type #-}

open import Cat.Raw

module Cat.Determination {C : Category} (L : LawfulCategory C) where

open Category C
open LawfulCategory L

record Determination {a b c : Obj} (h : a ⇒ c) (f : a ⇒ b) : Set where
  field
    retract : b ⇒ c
    commutes : retract ∘ f ≈ h

Retraction : {a b : Obj} → (h : a ⇒ b) → Set
Retraction = Determination id

