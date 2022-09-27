{-# OPTIONS --type-in-type #-}

open import Cat.Raw

module Cat.Determination {C : Category} (L : LawfulCategory C) where

open Category C
open LawfulCategory L

record Determination {a b c : Obj} (h : a ⇒ c) (f : a ⇒ b) : Set where
  constructor determines
  field
    retract : b ⇒ c
    commutes : retract ∘ f ≈ h

HasRetraction : {a b : Obj} → (h : a ⇒ b) → Set
HasRetraction = Determination id



module Properties where

  open import Data.Product

  HasFixedPointProperty : Obj → Obj → Set
  HasFixedPointProperty A B = (f : A ⇒ A) → Σ (B ⇒ A) (λ x → f ∘ x ≈ x)

  p126ex2
    : {A X : Obj}
    → (s : A ⇒ X)
    → (r : HasRetraction s)
    → (T : Obj)
    → HasFixedPointProperty X T
    → HasFixedPointProperty A T
  p126ex2 s (determines r comm) T fp-x f with fp-x (s ∘ f ∘ r)
  ... | x , proof
      = f ∘ r ∘ x , ( ∘-congˡ (sym id-r ▹ ∘-congʳ (sym comm))
                    ▹ ∘-assoc
                    ▹ ∘-congʳ (∘-assoc ▹ ∘-congʳ (sym ∘-assoc ▹ sym ∘-assoc ▹ ∘-congˡ ∘-assoc))
                    ▹ sym ∘-assoc
                    ▹ ∘-congʳ proof
                    ▹ ∘-assoc
                    )
    where open HomReasoning

