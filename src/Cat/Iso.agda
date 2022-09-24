{-# OPTIONS --type-in-type #-}

open import Cat.Raw

module Cat.Iso {C : Category} (L : LawfulCategory C) where

module _ where
  open LawfulCategory L

  record Isomorphism (a b : Obj) : Set where
    field
      fwd : a ⇒ b
      bwd : b ⇒ a
      fwd-bwd : fwd ∘ bwd ≈ id
      bwd-fwd : bwd ∘ fwd ≈ id

module _ where
  open LawfulCategory L


  [∘]∘[∘]→∘[[∘]∘]
    : ∀ {a b c d e : Obj} {f : a ⇒ b} {g : b ⇒ c} {h : c ⇒ d} {i : d ⇒ e}
    → (i ∘ h) ∘ (g ∘ f) ≈ i ∘ ((h ∘ g) ∘ f)
  [∘]∘[∘]→∘[[∘]∘] = trans ∘-assoc (∘-congʳ (sym ∘-assoc))
    where open HomReasoning

open Category
open LawfulCategory hiding (Obj; id; _∘_; _⇒_)
open Isomorphism

ISO : Category
Category.Obj ISO = Obj C
Category._⇒_ ISO = Isomorphism
fwd (id ISO) = id C
bwd (id ISO) = id C
fwd-bwd (id ISO) = id-r L
bwd-fwd (id ISO) = id-r L
fwd ((ISO ∘ g) f) = _∘_ C (fwd g) (fwd f)
bwd ((ISO ∘ g) f) = _∘_ C (bwd f) (bwd g)
fwd-bwd (_∘_ ISO g f) =
  begin
    _∘_ C
      (_∘_ C (fwd g) (fwd f))
      (_∘_ C (bwd f) (bwd g))
  ≈⟨ [∘]∘[∘]→∘[[∘]∘]  ⟩
    _∘_ C (fwd g) (_∘_ C (_∘_ C (fwd f) (bwd f)) (bwd g))
  ≈⟨ ∘-congʳ L (∘-congˡ L (fwd-bwd f)) ⟩
    _∘_ C (fwd g) (_∘_ C (id C) (bwd g))
  ≈⟨ ∘-congʳ L (id-l L) ⟩
    _∘_ C (fwd g) (bwd g)
  ≈⟨ fwd-bwd g ⟩
    id C
  ∎
  where open HomReasoning L
bwd-fwd (Category._∘_ ISO g f) =
  begin
    _∘_ C
      (_∘_ C (bwd f) (bwd g))
      (_∘_ C (fwd g) (fwd f))
  ≈⟨ [∘]∘[∘]→∘[[∘]∘]  ⟩
    _∘_ C (bwd f) (_∘_ C (_∘_ C (bwd g) (fwd g)) (fwd f))
  ≈⟨ ∘-congʳ L (∘-congˡ L (bwd-fwd g)) ⟩
    _∘_ C (bwd f) (_∘_ C (id C) (fwd f))
  ≈⟨ ∘-congʳ L (id-l L) ⟩
    _∘_ C (bwd f) (fwd f)
  ≈⟨ bwd-fwd f ⟩
    id C
  ∎
  where open HomReasoning L

open import Data.Unit

ISO-laws : LawfulCategory ISO
_≈_ ISO-laws _ _ = ⊤
≈-equiv ISO-laws =
  record { refl = λ {x} → tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
∘-cong ISO-laws = λ _ _ → tt
id-l ISO-laws = tt
id-r ISO-laws = tt
∘-assoc ISO-laws = tt

