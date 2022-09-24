{-# OPTIONS --type-in-type #-}

open import Cat.Raw

module Cat.Iso {C : Category} (L : LawfulCategory C) where

module _ where
  open LawfulCategory L

  record Isomorphism (a b : Obj) : Set where
    constructor mk-iso
    field
      fwd : a ⇒ b
      bwd : b ⇒ a
      fwd-bwd : fwd ∘ bwd ≈ id
      bwd-fwd : bwd ∘ fwd ≈ id

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
fwd-bwd (_∘_ ISO g f)
  = [∘]∘[∘]→∘[[∘]∘] L
  ▹ (∘-congʳ L ( ∘-congˡ L (fwd-bwd f)
               ▹ id-l L
               )
    )
  ▹ fwd-bwd g
  where open HomReasoning L
bwd-fwd (Category._∘_ ISO g f)
  = [∘]∘[∘]→∘[[∘]∘] L
  ▹ (∘-congʳ L ( ∘-congˡ L (bwd-fwd g)
               ▹ id-l L
               )
    )
  ▹ bwd-fwd f
  where open HomReasoning L

open import Data.Unit

record IsoExt {a b : Obj C} (f g : Isomorphism a b) : Set where
  field
    fwd-ext : _≈_ L (f .fwd) (g .fwd)
    bwd-ext : _≈_ L (f .bwd) (g .bwd)

open IsoExt

open import Relation.Binary.Structures using (IsEquivalence)

ISO-laws : LawfulCategory ISO
_≈_ ISO-laws = IsoExt
fwd-ext (IsEquivalence.refl (≈-equiv ISO-laws)) = IsEquivalence.refl (≈-equiv L)
bwd-ext (IsEquivalence.refl (≈-equiv ISO-laws)) = IsEquivalence.refl (≈-equiv L)
fwd-ext (IsEquivalence.sym (≈-equiv ISO-laws) x) = IsEquivalence.sym (≈-equiv L) (fwd-ext x)
bwd-ext (IsEquivalence.sym (≈-equiv ISO-laws) x) = IsEquivalence.sym (≈-equiv L) (bwd-ext x)
fwd-ext (IsEquivalence.trans (≈-equiv ISO-laws) x y) = IsEquivalence.trans (≈-equiv L) (fwd-ext x) (fwd-ext y)
bwd-ext (IsEquivalence.trans (≈-equiv ISO-laws) x y) = IsEquivalence.trans (≈-equiv L) (bwd-ext x) (bwd-ext y)
fwd-ext (∘-cong ISO-laws x y) = ∘-cong L (fwd-ext x) (fwd-ext y)
bwd-ext (∘-cong ISO-laws x y) = ∘-cong L (bwd-ext y) (bwd-ext x)
fwd-ext (id-l ISO-laws) = id-l L
bwd-ext (id-l ISO-laws) = id-r L
fwd-ext (id-r ISO-laws) = id-r L
bwd-ext (id-r ISO-laws) = id-l L
fwd-ext (∘-assoc ISO-laws) = ∘-assoc L
bwd-ext (∘-assoc ISO-laws) = ⨟-assoc L

