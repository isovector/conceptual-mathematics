module Cat.Base where

open import Relation.Binary
  using (Rel; IsEquivalence; Setoid; Reflexive; Transitive)
open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  public
open import Algebra.Definitions
open import Function using (flip)


record Category (c ℓ : Level) : Set (lsuc c ⊔ lsuc ℓ) where
  infix 3 _≈_ _⇒_
  infixr 7 _∘_
  field
    Obj : Set c
    _⇒_ : Rel Obj ℓ
    _≈_ : {x y : Obj} → Rel (x ⇒ y) ℓ
    equiv : {x y : Obj} → IsEquivalence (_≈_ {x} {y})
    id : Reflexive _⇒_
    _∘_ : Transitive (flip _⇒_)
    identityˡ : ∀ {X Y} (f : X ⇒ Y) → id ∘ f ≈ f
    identityʳ : ∀ {X Y} (f : X ⇒ Y) → f ∘ id ≈ f
    assoc : ∀ {A B C D : Obj} (h : C ⇒ D) (g : B ⇒ C) (f : A ⇒ B) → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    cong : ∀ {X Y Z} {f f′ : X ⇒ Y} {g g′ : Y ⇒ Z} → g ≈ g′ → f ≈ f′ → g ∘ f ≈ g′ ∘ f′

  module Reasoning {x y : Obj} where
    setoid : Setoid ℓ _
    Setoid.Carrier (setoid) = x ⇒ y
    Setoid._≈_ setoid = _≈_
    Setoid.isEquivalence setoid = equiv

    open import Relation.Binary.Reasoning.Setoid setoid
      public

    open IsEquivalence (Setoid.isEquivalence setoid) public

  congʳ : {A B C : Obj} {g h : A ⇒ B} {f : B ⇒ C} → g ≈ h → f ∘ g ≈ f ∘ h
  congʳ = cong (equiv .IsEquivalence.refl)

  congˡ : {A B C : Obj} {g h : B ⇒ C} {f : A ⇒ B} → g ≈ h → g ∘ f ≈ h ∘ f
  congˡ x = cong x (equiv .IsEquivalence.refl)

  reassoc : ∀ {A B C D : Obj} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
  reassoc {h = h} {g} {f} = assoc h g f

  assoc-in : ∀ {A B C D E} → (f : D ⇒ E) → (g : C ⇒ D) → (h : B ⇒ C) → (i : A ⇒ B) → (f ∘ g) ∘ (h ∘ i) ≈ f ∘ ((g ∘ h) ∘ i)
  assoc-in f g h i = begin
    (f ∘ g) ∘ (h ∘ i)  ≈⟨ reassoc ⟩
    f ∘ (g ∘ (h ∘ i))  ≈⟨ congʳ (sym reassoc) ⟩
    f ∘ ((g ∘ h) ∘ i)  ∎
    where open Reasoning

  reassoc-in : ∀ {A B C D E} → {f : D ⇒ E} → {g : C ⇒ D} → {h : B ⇒ C} → {i : A ⇒ B} → (f ∘ g) ∘ (h ∘ i) ≈ f ∘ ((g ∘ h) ∘ i)
  reassoc-in {f = f} {g} {h} {i} = assoc-in f g h i

