module Cat.Base where

open import Relation.Binary
  using (Rel; IsEquivalence; Setoid; Reflexive; Transitive)
open import Level
  public
open import Algebra.Definitions
open import Function using (flip)


record Category (c ℓ : Level) : Set (suc c ⊔ suc ℓ) where
  infix 3 _≈_ _⇒_
  infixr 7 _∘_
  field
    Obj : Set c
    _⇒_ : Rel Obj ℓ
    _≈_ : {x y : Obj} → Rel (x ⇒ y) ℓ
    equiv : {x y : Obj} → IsEquivalence (_≈_ {x} {y})
    id : Reflexive _⇒_
    _∘_ : Transitive (flip _⇒_)
    ∘-identityˡ : ∀ {X Y} (f : X ⇒ Y) → id ∘ f ≈ f
    ∘-identityʳ : ∀ {X Y} (f : X ⇒ Y) → f ∘ id ≈ f
    ∘-assoc : ∀ {A B C D : Obj} (h : C ⇒ D) (g : B ⇒ C) (f : A ⇒ B) → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    ∘-cong : ∀ {X Y Z} {f f′ : X ⇒ Y} {g g′ : Y ⇒ Z} → g ≈ g′ → f ≈ f′ → g ∘ f ≈ g′ ∘ f′

  module Reasoning {x y : Obj} where
    setoid : Setoid ℓ _
    Setoid.Carrier (setoid) = x ⇒ y
    Setoid._≈_ setoid = _≈_
    Setoid.isEquivalence setoid = equiv

    open import Relation.Binary.Reasoning.Setoid setoid
      public

    open IsEquivalence (Setoid.isEquivalence setoid) public

