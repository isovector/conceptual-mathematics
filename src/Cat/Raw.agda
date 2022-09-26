{-# OPTIONS --type-in-type #-}

module Cat.Raw where

record Category : Set where
  infixr 0 _⇒_
  infixr 5 _∘_
  infixr 5 _⨟_
  field
    Obj : Set
    _⇒_ : Obj → Obj → Set
    id : {a : Obj} → a ⇒ a
    _∘_ : {a b c : Obj} → (g : b ⇒ c) → (f : a ⇒ b) → a ⇒ c


  _⨟_ : {a b c : Obj} → (f : a ⇒ b) → (g : b ⇒ c) → a ⇒ c
  _⨟_ f g = g ∘ f


open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

record LawfulCategory (C : Category) : Set where
  open Category C

  infix 0 _≈_

  field
    _≈_ : {a b : Obj} → a ⇒ b → a ⇒ b → Set
    ≈-equiv : {a b : Obj} → IsEquivalence (_≈_ {a} {b})
    ∘-cong : {a b c : Obj}
           → {g g' : b ⇒ c}
           → {f f' : a ⇒ b}
           → g ≈ g'
           → f ≈ f'
           → g ∘ f ≈ g' ∘ f'

    id-l : {a b : Obj} → {f : a ⇒ b} → id ∘ f ≈ f
    id-r : {a b : Obj} → {f : a ⇒ b} → f ∘ id ≈ f
    ∘-assoc : {a b c d : Obj}
            → {h : c ⇒ d}
            → {g : b ⇒ c}
            → {f : a ⇒ b}
            → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

  ∘-congˡ : {a b c : Obj}
          → {g g' : b ⇒ c}
          → {f : a ⇒ b}
          → g ≈ g'
          → g ∘ f ≈ g' ∘ f
  ∘-congˡ g≈ = ∘-cong g≈ (IsEquivalence.refl ≈-equiv)

  ∘-congʳ : {a b c : Obj}
           → {g : b ⇒ c}
           → {f f' : a ⇒ b}
           → f ≈ f'
           → g ∘ f ≈ g ∘ f'
  ∘-congʳ = ∘-cong (IsEquivalence.refl ≈-equiv)

  ⨟-assoc : {a b c d : Obj}
          → {f : a ⇒ b}
          → {g : b ⇒ c}
          → {h : c ⇒ d}
          → (f ⨟ g) ⨟ h ≈ f ⨟ (g ⨟ h)
  ⨟-assoc {f = f} {g} {h} = IsEquivalence.sym ≈-equiv (∘-assoc {h = h} {g} {f})

  setoid : {X Y : Obj} → Setoid _ _
  Setoid.Carrier (setoid {X} {Y}) = X ⇒ Y
  Setoid._≈_ setoid  = _≈_
  Setoid.isEquivalence setoid = ≈-equiv

  module HomReasoning {A B : Obj} where
    open SetoidR (setoid {A} {B}) public
    open IsEquivalence (≈-equiv {A} {B}) public

    infixr 1 _▹_
    _▹_ = trans

  [∘]∘[∘]→∘[[∘]∘]
    : ∀ {a b c d e : Obj} {f : a ⇒ b} {g : b ⇒ c} {h : c ⇒ d} {i : d ⇒ e}
    → (i ∘ h) ∘ (g ∘ f) ≈ i ∘ ((h ∘ g) ∘ f)
  [∘]∘[∘]→∘[[∘]∘] = trans ∘-assoc (∘-congʳ (sym ∘-assoc))
    where open HomReasoning

