open import Cat.Base

module Constr.Automorphism {ℓ₁ ℓ₂ : Level} (c : Category ℓ₁ ℓ₂) where

open import Constr.Iso
open import Data.Product

module Definition {ℓ₁ ℓ₂ : Level} (c : Category ℓ₁ ℓ₂) where
  open Category c

  private variable
    A B C T : Obj
    f : A ⇒ B
    g : B ⇒ C

  -- DEFINITION, page 54
  IsIsomorphism′ : A ⇒ B → Set ℓ₂
  IsIsomorphism′ {A = A} {B = B} f
    = Σ[ f⁻¹ ∈ B ⇒ A ] ( f   ∘ f⁻¹ ≈ id {B}
                       × f⁻¹ ∘ f   ≈ id {A}
                       )

  -- EXERCISE 11, page 55
  -- f Fatima = coffee
  -- f Omer   = tea
  -- f Alysia = cocoa

  -- There are 3! automorphisms

  -- DEFINITION, page 54
  Automorphism : {A : Obj} → A ⇒ A → Set ℓ₂
  Automorphism = IsIsomorphism c

  -- DEFINITION, page 55
  Aut : (A : Obj) → Set ℓ₂
  Aut A = Σ (A ⇒ A) Automorphism

  -- DEFINITION, page 55
  Isom : (A B : Obj) → Set ℓ₂
  Isom A B = Σ (A ⇒ B) (IsIsomorphism c)


module _ where
  open import Cat.SET ℓ₂
  open Category c
  open Definition c
  open import Relation.Binary.PropositionalEquality

  _≅∘_ : {A B C : Obj} → Σ (B ⇒ C) (IsIsomorphism c) → Σ (A ⇒ B) (IsIsomorphism c) → Σ (A ⇒ C) (IsIsomorphism c)
  _≅∘_ = iso-trans c

  aut-iso : {A B : Obj} → Isomorphic c A B → Isomorphic SET (Aut A) (Isom A B)
  proj₁ (aut-iso f) aut = f ≅∘ aut
  inverse (proj₂ (aut-iso f)) isom = iso-sym c f ≅∘ isom
  inverse∘f (proj₂ (aut-iso f)) aut = begin
    iso-sym c f ≅∘ (f ≅∘ aut)  ≡⟨ ? ⟩
    (iso-sym c f ≅∘ f) ≅∘ aut  ≡⟨ ? ⟩
    iso-refl c ≅∘ aut          ≡⟨ ? ⟩
    aut                        ∎
    where open ≡-Reasoning
  f∘inverse (proj₂ (aut-iso f)) isom = begin
    f ≅∘ (iso-sym c f ≅∘ isom)  ≡⟨ ? ⟩
    (f ≅∘ iso-sym c f) ≅∘ isom  ≡⟨ ? ⟩
    iso-refl c ≅∘ isom          ≡⟨ ? ⟩
    isom                        ∎
    where open ≡-Reasoning



open Definition c public

