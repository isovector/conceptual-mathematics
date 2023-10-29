open import Cat.Base

module Constr.Iso {ℓ₁ ℓ₂ : Level} (c : Category ℓ₁ ℓ₂) where

private module Definition {ℓ₁ ℓ₂ : Level} (c : Category ℓ₁ ℓ₂) where
  open import Relation.Binary
    using (Rel; Reflexive; Symmetric; Transitive)
  open Category c

  -- DEFINITION, Page 40
  record IsIsomorphism {A B : Obj} (f : A ⇒ B) : Set ℓ₂ where
    constructor iso
    field
      inverse : B ⇒ A
      inverse∘f : inverse ∘ f ≈ id
      f∘inverse : f ∘ inverse ≈ id
  open IsIsomorphism public

  open import Data.Product

  -- DEFINITION, Page 40
  Isomorphic : Rel Obj ℓ₂
  Isomorphic A B = Σ (A ⇒ B) IsIsomorphism


  -- EXERCISE 1r
  iso-refl : Reflexive Isomorphic
  proj₁ iso-refl = id
  proj₂ iso-refl = iso id (identityˡ id) (identityˡ id)


  -- EXERCISE 1s
  iso-sym : Symmetric Isomorphic
  iso-sym (f , iso inverse inverse∘f f∘inverse)
    = inverse , iso f f∘inverse inverse∘f


  -- EXERCISE 1t
  iso-trans′ : Transitive Isomorphic
  proj₁ (iso-trans′ (f , iso fi fiˡ fiʳ) (g , iso gi giˡ giʳ)) = g ∘ f
  inverse (proj₂ (iso-trans′ (f , iso fi fiˡ fiʳ) (g , iso gi giˡ giʳ))) = fi ∘ gi
  inverse∘f (proj₂ (iso-trans′ (f , iso fi fiˡ fiʳ) (g , iso gi giˡ giʳ))) = begin
    (fi ∘ gi) ∘ (g ∘ f)  ≈⟨ reassoc-in ⟩
    fi ∘ ((gi ∘ g) ∘ f)  ≈⟨ congʳ (congˡ giˡ) ⟩
    fi ∘ (id ∘ f)        ≈⟨ congʳ (identityˡ f) ⟩
    fi ∘ f               ≈⟨ fiˡ ⟩
    id                   ∎
    where open Reasoning
  f∘inverse (proj₂ (iso-trans′ (f , iso fi fiˡ fiʳ) (g , iso gi giˡ giʳ))) = begin
    (g ∘ f) ∘ (fi ∘ gi)  ≈⟨ reassoc-in ⟩
    g ∘ ((f ∘ fi) ∘ gi)  ≈⟨ congʳ (congˡ fiʳ) ⟩
    g ∘ (id ∘ gi)        ≈⟨ congʳ (identityˡ gi) ⟩
    g ∘ gi               ≈⟨ giʳ ⟩
    id                   ∎
    where open Reasoning

  open import Function using (flip)

  iso-trans : {A B C : Obj} → (y : Σ (B ⇒ C) IsIsomorphism) (x : Σ (A ⇒ B) IsIsomorphism) → Σ (A ⇒ C) IsIsomorphism
  iso-trans = flip iso-trans′

  private variable
    A B : Obj
    f g h k : A ⇒ B


  -- EXERCISE 2
  iso-unique : (g k : IsIsomorphism f) → inverse g ≈ inverse k
  iso-unique {f = f} g k = begin
    inverse g                    ≈⟨ sym (identityˡ _) ⟩
    id ∘ inverse g               ≈⟨ congˡ (sym (inverse∘f k)) ⟩
    (inverse k ∘ f) ∘ inverse g  ≈⟨ reassoc ⟩
    inverse k ∘ (f ∘ inverse g)  ≈⟨ congʳ (f∘inverse g) ⟩
    inverse k ∘ id               ≈⟨ identityʳ _ ⟩
    inverse k                    ∎
    where open Reasoning


  -- NOTATION, page 43
  _⁻¹ : (f : A ⇒ B) → Set ℓ₂
  _⁻¹ = IsIsomorphism


  -- EXERCISE 3a
  iso-injectiveˡ : IsIsomorphism f → f ∘ h ≈ f ∘ k → h ≈ k
  iso-injectiveˡ {f = f} {h = h} {k = k} f-iso fh≈fk = begin
    h                        ≈⟨ sym (identityˡ _) ⟩
    id ∘ h                   ≈⟨ congˡ (sym (inverse∘f f-iso)) ⟩
    (inverse f-iso ∘ f) ∘ h  ≈⟨ reassoc ⟩
    inverse f-iso ∘ (f ∘ h)  ≈⟨ cong refl fh≈fk ⟩
    inverse f-iso ∘ (f ∘ k)  ≈⟨ sym reassoc ⟩
    (inverse f-iso ∘ f) ∘ k  ≈⟨ congˡ (inverse∘f f-iso) ⟩
    id ∘ k                   ≈⟨ identityˡ _ ⟩
    k                        ∎
    where open Reasoning


  -- EXERCISE 3b
  iso-injectiveʳ : IsIsomorphism f → h ∘ f ≈ k ∘ f → h ≈ k
  iso-injectiveʳ {f = f} {h = h} {k = k} f-iso hf≈kf = begin
    h                        ≈⟨ sym (identityʳ _) ⟩
    h ∘ id                   ≈⟨ congʳ (sym (f∘inverse f-iso)) ⟩
    h ∘ (f ∘ inverse f-iso)  ≈⟨ sym reassoc ⟩
    (h ∘ f) ∘ inverse f-iso  ≈⟨ congˡ hf≈kf ⟩
    (k ∘ f) ∘ inverse f-iso  ≈⟨ reassoc ⟩
    k ∘ (f ∘ inverse f-iso)  ≈⟨ congʳ (f∘inverse f-iso) ⟩
    k ∘ id                   ≈⟨ identityʳ _ ⟩
    k                        ∎
    where open Reasoning


open import Relation.Nullary
open import Data.Bool
open import Data.Bool.Properties
open import Cat.SET lzero
open import Relation.Binary.PropositionalEquality as ≡
  using (_≢_; module ≡-Reasoning)


-- Needed for exercise 3c
module Specialize where
  open Definition SET
  open import Function using (const; id)

  f h k : Bool → Bool
  f = not
  h = const false
  k = const true

  f-inv : IsIsomorphism f
  f-inv = iso not not-involutive not-involutive

  no-way : false ≢ true
  no-way ()


-- EXERCISE 3c
¬h∘f≈f∘k⊃h≈k
  : ¬ ((c : Category (lsuc lzero) lzero)
       → let open Category c in
       ∀ {X : Obj} (f h k : X ⇒ X)
       → h ∘ f ≈ f ∘ k
       → h ≈ k
       )
¬h∘f≈f∘k⊃h≈k contra = S.no-way ( begin
  false            ≡⟨⟩
  S.h (S.f false)  ≡⟨ contra SET S.f S.h S.k (λ x → ≡.refl) (S.f false) ⟩
  S.k (S.f false)  ≡⟨⟩
  true             ∎)
  where
    module S = Specialize
    open ≡-Reasoning


-- Page 44 exercise 4
--
-- Which are invertable?
-- 1. YES
--    y = 3x + 7
--    x = (y - 7)/3
--
-- 2. YES
--    x = sqrt(y)
--
-- 3. NO; not injective!
--    -1^2 = 1 = 1^2
--    but -1 ≢ 1
--
-- 4. NO; not injective!
--
-- 5. LGTM
--    y = 1/x + 1
--    y - 1 = 1/x
--    x = 1/(y - 1)

open Definition c public

