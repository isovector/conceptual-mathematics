open import Cat.Base

module Constr.Iso where

module Definition {ℓ₁ ℓ₂ : Level} (c : Category ℓ₁ ℓ₂) where
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
  open IsIsomorphism

  open import Data.Product

  -- DEFINITION, Page 40
  Isomorphic : Rel Obj ℓ₂
  Isomorphic A B = Σ (A ⇒ B) IsIsomorphism


  -- EXERCISE 1r
  isomorphic-refl : Reflexive Isomorphic
  proj₁ isomorphic-refl = id
  proj₂ isomorphic-refl = iso id (identityˡ id) (identityˡ id)


  -- EXERCISE 1s
  isomorphic-sym : Symmetric Isomorphic
  isomorphic-sym (f , iso inverse inverse∘f f∘inverse)
    = inverse , iso f f∘inverse inverse∘f


  -- EXERCISE 1t
  isomorphic-trans : Transitive Isomorphic
  proj₁ (isomorphic-trans (f , iso fi fiˡ fiʳ) (g , iso gi giˡ giʳ)) = g ∘ f
  inverse (proj₂ (isomorphic-trans (f , iso fi fiˡ fiʳ) (g , iso gi giˡ giʳ))) = fi ∘ gi
  inverse∘f (proj₂ (isomorphic-trans (f , iso fi fiˡ fiʳ) (g , iso gi giˡ giʳ))) = begin
    (fi ∘ gi) ∘ (g ∘ f)  ≈⟨ assoc fi gi (g ∘ f) ⟩
    fi ∘ (gi ∘ (g ∘ f))  ≈⟨ cong refl (sym (assoc gi g f)) ⟩
    fi ∘ ((gi ∘ g) ∘ f)  ≈⟨ cong refl (cong giˡ refl) ⟩
    fi ∘ (id ∘ f)        ≈⟨ cong refl (identityˡ f) ⟩
    fi ∘ f               ≈⟨ fiˡ ⟩
    id                   ∎
    where open Reasoning
  f∘inverse (proj₂ (isomorphic-trans (f , iso fi fiˡ fiʳ) (g , iso gi giˡ giʳ))) = begin
    (g ∘ f) ∘ (fi ∘ gi)  ≈⟨ assoc g f (fi ∘ gi) ⟩
    g ∘ (f ∘ (fi ∘ gi))  ≈⟨ cong refl (sym (assoc f fi gi)) ⟩
    g ∘ ((f ∘ fi) ∘ gi)  ≈⟨ cong refl (cong fiʳ refl) ⟩
    g ∘ (id ∘ gi)        ≈⟨ cong refl (identityˡ gi) ⟩
    g ∘ gi               ≈⟨ giʳ ⟩
    id                   ∎
    where open Reasoning

  private variable
    A B : Obj
    f g h k : A ⇒ B


  -- EXERCISE 2
  iso-unique : (g k : IsIsomorphism f) → inverse g ≈ inverse k
  iso-unique {f = f} g k = begin
    inverse g                    ≈⟨ sym (identityˡ _) ⟩
    id ∘ inverse g               ≈⟨ cong (sym (inverse∘f k)) refl ⟩
    (inverse k ∘ f) ∘ inverse g  ≈⟨ assoc _ _ _ ⟩
    inverse k ∘ (f ∘ inverse g)  ≈⟨ cong refl (f∘inverse g) ⟩
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
    id ∘ h                   ≈⟨ cong (sym (inverse∘f f-iso)) refl ⟩
    (inverse f-iso ∘ f) ∘ h  ≈⟨ assoc _ _ _ ⟩
    inverse f-iso ∘ (f ∘ h)  ≈⟨ cong refl fh≈fk ⟩
    inverse f-iso ∘ (f ∘ k)  ≈⟨ sym (assoc _ _ _) ⟩
    (inverse f-iso ∘ f) ∘ k  ≈⟨ cong (inverse∘f f-iso) refl ⟩
    id ∘ k                   ≈⟨ identityˡ _ ⟩
    k                        ∎
    where open Reasoning


  -- EXERCISE 3b
  iso-injectiveʳ : IsIsomorphism f → h ∘ f ≈ k ∘ f → h ≈ k
  iso-injectiveʳ {f = f} {h = h} {k = k} f-iso hf≈kf = begin
    h                        ≈⟨ sym (identityʳ _) ⟩
    h ∘ id                   ≈⟨ cong refl (sym (f∘inverse f-iso)) ⟩
    h ∘ (f ∘ inverse f-iso)  ≈⟨ sym (assoc _ _ _) ⟩
    (h ∘ f) ∘ inverse f-iso  ≈⟨ cong hf≈kf refl ⟩
    (k ∘ f) ∘ inverse f-iso  ≈⟨ assoc _ _ _ ⟩
    k ∘ (f ∘ inverse f-iso)  ≈⟨ cong refl (f∘inverse f-iso) ⟩
    k ∘ id                   ≈⟨ identityʳ _ ⟩
    k                        ∎
    where open Reasoning


open import Relation.Nullary
open import Data.Bool
open import Data.Bool.Properties
open import Cat.SET
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
  : ¬ ((c : Category (suc zero) zero)
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

open Definition public

