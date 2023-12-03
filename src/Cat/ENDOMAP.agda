open import Cat.Base

module Cat.ENDOMAP {ℓ₁ ℓ₂ : Level} (c : Category ℓ₁ ℓ₂) where


open Category
open import Data.Product
open import Relation.Binary hiding (_⇒_)
open IsEquivalence

open Category c renaming (_∘_ to _∘ᶜ_; _≈_ to _≈ᶜ_)

Endo : Set _
Endo = Σ (Obj c) (λ x → _⇒_ c x x)

record EndoArr (A B : Endo) : Set ℓ₂ where
  field
    mapAut : _⇒_ c (proj₁ A) (proj₁ B)
    preserves : mapAut ∘ᶜ proj₂ A ≈ᶜ proj₂ B ∘ᶜ mapAut

open EndoArr

PERM : Category _ _
Obj PERM = Endo
_⇒_ PERM = EndoArr
_≈_ PERM f g = mapAut f ≈ᶜ mapAut g
refl  (equiv PERM) = refl (equiv c)
sym   (equiv PERM) = sym (equiv c)
trans (equiv PERM) = trans (equiv c)
mapAut (id PERM) = id c
preserves (id PERM {x = x}) = begin
  id c ∘ᶜ (proj₂ x)  ≈⟨ identityˡ c (proj₂ x) ⟩
  proj₂ x            ≈˘⟨ identityʳ c (proj₂ x) ⟩
  proj₂ x ∘ᶜ id c    ∎
  where open Category.Reasoning c
mapAut (_∘_ PERM g f) = mapAut g ∘ᶜ mapAut f
preserves (_∘_ PERM {i} {j} {k} g f) = begin
  (mapAut g ∘ᶜ mapAut f) ∘ᶜ proj₂ k  ≈⟨ assoc c _ _ _ ⟩
  mapAut g ∘ᶜ (mapAut f ∘ᶜ proj₂ k)  ≈⟨ Category.congʳ c (preserves f) ⟩
  mapAut g ∘ᶜ (proj₂ j ∘ᶜ mapAut f)  ≈˘⟨ assoc c _ _ _ ⟩
  (mapAut g ∘ᶜ proj₂ j) ∘ᶜ mapAut f  ≈⟨ Category.congˡ c (preserves g) ⟩
  (proj₂ i ∘ᶜ mapAut g) ∘ᶜ mapAut f  ≈⟨ assoc c _ _ _ ⟩
  proj₂ i ∘ᶜ mapAut g ∘ᶜ mapAut f    ∎
  where open Category.Reasoning c
identityˡ PERM f = identityˡ c (mapAut f)
identityʳ PERM f = identityʳ c (mapAut f)
assoc PERM h g f = assoc c (mapAut h) (mapAut g) (mapAut f)
cong PERM x y = cong c x y

open import Data.Maybe

Accessible : Rel Endo _
Accessible x y = Maybe (EndoArr x y)

-- only makes sense in ENDMAP SET
-- Convergent : Endo → Set _
-- Convergent x = Maybe (EndoArr x y)

-- EXERCISE 4: p140
-- α(x) = -x is an involution, since α∘α=id
--
-- It is NOT idempotent, since we don't have the fact that
--  α∘α = α

-- EXERCISE 5: p140
-- α(x) = |x|
--
-- Not an involution, since α∘α≠id
-- but idempotent, because α∘α=α

-- EXERCISE 6: p140
-- β(x) = x - 3

-- EXERCISE 7: p140
-- α(x) = 5x
--  Yes an endomap
--  Not an automorphism, since it is not closed under inverse
--  Not an involution
--  Not an idempotent

-- EXERCISE 8: p140
-- Idempotent: α ∘ α = α
-- therefore:
--    α³ = α∘α∘α
--       = α∘α
--       = α
--
-- Involution: α ∘ α = id
--
--    α³ = α∘α∘α
--       = id∘α
--       = α


-- EXERCISE 9: p141
-- α(0) = 1
-- α(1) = 2
-- α(2) = 1
--
-- α∘α∘α(0) = α∘α(1)=α(2) = 1 = α(0)
-- α∘α∘α(1) = α∘α(2)=α(1) = 2 = α(1)
-- α∘α∘α(2) = α∘α(1)=α(2) = 1 = α(2)
--
-- ∴ α∘α∘α = α
--
-- Not an involution:
--  α∘α 0 = α 1 = 2 ≠ id 0
--
-- Not an idempotent
--  α∘α 0 = α 1 = 2 ≠ α 0

