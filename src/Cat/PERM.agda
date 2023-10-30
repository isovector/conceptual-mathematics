open import Cat.Base

module Cat.PERM {ℓ₁ ℓ₂ : Level} (c : Category ℓ₁ ℓ₂) where


open Category
open import Constr.Iso c
open import Data.Product
open import Relation.Binary hiding (_⇒_)
open IsEquivalence
open import Constr.Automorphism c

open Category c renaming (_∘_ to _∘ᶜ_; _≈_ to _≈ᶜ_)

AutObj : Set _
AutObj = Σ (Obj c) Aut

record AutArr (A B : AutObj) : Set ℓ₂ where
  field
    mapAut : _⇒_ c (proj₁ A) (proj₁ B)
    preserves : mapAut ∘ᶜ proj₁ (proj₂ A) ≈ᶜ proj₁ (proj₂ B) ∘ᶜ mapAut

open AutArr

PERM : Category _ _
Obj PERM = AutObj
_⇒_ PERM = AutArr
_≈_ PERM f g = mapAut f ≈ᶜ mapAut g
refl (equiv PERM) = refl (equiv c)
sym (equiv PERM) = sym (equiv c)
trans (equiv PERM) = trans (equiv c)
mapAut (id PERM) = id c
preserves (id PERM {x = x}) = begin
  id c ∘ᶜ proj₁ (proj₂ x)  ≈⟨ identityˡ c (proj₁ (proj₂ x)) ⟩
  proj₁ (proj₂ x)          ≈˘⟨ identityʳ c (proj₁ (proj₂ x)) ⟩
  proj₁ (proj₂ x) ∘ᶜ id c  ∎
  where open Category.Reasoning c
mapAut (_∘_ PERM g f) = mapAut g ∘ᶜ mapAut f
preserves (_∘_ PERM {i} {j} {k} g f) = begin
  (mapAut g ∘ᶜ mapAut f) ∘ᶜ proj₁ (proj₂ k)  ≈⟨ assoc c _ _ _ ⟩
  mapAut g ∘ᶜ (mapAut f ∘ᶜ proj₁ (proj₂ k))  ≈⟨ Category.congʳ c (preserves f) ⟩
  mapAut g ∘ᶜ (proj₁ (proj₂ j) ∘ᶜ mapAut f)  ≈˘⟨ assoc c _ _ _ ⟩
  (mapAut g ∘ᶜ proj₁ (proj₂ j)) ∘ᶜ mapAut f  ≈⟨ Category.congˡ c (preserves g) ⟩
  (proj₁ (proj₂ i) ∘ᶜ mapAut g) ∘ᶜ mapAut f  ≈⟨ assoc c _ _ _ ⟩
  proj₁ (proj₂ i) ∘ᶜ mapAut g ∘ᶜ mapAut f    ∎
  where open Category.Reasoning c
identityˡ PERM f = identityˡ c (mapAut f)
identityʳ PERM f = identityʳ c (mapAut f)
assoc PERM h g f = assoc c (mapAut h) (mapAut g) (mapAut f)
cong PERM x y = cong c x y

