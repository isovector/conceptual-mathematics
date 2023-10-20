open import Cat.Base

module Constr.Section {ℓ₁ ℓ₂ : Level} (c : Category ℓ₁ ℓ₂) where

open Category c
open import Constr.DivisionChoice c
open import Data.Product

open _is-determined-by_
open _is-chosen-by_

private variable
  A B C T : Obj
  f : A ⇒ B
  g : B ⇒ C


-- DEFINITION, page 49
RetractionFor : A ⇒ B → Set ℓ₂
RetractionFor {A = A} f = id {A} is-determined-by f


-- DEFINITION, page 49
SectionFor : A ⇒ B → Set ℓ₂
SectionFor {B = B} f = id {B} is-chosen-by f


-- PROPOSITION 1, page 51
prop1 : SectionFor f → (y : T ⇒ B) → Σ[ x ∈ T ⇒ A ] (f ∘ x ≈ y)
prop1 {f = f} record { factoring = s ; chooses = pr } y = s ∘ y ,
  ( begin
    f ∘ (s ∘ y)  ≈⟨ sym (assoc _ _ _) ⟩
    (f ∘ s) ∘ y  ≈⟨ cong pr refl ⟩
    id ∘ y       ≈⟨ identityˡ y ⟩
    y            ∎
  )
  where open Reasoning


-- PROPOSITION 1*, page 52
prop1* : RetractionFor f → (g : A ⇒ T) → Σ[ t ∈ B ⇒ T ] (t ∘ f ≈ g)
prop1* {f = f} record { factoring = r ; determines = pr } g = g ∘ r ,
  ( begin
    (g ∘ r) ∘ f  ≈⟨ assoc _ _ _ ⟩
    g ∘ (r ∘ f)  ≈⟨ cong refl pr ⟩
    g ∘ id       ≈⟨ identityʳ g ⟩
    g            ∎
  )
  where open Reasoning


-- DEFINITION, Page 52
_is-injective-for-maps-from_ : A ⇒ B → Obj → Set ℓ₂
_is-injective-for-maps-from_ {A = A} f T = (t₁ t₂ : T ⇒ A) → f ∘ t₁ ≈ f ∘ t₂ → t₁ ≈ t₂


-- DEFINITION, Page 52
IsMonomorphism : A ⇒ B → Set (ℓ₁ ⊔ ℓ₂)
IsMonomorphism f = {T : Obj} → f is-injective-for-maps-from T


-- DEFINITION, Page 52
_is-surjective-for-maps-to_ : A ⇒ B → Obj → Set ℓ₂
_is-surjective-for-maps-to_ {B = B} f T = (t₁ t₂ : B ⇒ T) → t₁ ∘ f ≈ t₂ ∘ f → t₁ ≈ t₂


-- DEFINITION, Page 52
IsEpimorphism : A ⇒ B → Set (ℓ₁ ⊔ ℓ₂)
IsEpimorphism f = {T : Obj} → f is-surjective-for-maps-to T


-- PROPOSITION 2, page 52
prop2 : RetractionFor f → IsMonomorphism f
prop2 {f = f} record { factoring = r ; determines = pr } x₁ x₂ fx₁≈fx₂ =
  begin
  x₁            ≈⟨ sym (identityˡ _) ⟩
  id ∘ x₁       ≈⟨ sym (cong pr refl) ⟩
  (r ∘ f) ∘ x₁  ≈⟨ assoc _ _ _ ⟩
  r ∘ (f ∘ x₁)  ≈⟨ cong refl fx₁≈fx₂ ⟩
  r ∘ (f ∘ x₂)  ≈⟨ sym (assoc _ _ _) ⟩
  (r ∘ f) ∘ x₂  ≈⟨ cong pr refl ⟩
  id ∘ x₂       ≈⟨ identityˡ _ ⟩
  x₂            ∎
  where open Reasoning


-- EXERCISE 7, page 52
prop2* : SectionFor f → IsEpimorphism f
prop2* {f = f} record { factoring = s ; chooses = pr } t₁ t₂ eq =
  begin
  t₁            ≈⟨ sym (identityʳ _) ⟩
  t₁ ∘ id       ≈⟨ sym (cong refl pr) ⟩
  t₁ ∘ (f ∘ s)  ≈⟨ sym (assoc _ _ _) ⟩
  (t₁ ∘ f) ∘ s  ≈⟨ cong eq refl ⟩
  (t₂ ∘ f) ∘ s  ≈⟨ assoc _ _ _ ⟩
  t₂ ∘ (f ∘ s)  ≈⟨ cong refl pr ⟩
  t₂ ∘ id       ≈⟨ identityʳ _ ⟩
  t₂            ∎
  where open Reasoning


-- PROPOSITION 3, page 53
prop3 : RetractionFor f → RetractionFor g → RetractionFor (g ∘ f)
factoring (prop3 (det rf pf) (det rg pg)) = rf ∘ rg
determines (prop3 {f = f} {g = g} (det rf pf) (det rg pg)) =
  begin
  (rf ∘ rg) ∘ (g ∘ f)  ≈⟨ assoc _ _ _ ⟩
  rf ∘ (rg ∘ (g ∘ f))  ≈⟨ cong refl (sym (assoc _ _ _)) ⟩
  rf ∘ ((rg ∘ g) ∘ f)  ≈⟨ cong refl (cong pg refl) ⟩
  rf ∘ (id ∘ f)        ≈⟨ cong refl (identityˡ f) ⟩
  rf ∘ f               ≈⟨ pf ⟩
  id                   ∎
  where open Reasoning

sec→ret : (s : SectionFor f) → RetractionFor (s .factoring)
sec→ret {f = f} (cho s pr) = det f pr

ret→sec : (r : RetractionFor f) → SectionFor (r .factoring)
ret→sec {f = f} (det r pr) = cho f pr


-- EXERCISE, page 54
ex8 : SectionFor f → SectionFor g → SectionFor (f ∘ g)
ex8 sf sg = ret→sec (prop3 (sec→ret sf) (sec→ret sg))


-- DEFINITION, page 54
IsIdempotent : A ⇒ A → Set ℓ₂
IsIdempotent e = e ∘ e ≈ e


-- EXERCISE 9, page 54
ex9 : (rf : RetractionFor f) → IsIdempotent (f ∘ rf .factoring)
ex9 {f = f} (det g pr) = begin
  (f ∘ g) ∘ (f ∘ g)  ≈⟨ assoc _ _ _ ⟩
  f ∘ (g ∘ (f ∘ g))  ≈⟨ cong refl (sym (assoc _ _ _)) ⟩
  f ∘ ((g ∘ f) ∘ g)  ≈⟨ cong refl (cong pr refl) ⟩
  f ∘ (id ∘ g)       ≈⟨ cong refl (identityˡ _) ⟩
  f ∘ g              ∎
  where open Reasoning


-- THEOREM: UNIQUENESS OF INVERSES, page 54
uii : (r : RetractionFor f) → (s : SectionFor f) → s .factoring ≈ r .factoring
uii {f = f} (det r pr) (cho s ps) = begin
  s            ≈⟨ sym (identityˡ _) ⟩
  id ∘ s       ≈⟨ cong (sym pr) refl ⟩
  (r ∘ f) ∘ s  ≈⟨ assoc _ _ _ ⟩
  r ∘ (f ∘ s)  ≈⟨ cong refl ps ⟩
  r ∘ id       ≈⟨ identityʳ _ ⟩
  r            ∎
  where open Reasoning

