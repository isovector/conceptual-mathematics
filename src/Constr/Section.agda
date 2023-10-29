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


-- DEFINITION, Page 52
_is-injective-for-maps-from_ : A ⇒ B → Obj → Set ℓ₂
_is-injective-for-maps-from_ {A = A} f T
  = (t₁ t₂ : T ⇒ A) → f ∘ t₁ ≈ f ∘ t₂ → t₁ ≈ t₂


-- DEFINITION, Page 52
IsMonomorphism : A ⇒ B → Set (ℓ₁ ⊔ ℓ₂)
IsMonomorphism {A = A} f = {T : Obj} → f is-injective-for-maps-from T


-- DEFINITION, Page 52
_is-surjective-for-maps-from_ : A ⇒ B → Obj → Set ℓ₂
_is-surjective-for-maps-from_ {A = A} {B = B} f T
  = (y : T ⇒ B) → Σ[ x ∈ T ⇒ A ] (f ∘ x ≈ y)


-- DEFINITION, Page 52
IsEpimorphism : A ⇒ B → Set (ℓ₁ ⊔ ℓ₂)
IsEpimorphism {B = B} f
  = ∀ {T : Obj} → (t₁ t₂ : B ⇒ T) → t₁ ∘ f ≈ t₂ ∘ f → t₁ ≈ t₂


-- PROPOSITION 1, page 51
-- This is the property of surjectivity of `f`; for any particular result `y` we
-- want, we can find some other map `x` such that precomposing it gives us us
-- the thing we want.
--
-- Why is this surjectivity? Because if the function weren't surjective, `y`
-- could map somewhere in `B` that we can't get to from `f`.
prop1 : SectionFor f → (y : T ⇒ B) → Σ[ x ∈ T ⇒ A ] (f ∘ x ≈ y)
prop1 {f = f} record { factoring = s ; chooses = pr } y = s ∘ y ,
  ( begin
    f ∘ (s ∘ y)  ≈⟨ sym reassoc ⟩
    (f ∘ s) ∘ y  ≈⟨ id-elimˡ pr ⟩
    y            ∎
  )
  where open Reasoning


-- PROPOSITION 1*, page 52
prop1* : RetractionFor f → (g : A ⇒ T) → Σ[ t ∈ B ⇒ T ] (t ∘ f ≈ g)
prop1* {f = f} record { factoring = r ; determines = pr } g = g ∘ r ,
  ( begin
    (g ∘ r) ∘ f  ≈⟨ reassoc ⟩
    g ∘ (r ∘ f)  ≈⟨ id-elimʳ pr ⟩
    g            ∎
  )
  where open Reasoning


-- PROPOSITION 2, page 52
prop2 : RetractionFor f → IsMonomorphism f
prop2 {f = f} record { factoring = r ; determines = pr } x₁ x₂ fx₁≈fx₂ =
  begin
  x₁            ≈⟨ sym (id-elimˡ pr) ⟩
  (r ∘ f) ∘ x₁  ≈⟨ reassoc ⟩
  r ∘ (f ∘ x₁)  ≈⟨ congʳ fx₁≈fx₂ ⟩
  r ∘ (f ∘ x₂)  ≈⟨ sym reassoc ⟩
  (r ∘ f) ∘ x₂  ≈⟨ id-elimˡ pr ⟩
  x₂            ∎
  where open Reasoning


-- EXERCISE 7, page 52
prop2* : SectionFor f → IsEpimorphism f
prop2* {f = f} record { factoring = s ; chooses = pr } t₁ t₂ eq =
  begin
  t₁            ≈⟨ sym (id-elimʳ pr) ⟩
  t₁ ∘ (f ∘ s)  ≈⟨ sym reassoc ⟩
  (t₁ ∘ f) ∘ s  ≈⟨ congˡ eq ⟩
  (t₂ ∘ f) ∘ s  ≈⟨ reassoc ⟩
  t₂ ∘ (f ∘ s)  ≈⟨ id-elimʳ pr ⟩
  t₂            ∎
  where open Reasoning


-- PROPOSITION 3, page 53
prop3 : RetractionFor f → RetractionFor g → RetractionFor (g ∘ f)
factoring (prop3 (det rf pf) (det rg pg)) = rf ∘ rg
determines (prop3 {f = f} {g = g} (det rf pf) (det rg pg)) =
  begin
  (rf ∘ rg) ∘ (g ∘ f)  ≈⟨ reassoc-in ⟩
  rf ∘ ((rg ∘ g) ∘ f)  ≈⟨ congʳ (id-elimˡ pg) ⟩
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
  (f ∘ g) ∘ (f ∘ g)  ≈⟨ reassoc-in ⟩
  f ∘ ((g ∘ f) ∘ g)  ≈⟨ congʳ (id-elimˡ pr) ⟩
  f ∘ g              ∎
  where open Reasoning


-- THEOREM: UNIQUENESS OF INVERSES, page 54
uii : (r : RetractionFor f) → (s : SectionFor f) → s .factoring ≈ r .factoring
uii {f = f} (det r pr) (cho s ps) = begin
  s            ≈⟨ sym (id-elimˡ pr) ⟩
  (r ∘ f) ∘ s  ≈⟨ reassoc ⟩
  r ∘ (f ∘ s)  ≈⟨ id-elimʳ ps ⟩
  r            ∎
  where open Reasoning

-- QUESTIONS
--
-- 1) The definitions given, `_is-surjective-for-maps-from_` is NOT dual to
--    `_is-injective-for-maps-from_`. Because `IsMonomorphism` is forall T,
--    is-injective..., but the converse is not true for `IsEpimorphism`.
--
--    Wrong definition? Only true in sets? What's going on here?

-- NOTES
--
-- r ∘ s = 1ₐ; A must be smaller than B
-- the section goes to the bigger domain
-- the retraction comes back
--    > section is a CHOICE OF REPRESENTATIVE of the smaller set
--    > while the retraction maps back to the smaller set
--
--    * retraction : person -> riding
--    * section    : riding -> person

