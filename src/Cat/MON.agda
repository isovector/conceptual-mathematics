open import Cat.Base

module Cat.MON where

open Category hiding (_≈_; id)
open import Function using (id)
open import Algebra using (Monoid; IsMonoid)
open import Relation.Binary using (IsEquivalence; Rel)
import Relation.Binary.Reasoning.Setoid as Setoid-Reasoning

open Monoid using (Carrier; isEquivalence)

module _ (m₁ m₂ : Monoid lzero lzero) where
  open Monoid ⦃ ... ⦄

  private instance
    _ = m₁
    _ = m₂

  record MonHom : Set where
    constructor hom
    field
      map : m₁ .Carrier → m₂ .Carrier
      map-ε : map ε ≈ ε
      map-∙ : ∀ x y → map (x ∙ y) ≈ map x ∙ map y
      cong : ∀ {x y}  → x ≈ y → map x ≈ map y
  open MonHom

  ≈-MonHom : Rel MonHom _
  ≈-MonHom x y = ∀ a → map x a ≈ map y a

  open IsEquivalence

  ≈-equiv : IsEquivalence ≈-MonHom
  refl  ≈-equiv     a = refl  (isEquivalence m₂)
  sym   ≈-equiv f   a = sym   (isEquivalence m₂) (f a)
  trans ≈-equiv f g a = trans (isEquivalence m₂) (f a) (g a)

open IsEquivalence
open MonHom


MON : Category _ _
Obj MON = Monoid lzero lzero
_⇒_ MON = MonHom
Category._≈_ MON {m₁} {m₂} = ≈-MonHom m₁ m₂
equiv        MON {m₁} {m₂} = ≈-equiv m₁ m₂
map   (Category.id MON) = id
map-ε (Category.id MON {m})     = refl (isEquivalence m)
map-∙ (Category.id MON {m}) x y = refl (isEquivalence m)
cong  (Category.id MON) = id
map   (_∘_ MON g f) = map g Function.∘ map f
map-ε (_∘_ MON {m₃} {m₂} {m₁} g f) = begin
  map g (map f (Monoid.ε m₁))  ≈⟨ cong g (map-ε f) ⟩
  map g (Monoid.ε m₂)          ≈⟨ map-ε g ⟩
  Monoid.ε m₃                  ∎
  where open Setoid-Reasoning (Monoid.setoid m₃)
map-∙ (_∘_ MON {m₃} {m₂} {m₁} g f) x y = begin
  map (_∘_ MON g f) (Monoid._∙_ m₁ x y)  ≈⟨ cong g (map-∙ f x y) ⟩
  _                                      ≈⟨ map-∙ g _ _ ⟩
  _                                      ∎
  where open Setoid-Reasoning (Monoid.setoid m₃)
cong  (Category._∘_ MON {m₃} {m₂} {m₁} g f) = cong g Function.∘ cong f
identityˡ MON {Y = m} f a = refl (isEquivalence m)
identityʳ MON {Y = m} f a = refl (isEquivalence m)
assoc     MON {D = m} h g f a = refl (isEquivalence m)
cong      MON {Z = m } {f} {f′} {g} {g′} g=g' f=f' a = begin
  map g (map f a)    ≈⟨ g=g' _ ⟩
  map g′ (map f a)   ≈⟨ cong g′ (f=f' _) ⟩
  map g′ (map f′ a)  ∎
  where open Setoid-Reasoning (Monoid.setoid m)


module Exercises where
  open import Relation.Binary.PropositionalEquality

  data EvenOdd : Set where
    odd even : EvenOdd

  postulate
    idc : {A : Set} → A

  EvenOdd-+ : Monoid _ _
  Carrier EvenOdd-+ = EvenOdd
  Monoid._≈_ EvenOdd-+ = _≡_
  Monoid._∙_ EvenOdd-+ even y = y
  Monoid._∙_ EvenOdd-+ odd even = odd
  Monoid._∙_ EvenOdd-+ odd odd = even
  Monoid.ε EvenOdd-+ = even
  Monoid.isMonoid EvenOdd-+ = idc

  data PosNeg : Set where
    positive negative : PosNeg

  PosNeg-+ : Monoid _ _
  Carrier PosNeg-+ = PosNeg
  Monoid._≈_ PosNeg-+ = _≡_
  Monoid._∙_ PosNeg-+ positive y = y
  Monoid._∙_ PosNeg-+ negative positive = negative
  Monoid._∙_ PosNeg-+ negative negative = positive
  Monoid.ε PosNeg-+ = positive
  Monoid.isMonoid PosNeg-+ = idc

  -- EXERCISE 2, page 79
  evenodd→posneg-homm : MonHom EvenOdd-+ PosNeg-+
  map evenodd→posneg-homm odd = negative
  map evenodd→posneg-homm even = positive
  map-ε evenodd→posneg-homm = _≡_.refl
  map-∙ evenodd→posneg-homm odd odd = _≡_.refl
  map-∙ evenodd→posneg-homm odd even = _≡_.refl
  map-∙ evenodd→posneg-homm even y = _≡_.refl
  MonHom.cong evenodd→posneg-homm _≡_.refl = _≡_.refl


  -- Exercise 3, page 79
  -- a) p(a + b) = p(a) + p(b)
  --    a + b + a /= a + 1 + b + 1
  --    NOT A HOM
  --
  -- b) sq(a * b) = sq(a) * sq(b)
  --    a^2*b^2 = a^2 * b^2
  --    YES A HOM, but not an ISO
  --
  -- c) NOT EVEN A FUNCTION
  --
  -- d) m(a + b) = m(a) + m(b)
  --    -(a + b) = -a + -b
  --    YES A HOM. An ISO? Definitely
  --
  -- e) m(a * b) = -a * -b
  --    -(a * b) /= a * b
  --    NOT A HOM
  --
  -- f) NAH BABY


