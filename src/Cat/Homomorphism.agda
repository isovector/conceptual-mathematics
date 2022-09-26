{-# OPTIONS --type-in-type #-}

open import Cat.Raw

module Cat.Homomorphism ⦃ C D : Category ⦄ (LD : LawfulCategory D) where

open Category ⦃ ... ⦄ hiding (Obj)
open Category using (Obj)

private instance
  import Cat.SetoidEq
  setoidEq = Cat.SetoidEq.SETOIDEQ LD

record Homomorphism : Set where
  open LawfulCategory LD
  field
    obj-map : Obj C → Obj D
    hom-map : {a b : Obj C} → (a ⇒ b) → obj-map a ⇒ obj-map b
    ∘-map : {a b c : Obj C} {g : b ⇒ c} {f : a ⇒ b} → hom-map (g ∘ f) ≈ hom-map g ∘ hom-map f

    id-map : {a : Obj C} → hom-map (id {a}) ≈ id


record HomomorphismExt (hom : Homomorphism) {a b : Obj C} (f g : a ⇒ b) : Set where
  open Homomorphism hom
  open LawfulCategory LD

  field
    eq : hom-map f ≈ hom-map g

open import Relation.Binary.Structures using (IsEquivalence)


open Homomorphism
open HomomorphismExt
open LawfulCategory.HomReasoning LD using (_▹_; sym; refl; trans)
open LawfulCategory LD


makeLawful : Homomorphism → LawfulCategory C
_≈_     (makeLawful h) = HomomorphismExt h
eq (IsEquivalence.refl (≈-equiv (makeLawful h))) = refl
eq (IsEquivalence.sym (≈-equiv (makeLawful h)) x) = sym (eq x)
eq (IsEquivalence.trans (≈-equiv (makeLawful h)) x y) = trans (eq x) (eq y)
eq (∘-cong (makeLawful h) g≈ f≈) = ∘-map h ▹ ∘-cong (eq g≈) (eq f≈) ▹ sym (∘-map h)
eq (id-l (makeLawful h)) = ∘-map h ▹ ∘-cong (id-map h) refl ▹ id-l
eq (id-r (makeLawful h)) = ∘-map h ▹ ∘-cong refl (id-map h) ▹ id-r
eq (∘-assoc (makeLawful h))
  = ∘-map h
  ⨟ ∘-cong (∘-map h) refl
  ⨟ ∘-assoc
  ⨟ sym (∘-cong refl (∘-map h))
  ⨟ sym (∘-map h)

