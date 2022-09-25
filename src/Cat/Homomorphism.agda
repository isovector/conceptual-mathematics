{-# OPTIONS --type-in-type #-}

open import Cat.Raw

module Cat.Homomorphism {C D : Category} (LD : LawfulCategory D) where

open Category C renaming (Obj to ObjC; _⇒_ to _⇒_; id to idC; _∘_ to _∘_)
open Category D renaming (Obj to ObjD; _⇒_ to _⊸_; id to idD; _∘_ to _⊚_)

record Homomorphism : Set where
  open LawfulCategory LD
  field
    obj-map : ObjC → ObjD
    hom-map : {a b : ObjC} → (a ⇒ b) → obj-map a ⊸ obj-map b
    id-map : {a : ObjC} → hom-map (idC {a}) ≈ idD
    ∘-map : {a b c : ObjC} {g : b ⇒ c} {f : a ⇒ b} → hom-map (g ∘ f) ≈ hom-map g ⊚ hom-map f


record HomomorphismExt (hom : Homomorphism) {a b : ObjC} (f g : a ⇒ b) : Set where
  open Homomorphism hom
  open LawfulCategory LD

  field
    eq : hom-map f ≈ hom-map g

open import Relation.Binary.Structures using (IsEquivalence)

open LawfulCategory

open Homomorphism
open HomomorphismExt
open HomReasoning LD
open LawfulCategory LD


makeLawful : Homomorphism → LawfulCategory C
_≈_     (makeLawful h) = HomomorphismExt h
eq (IsEquivalence.refl (≈-equiv (makeLawful h))) = refl
eq (IsEquivalence.sym (≈-equiv (makeLawful h)) x) = sym (eq x)
eq (IsEquivalence.trans (≈-equiv (makeLawful h)) x y) = trans (eq x) (eq y)
eq (∘-cong (makeLawful h) g≈ f≈) = ∘-map h ▹ ∘-cong LD (eq g≈) (eq f≈) ▹ sym (∘-map h)
eq (id-l (makeLawful h)) = ∘-map h ▹ ∘-cong LD (id-map h) refl ▹ id-l LD
eq (id-r (makeLawful h)) = ∘-map h ▹ ∘-cong LD refl (id-map h) ▹ id-r LD
eq (∘-assoc (makeLawful h))
  = ∘-map h
  ▹ ∘-cong LD (∘-map h) refl
  ▹ ∘-assoc LD
  ▹ sym (∘-cong LD refl (∘-map h))
  ▹ sym (∘-map h)

