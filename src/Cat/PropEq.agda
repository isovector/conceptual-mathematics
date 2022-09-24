{-# OPTIONS --type-in-type #-}

module Cat.PropEq where

open import Cat.Raw
open Category
open LawfulCategory

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures using (IsEquivalence)


module _ where

  PROPEQ : Category
  Obj PROPEQ     = Set
  _⇒_ PROPEQ     = _≡_
  id PROPEQ      = refl
  _∘_ PROPEQ g f = trans f g

  PROPEQ-laws : LawfulCategory PROPEQ
  _≈_     PROPEQ-laws = _≡_
  IsEquivalence.refl  (≈-equiv PROPEQ-laws {a} {b}) = refl
  IsEquivalence.sym   (≈-equiv PROPEQ-laws {a} {b}) refl = refl
  IsEquivalence.trans (≈-equiv PROPEQ-laws {a} {b}) refl refl = refl
  ∘-cong  PROPEQ-laws refl refl = refl
  id-l    PROPEQ-laws refl = refl
  id-r    PROPEQ-laws refl = refl
  ∘-assoc PROPEQ-laws refl refl refl = refl


module _ where

  SET : Category
  Obj SET = Set
  _⇒_ SET a b = a → b
  id  SET a = a
  _∘_ SET g f a = g (f a)


  SET-laws : LawfulCategory SET
  _≈_     SET-laws = _≗_
  IsEquivalence.refl  (≈-equiv SET-laws) x       = refl
  IsEquivalence.sym   (≈-equiv SET-laws) z a     = sym (z a)
  IsEquivalence.trans (≈-equiv SET-laws) y z a   = trans (y a) (z a)
  ∘-cong  SET-laws {g' = g'} g≈ f≈ a = trans (g≈ _) (cong g' (f≈ a))
  id-l    SET-laws f a = refl
  id-r    SET-laws f a = refl
  ∘-assoc SET-laws h g f a = refl

