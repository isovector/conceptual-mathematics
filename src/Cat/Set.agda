{-# OPTIONS --type-in-type #-}

module Cat.Set where

open import Cat.Raw
open Category
open LawfulCategory

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures using (IsEquivalence)

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
id-l    SET-laws {f = f} a = refl
id-r    SET-laws {f = f} a = refl
∘-assoc SET-laws {h = h} {g} {f} a = refl

