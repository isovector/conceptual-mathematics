{-# OPTIONS --type-in-type #-}

module Cat.PropEq where

open import Cat.Raw
open Category
open LawfulCategory

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures using (IsEquivalence)


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
id-l    PROPEQ-laws {f = refl} = refl
id-r    PROPEQ-laws {f = refl} = refl
∘-assoc PROPEQ-laws {h = refl} {refl} {refl} = refl

