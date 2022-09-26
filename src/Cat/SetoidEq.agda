{-# OPTIONS --type-in-type #-}

open import Cat.Raw

module Cat.SetoidEq { C : Category } ( LC : LawfulCategory C ) where

open Category
open LawfulCategory

open import Relation.Binary.Structures using (IsEquivalence)


SETOIDEQ : {A B : Obj C} → Category
Obj (SETOIDEQ {A} {B}) =  _⇒_ C A B
_⇒_ SETOIDEQ     = _≈_ LC
id SETOIDEQ      = IsEquivalence.refl (≈-equiv LC)
_∘_ SETOIDEQ g f = IsEquivalence.trans (≈-equiv LC) f g


