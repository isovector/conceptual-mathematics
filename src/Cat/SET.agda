open import Cat.Base

module Cat.SET (ℓ : Level) where

open Category
import Function
import Function.Properties
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≗_; _→-setoid_)
  public
open import Relation.Binary using (Setoid)

SET : Category _ _
Obj SET = Set ℓ
_⇒_ SET x y = x → y
_≈_ SET = _≗_
equiv SET = (_ →-setoid _) .Setoid.isEquivalence
id SET = Function.id
_∘_ SET g f = g Function.∘ f
identityˡ SET f x = refl
identityʳ SET f x = refl
assoc SET h g f x = refl
cong SET {_} {f} {g} {h} {i} f=g h=i x
  rewrite h=i x
  rewrite f=g (i x)
    = refl

