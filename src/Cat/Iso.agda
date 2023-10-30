open import Cat.Base

module Cat.Iso {ℓ₁ ℓ₂ : Level} (c : Category ℓ₁ ℓ₂) where

open Category
open import Constr.Iso c
open import Data.Product
open import Relation.Binary hiding (_⇒_)
open IsEquivalence


Iso : Category _ _
Obj Iso     = Obj c
_⇒_ Iso     = Isomorphic
_≈_ Iso f g = _≈_ c (proj₁ f) (proj₁ g)
refl  (equiv Iso) = refl (equiv c)
sym   (equiv Iso) = sym (equiv c)
trans (equiv Iso) = trans (equiv c)
id  Iso = iso-refl
_∘_ Iso = _≅∘_
identityˡ Iso (f , f-iso) = identityˡ c f
identityʳ Iso (f , f-iso) = identityʳ c f
assoc Iso h g f = assoc c _ _ _
cong  Iso g=g f=f = cong c g=g f=f

