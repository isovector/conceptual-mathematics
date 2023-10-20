open import Algebra.Bundles using (Monoid)
open import Cat.Base

module Cat.Monoid {c : Level} (M : Monoid c c) where
  open Monoid M
    renaming (_≈_ to _≈ₘ_)
  open Category
  open import Data.Unit

  monoidCat : Category lzero c
  Obj monoidCat = ⊤
  _⇒_ monoidCat _ _ = Carrier
  _≈_ monoidCat = _≈ₘ_
  equiv monoidCat = isEquivalence
  id monoidCat = ε
  _∘_ monoidCat = _∙_
  Category.identityˡ monoidCat = Monoid.identityˡ M
  Category.identityʳ monoidCat = Monoid.identityʳ M
  Category.assoc monoidCat = Monoid.assoc M
  cong monoidCat = ∙-cong
