open import Cat.Raw

module Cat.Op {C : Category} (LC : LawfulCategory C)  where

open Category C
open LawfulCategory LC

data OpArr : Obj → Obj → Set where
  op : {a b : Obj} → a ⇒ b → OpArr b a

OP : Category
Category.Obj OP = Obj
Category._⇒_ OP = OpArr
Category.id OP = op id
Category._∘_ OP (op g) (op f) = op (f ∘ g)

open import Relation.Binary.Structures using (IsEquivalence)
open IsEquivalence

OP-laws : LawfulCategory OP
LawfulCategory._≈_ OP-laws (op f) (op g) = f ≈ g
refl (LawfulCategory.≈-equiv OP-laws) {op x} = refl ≈-equiv
sym (LawfulCategory.≈-equiv OP-laws) {op x₁} {op x₂} x = sym ≈-equiv x
trans (LawfulCategory.≈-equiv OP-laws) {op x₂} {op x₃} {op x₄} x x₁ = trans ≈-equiv x x₁
LawfulCategory.∘-cong OP-laws {g = op x₂} {op x₃} {f = op x₄} {op x₅} x x₁ = ∘-cong x₁ x
LawfulCategory.id-l OP-laws {a} {b} {op x} = id-r
LawfulCategory.id-r OP-laws {a} {b} {op x} = id-l
LawfulCategory.∘-assoc OP-laws {a} {b} {c} {d} {op x} {op x₁} {op x₂} = ⨟-assoc

