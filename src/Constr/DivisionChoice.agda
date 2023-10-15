{-# OPTIONS --allow-unsolved-metas #-}

module Constr.DivisionChoice where

open import Cat.Base

module Definition {ℓ₁ ℓ₂ : Level} (c : Category ℓ₁ ℓ₂) where
  open import Relation.Binary
    using (Rel; Reflexive; Symmetric; Transitive)
  open Category c

  private variable
    A B C : Obj

  -- DEFINITION, page 45
  -- alsa called an "extension" problem
  record _is-determined-by_ (h : A ⇒ C) (f : A ⇒ B) : Set ℓ₂ where
    field
      factoring : B ⇒ C
      determines : factoring ∘ f ≈ h


  -- DEFINITION, page 45
  -- alsa called a "lifting" problem
  record _is-chosen-by_ (h : A ⇒ C) (g : B ⇒ C) : Set ℓ₂ where
    field
      factoring : A ⇒ B
      chooses : g ∘ factoring ≈ h


module Example-SET where
  open import Cat.SET
  open Definition SET
  open Category SET

  open import Data.Nat
  open import Data.Fin
  open import Function using (const)

  open _is-chosen-by_
  open _is-determined-by_

  -- Page 45
  module Example1 where
    postulate
      a c : ℕ

      h : Fin a → Fin c
      f : Fin a → Fin 1
      g : Fin 1 → Fin c

      -- Unrestricted, we would expect there to be cᵃ choices for h. But the
      -- restriction that `h is-determined-by f` means there are in fact only
      -- c many!


  -- Page 46
  module Example2 where
    A = Fin 2
    B = Fin 3
    C = Fin 2

    h : A → C
    h a = a

    g : B → C
    g zero = zero
    g (suc x) = x

    -- try a boring injection into Fin 3
    try₁ : h is-chosen-by g
    factoring try₁ = inject₁
    chooses try₁ zero = refl
    chooses try₁ (suc zero) = {! zero ≢ suc zero !}  -- uh oh!

    f : A → B
    f zero = zero
    f (suc x) = suc (suc x)

    -- instead; it must be the case that f respects the equality
    try₂ : h is-chosen-by g
    factoring try₂ = f
    chooses try₂ zero = refl
    chooses try₂ (suc zero) = refl

    -- Lets think about the cardinalites here. Again naively we should expect
    -- there to be bᵃ possible options for f, but it's unclear how many there are
    -- in general now
    --
    -- Q for the group?

    other-way : h is-determined-by f
    factoring other-way zero = zero
    factoring other-way (suc zero) = zero -- agda can infer the other two; but this one is left up to us
    factoring other-way (suc (suc zero)) = suc zero
    determines other-way zero = refl
    determines other-way (suc zero) = refl

    -- AGDA CAN SOLVE DETERMINIATION PROBLEMS???
    -- but not choice problems? very interesting

  module Exercise5 where
    open import Data.Bool

    B = Fin 5
    A = Bool

    g : B → A
    g zero = false
    g (suc zero) = false
    g (suc (suc zero)) = false
    g (suc (suc (suc x))) = true

    choice : id is-chosen-by g
    factoring choice false = zero
    factoring choice true = suc (suc (suc zero))
    chooses choice false = refl
    chooses choice true = refl

    -- how many? we have 3 places we can send false, and 2 we can send true
    -- so 6 total

  module Pick'sForumla where
    -- need a function f : ℕ → ℕ → ℚ
    -- such that f(3, 17) = 10.5

    --     + +
    --     + +
    -- and f(0, 4) = 1

    --     + - +
    --     + - +
    -- and f(0, 6) = 2

    --     + - +
    --     | . |
    --     + - +
    -- and f(1, 8) = 4

    -- maybe
    -- f i p = i + (p - 2) / 2
    --
    -- looks good!

    -- Why is this a determination problem? Because we are given the mapping
    -- from the domain into the abstract problem space, and are asked only to
    -- to figure out what to do with that abstract problem space!
    -- The solution is determined by the choice of abstract problem space.


open Definition public
