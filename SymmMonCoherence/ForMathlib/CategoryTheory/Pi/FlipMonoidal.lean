/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Pi.Monoidal

/-! # Flipping variable as a monoidal functor. -/

universe w₁ v₁ u₁
@[expose] public section

namespace CategoryTheory.Pi

variable (C : Type u₁) [Category.{v₁} C]

@[simps!]
def flipFunctor (I J : Type*) : (I → J → C) ⥤ (J → I → C) where
  obj X := fun i j ↦ X j i
  map f := fun i j ↦ f j i

@[simps!]
instance flipMonoidal (I J : Type*) [MonoidalCategory C] : Functor.Monoidal (flipFunctor C I J) :=
  letI : Functor.CoreMonoidal (flipFunctor C I J) :=
    { εIso := .refl _
      μIso X Y := .refl _  }
  this.toMonoidal

instance (I J : Type*) [MonoidalCategory C] [SymmetricCategory C] :
    Functor.Braided (flipFunctor C I J) where
  braided X Y := by ext i; simp

end CategoryTheory.Pi
