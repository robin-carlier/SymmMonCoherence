/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Pi.Basic

universe w₀ w₁ w₂ v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {I : Type w₀} {J : Type w₁} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)]
variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)] {A : Type u₃} [Category.{v₃} A]

def pi'Comp

end CategoryTheory.Functor
