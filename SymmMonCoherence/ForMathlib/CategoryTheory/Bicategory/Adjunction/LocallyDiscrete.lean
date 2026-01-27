/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# Equivalences in locally discrete bicategories.

In this file, we give a constructor for equivalences in `LocallyDiscrete C` out of
an isomorphism in `C`. -/

@[expose] public section

namespace CategoryTheory.LocallyDiscrete

open Bicategory
def mkEquivalence {C : Type*} [Category* C] {x y : C} (f : x ≅ y) :
    (LocallyDiscrete.mk x) ≌ (LocallyDiscrete.mk y) where
  hom := f.hom.toLoc
  inv := f.inv.toLoc
  unit := eqToIso (by simp [← Quiver.Hom.comp_toLoc])
  counit := eqToIso (by simp [← Quiver.Hom.comp_toLoc])

end CategoryTheory.LocallyDiscrete
