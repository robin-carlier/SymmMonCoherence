/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.SingleObj

namespace CategoryTheory

/-- A "weight" on a category `C` in a monoid `M`
is the data of a function from morphisms in `C` to `M`
that sends identities to the neutral element, and sends
compositions to multiplications. Under the hood, this is a functor
from `C` to a one-object category. -/
public structure weight (C : Type*) [Category* C] (M : Type*) [Monoid M] where
  F : C ⥤ (SingleObj M)ᵒᵖ

namespace weight

section Monoid

variable {C : Type*} [Category* C] {M : Type*} [Monoid M]

public def app (w : weight C M) {x y : C} (f : x ⟶ y) : M := Quiver.Hom.unop <| w.F.map f

public lemma app_eq (w : weight C M) {x y : C} (f : x ⟶ y) :
    (Quiver.Hom.unop <| w.F.map f) = w.app f := (rfl)

@[simp, grind =]
public lemma weight_id {w : weight C M} (x : C) : w.app (𝟙 x) = 1 := by
  simp only [app, Functor.map_id]
  rfl

@[simp, grind =]
public lemma weight_comp {w : weight C M} {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    w.app (f ≫ g) = w.app f * w.app g := by
  simp only [app, Functor.map_comp, unop_comp]
  rfl

public lemma app_mk (F : C ⥤ (SingleObj M)ᵒᵖ) {x y : C} (f : x ⟶ y) :
    (weight.mk F).app f = (F.map f).unop :=
  (rfl)

@[simp, grind =]
public lemma app_eqToHom {w : weight C M} {i j : C} (h : i = j) : w.app (eqToHom h) = 1 := by
  subst h
  simp

public def postComp (w : weight C M) {M' : Type*} [Monoid M'] (φ : M →* M') : weight C M' where
  F := w.F ⋙ (SingleObj.mapHom _ _ φ).op

@[simp, grind =]
public lemma postComp_app (w : weight C M) {M' : Type*} [Monoid M'] (φ : M →* M')
    {x y : C} (f : x ⟶ y) :
    (w.postComp φ).app f = φ (w.app f) :=
  (rfl)

public lemma isUnit_of_isIso (w : weight C M) {x y : C} (f : x ⟶ y) [IsIso f] :
    IsUnit (w.app f) :=
  ⟨⟨w.app f, w.app (inv f), by simp [← weight_comp], by simp [← weight_comp]⟩, rfl⟩

end Monoid

section Group

variable {C : Type*} [Category* C] {G : Type*} [Group G]

@[simp, grind =]
public lemma app_inv {w : weight C G} {x y : C} (f : x ⟶ y) [IsIso f] :
    w.app (inv f) = (w.app f)⁻¹ := by
  simp [ eq_inv_iff_mul_eq_one, ← weight_comp]

@[simp, grind =]
public lemma app_inv' {w : weight C G} {x y : C} (f : x ≅ y) :
    w.app f.inv = (w.app f.hom)⁻¹ := by
  simp [ eq_inv_iff_mul_eq_one, ← weight_comp]

end Group

end weight

end CategoryTheory
