/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
-- public import SymmMonCoherence.ForMathlib.Tactic.CategoryTheory.RotateIso

/-!
# Pseudofunctors map equivalences to equivalences and adjunctions to adjunctions

In this file, we provide `Pseudofunctor.mapAdj` and `Pseudofunctor.mapEquiv` as
bicategorical analogues of `Functor.mapIso`. -/

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Pseudofunctor

open Bicategory

variable {C : Type u₁} {D : Type u₂} [Bicategory.{w₁, v₁} C] [Bicategory.{w₂, v₂} D] (F : C ⥤ᵖ D)

section

@[reassoc]
lemma map₂_associator_inv {a b c d : C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map₂ (α_ f g h).inv =
    (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom ≫
      (α_ (F.map f) (F.map g) (F.map h)).inv ≫ (F.mapComp f g).inv ▷ F.map h ≫
      (F.mapComp (f ≫ g) h).inv := by
  simp [← IsIso.inv_eq_inv, ← PrelaxFunctor.map₂_inv]

@[reassoc]
lemma map₂_left_unitor_inv {a b : C} (f : a ⟶ b) :
    F.map₂ (λ_ f).inv =
    (λ_ (F.map f)).inv ≫ (F.mapId a).inv ▷ F.map f ≫ (F.mapComp (𝟙 a) f).inv := by
  simp [← IsIso.inv_eq_inv, ← PrelaxFunctor.map₂_inv]

@[reassoc]
lemma map₂_right_unitor_inv {a b : C} (f : a ⟶ b) :
    F.map₂ (ρ_ f).inv =
    (ρ_ (F.map f)).inv ≫  F.map f ◁ (F.mapId b).inv ≫ (F.mapComp f (𝟙 b)).inv := by
  simp [← IsIso.inv_eq_inv, ← PrelaxFunctor.map₂_inv]

end
/-- A pseudofunctor maps an adjunction in the source bicategory to an adjunction
in the target bicategory. -/
@[simps]
def mapAdj {x y : C} {f : x ⟶ y} {g : y ⟶ x} (adj : f ⊣ g) :
    F.map f ⊣ F.map g where
  unit := (F.mapId _).inv ≫ F.map₂ (adj.unit) ≫ (F.mapComp _ _).hom
  counit := (F.mapComp _ _).inv ≫ F.map₂ (adj.counit) ≫ (F.mapId _).hom
  left_triangle := by
    have := congr(F.map₂ $(adj.left_triangle)) =≫ (F.mapComp f (𝟙 y)).hom
    dsimp [leftZigzag, bicategoricalComp] at this ⊢
    simp only [whiskerRight_comp, id_whiskerRight, Category.id_comp, Iso.inv_hom_id,
      Category.comp_id, PrelaxFunctor.map₂_comp, map₂_whisker_right, map₂_associator,
      map₂_whisker_left, Category.assoc, Iso.inv_hom_id_assoc, map₂_left_unitor,
      Iso.cancel_iso_hom_left, comp_whiskerRight, whiskerLeft_comp] at this ⊢
    simp [reassoc_of% this, inv_hom_whiskerRight_assoc, map₂_right_unitor_inv]
  right_triangle := by
    have e₁ := congr(F.map₂ $(adj.right_triangle)) =≫ (F.mapComp (𝟙 y) g).hom
    dsimp [rightZigzag, bicategoricalComp] at e₁ ⊢
    simp only [whiskerRight_comp, id_whiskerRight, Category.id_comp, Iso.inv_hom_id,
      PrelaxFunctor.map₂_comp, map₂_whisker_left, map₂_whisker_right, Category.assoc,
      Category.comp_id, map₂_right_unitor, Iso.cancel_iso_hom_left, whiskerLeft_comp,
      comp_whiskerRight] at e₁ ⊢
    simp_rw [map₂_associator_inv, Category.assoc, Iso.inv_hom_id_assoc] at e₁
    simp [reassoc_of% e₁, map₂_left_unitor_inv]

@[simps]
def _root_.CategoryTheory.Bicategory.Equivalence.adjunction {x y : C} (e : x ≌ y) :
    e.hom ⊣ e.inv where
  unit := e.unit.hom
  counit := e.counit.hom
  left_triangle := congr($(e.left_triangle).hom)
  right_triangle := congr($(e.right_triangle).hom)

@[simps]
/- The inverse equivalence of an equivalence internal to a bicategory. -/
def _root_.CategoryTheory.Bicategory.Equivalence.symm {x y : C} (e : x ≌ y) :
    y ≌ x where
  hom := e.inv
  inv := e.hom
  unit := e.counit.symm
  counit := e.unit.symm
  left_triangle := by
    have := congr(Iso.symm <| $e.right_triangle)
    dsimp [leftZigzagIso, rightZigzagIso, bicategoricalIsoComp] at this ⊢
    simpa using this

@[simps]
/- Transitivity of equivalence. -/
def _root_.CategoryTheory.Bicategory.Equivalence.trans {x y z: C} (e : x ≌ y) (e' : y ≌ z) :
    x ≌ z where
  hom := e.hom ≫ e'.hom
  inv := e'.inv ≫ e.inv
  unit :=
    e.unit ≪≫
      whiskerLeftIso e.hom (λ_ _).symm
      ≪≫ whiskerLeftIso e.hom (whiskerRightIso e'.unit _)
      ≪≫ whiskerLeftIso e.hom (α_ _ _ _)
      ≪≫ (α_ _ _ _).symm
  counit :=
    (α_ _ _ _)
      ≪≫ whiskerLeftIso e'.inv (α_ _ _ _).symm
      ≪≫ whiskerLeftIso e'.inv (whiskerRightIso e.counit _)
      ≪≫ whiskerLeftIso e'.inv (λ_ _)
      ≪≫ e'.counit
  left_triangle := by
    ext
    dsimp
    have := e.adjunction.comp e'.adjunction |>.left_triangle
    simpa [leftZigzag, bicategoricalComp] using this

lemma _root_.CategoryTheory.Bicategory.Equivalence.trans_adjunction
    {x y z: C} (e : x ≌ y) (e' : y ≌ z) :
    (e.trans e').adjunction = e.adjunction.comp e'.adjunction := by
  ext
  · simp [bicategoricalComp]
  · simp [bicategoricalComp]

lemma _root_.CategoryTheory.Bicategory.Equivalence.symm_trans_adjunction
    {x y z: C} (e : x ≌ y) (e' : y ≌ z) :
    (e.trans e').symm.adjunction = e'.symm.adjunction.comp e.symm.adjunction := by
  ext
  · simp [bicategoricalComp]
  · simp [bicategoricalComp]

/-- A pseudofunctor maps an equivalence in the source bicategory to an equivalence
in the target bicategory. This is the bicategorical version of `Functor.mapIso`. -/
@[simps]
def mapEquivalence {x y : C} (e : x ≌ y) :
    F.obj x ≌ F.obj y where
  hom := F.map e.hom
  inv := F.map e.inv
  unit := (F.mapId _).symm ≪≫ F.map₂Iso e.unit ≪≫ (F.mapComp _ _)
  counit := (F.mapComp _ _).symm ≪≫ F.map₂Iso e.counit ≪≫ (F.mapId _)
  left_triangle := by
    ext
    exact (F.mapAdj (e.adjunction)).left_triangle

end CategoryTheory.Pseudofunctor
