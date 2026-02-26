/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import Mathlib.Tactic.CategoryTheory.MonoidalComp

/-! # Categories of symmetric monoidal functors

In this file, we show that symmetric monoidal functors `C ⥤ D` where `C` and `D`
are monoidal also form a symmetric monoidal category. We do this in an unbundled way,
by providing braided instances on `F ⊗ G`, and monoidal natural transformations instances
on the associators, unitors, etc. -/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Monoidal

section

@[simps!]
instance {C : Type*} [Category* C] {D : Type*} [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory D] (F G : C ⥤ D) [F.LaxMonoidal] [G.LaxMonoidal] : (F ⊗ G).LaxMonoidal :=
  inferInstanceAs (Functor.prod' F G ⋙ tensor D).LaxMonoidal

@[simps!]
instance {C : Type*} [Category* C] {D : Type*} [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory D] (F G : C ⥤ D) [F.OplaxMonoidal] [G.OplaxMonoidal] : (F ⊗ G).OplaxMonoidal :=
  inferInstanceAs (Functor.prod' F G ⋙ tensor D).OplaxMonoidal

instance {C : Type*} [Category* C] {D : Type*} [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory D] (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] : (F ⊗ G).Monoidal where

instance {C : Type*} [Category* C] {D : Type*} [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [SymmetricCategory D] (F G : C ⥤ D) [F.Braided] [G.Braided] :
    (F ⊗ G).Braided where
  braided X Y := by
    -- simp? [tensorμ, cancel_epi, tensorHom_def]
    simp only [Monoidal.tensorObj_obj, μ_def, tensorμ, tensorHom_def, whiskerRight_tensor,
      Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc, Monoidal.tensorObj_map,
      Functor.map_braiding, comp_whiskerRight, whiskerLeft_comp,
      BraidedCategory.braiding_tensor_right_hom, BraidedCategory.braiding_tensor_left_hom,
      whisker_assoc, pentagon_assoc, pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc,
      whiskerLeft_hom_inv_assoc, cancel_epi]
    simp_rw [← Category.assoc, cancel_mono, Category.assoc]
    simp_rw [associator_naturality_left_assoc, whisker_exchange_assoc, ← comp_whiskerRight_assoc,
      Functor.Monoidal.μ_δ_assoc, comp_whiskerRight_assoc, cancel_epi, ← whiskerLeft_comp_assoc,
        Functor.Monoidal.μ_δ, whiskerLeft_id_assoc, whiskerLeft_comp_assoc]
    rw [← cancel_mono (F.obj (Y ⊗ X) ◁ (β_ (G.obj X) (G.obj Y)).inv ≫
        (Functor.OplaxMonoidal.δ F Y X ▷ (G.obj X ⊗ G.obj Y)))]
    simp_rw [Category.assoc, whiskerLeft_hom_inv_assoc, associator_naturality_left_assoc,
      ← whisker_exchange_assoc, ← comp_whiskerRight, Functor.Monoidal.μ_δ,
      id_whiskerRight]
    -- Now it’s a pure braid computation
    simp only [tensor_whiskerLeft, Category.comp_id, pentagon_inv_hom_hom_hom_hom_assoc,
      Iso.inv_hom_id_assoc, SymmetricCategory.braiding_swap_eq_inv_braiding (F.obj X) (G.obj Y),
      ← whiskerLeft_comp_assoc, hom_inv_whiskerRight_assoc]
    simp

@[simps!]
instance unitMonoidal {C : Type*} [Category* C] {D : Type*} [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] :
    (𝟙_ (C ⥤ D)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := .refl _
      μIso X Y := λ_ _
      associativity X Y Z := by simp [unitors_equal]
      right_unitality := by simp [unitors_equal] }

instance {C : Type*} [Category* C] {D : Type*} [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D] :
    (𝟙_ (C ⥤ D)).Braided where
  braided X Y := by simp [unitors_inv_equal]

instance {C : Type*} [Category* C] {D : Type*} [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory D] {F G H : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal] :
    (α_ F G H).hom.IsMonoidal where
  unit := by
    dsimp
    simp only [ε_def, tensorObj_obj, unitors_inv_equal, tensorHom_def, whiskerRight_id,
      Category.assoc, Iso.inv_hom_id_assoc,
      tensor_whiskerLeft, Iso.inv_hom_id, Category.comp_id, whiskerLeft_comp]
    simp_rw [rightUnitor_tensor_inv]
    simp
  tensor X Y := by
    -- getting rid of all the `μ`'s to leave only braidings and associators
    simp only [tensorObj_obj, μ_def, tensorμ, tensor_whiskerLeft,
      BraidedCategory.braiding_tensor_right_hom, comp_whiskerRight, whisker_assoc, Category.assoc,
      whiskerLeft_comp, Iso.inv_hom_id_assoc, tensorHom_def, whiskerRight_tensor,
      pentagon_hom_inv_inv_inv_inv_assoc, pentagon_inv_inv_hom_hom_inv, associator_hom_app,
      Iso.inv_hom_id, Category.comp_id, BraidedCategory.braiding_tensor_left_hom,
      Iso.hom_inv_id_assoc]
    simp_rw [
      ← comp_whiskerRight_assoc, ← comp_whiskerRight, Category.assoc,
      associator_naturality_left, comp_whiskerRight_assoc, comp_whiskerRight, Category.assoc,
      associator_naturality_left_assoc, ← whisker_exchange_assoc, ← whisker_exchange,
      ← reassoc_of% comp_whiskerRight (Z := H.obj Y),
      ← reassoc_of% comp_whiskerRight (Z := H.obj X), associator_naturality_left,
      comp_whiskerRight (Z := H.obj X), Category.assoc, associator_naturality_left,
      comp_whiskerRight_assoc, associator_naturality_left_assoc]
    calc
      _ = 𝟙 _ ⊗≫
          (F.obj X ⊗ G.obj X) ◁ (β_ (H.obj X) (F.obj Y)).hom ▷ (G.obj Y ⊗ H.obj Y) ⊗≫
          (F.obj X) ◁
            ((G.obj X ⊗ F.obj Y) ◁ (β_ (H.obj X) (G.obj Y)).hom ≫
              (β_ (G.obj X) (F.obj Y)).hom ▷ (G.obj Y ⊗ H.obj X)) ▷ H.obj Y ⊗≫
            ((Functor.LaxMonoidal.μ F X Y ▷ (((G.obj X ⊗ G.obj Y) ⊗ H.obj X) ⊗ H.obj Y)) ≫
              (F.obj (X ⊗ Y) ◁ Functor.LaxMonoidal.μ G X Y ▷ H.obj X ▷ H.obj Y) ≫
              (F.obj (X ⊗ Y) ◁ (α_ (G.obj (X ⊗ Y)) (H.obj X) (H.obj Y)).hom) ≫
              F.obj (X ⊗ Y) ◁ G.obj (X ⊗ Y) ◁ Functor.LaxMonoidal.μ H X Y) ⊗≫ 𝟙 _ := by monoidal
      _ = _ := by
        rw [whisker_exchange (g := (β_ (H.obj X) (G.obj Y)).hom), ← whisker_exchange_assoc]
        simp_rw [ ← whiskerLeft_comp]
        rw [← whisker_exchange (f := Functor.LaxMonoidal.μ F X Y)]
        monoidal

instance {C : Type*} [Category* C] {D : Type*} [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory D] {F G H : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (α : G ⟶ H) [α.IsMonoidal] :
    (F ◁ α).IsMonoidal where
  unit := by
    have := NatTrans.IsMonoidal.unit (τ := α)
    simp only [tensorObj_obj, ε_def, tensorHom_def, whiskerRight_id, Category.assoc,
      whiskerLeft_app, Iso.cancel_iso_inv_left, Iso.cancel_iso_hom_left]
    simp_rw [← whiskerLeft_comp, this]
  tensor X Y := by
    have := NatTrans.IsMonoidal.tensor (τ := α) X Y
    simp only [tensorHom_def, Category.assoc] at this
    simp only [tensorObj_obj, μ_def, tensorHom_def, whiskerRight_tensor, Category.assoc,
      whiskerLeft_app, whisker_assoc, comp_whiskerRight, pentagon_inv_inv_hom_hom_inv,
      pentagon_inv_hom_hom_hom_inv_assoc, tensor_whiskerLeft,
      Iso.inv_hom_id_assoc] -- big computation
    simp_rw [← whiskerLeft_comp, this, whiskerLeft_comp, associator_naturality_left_assoc,
      ← whisker_exchange_assoc, ← whisker_exchange, Iso.inv_hom_id_assoc]
    simp only [tensorμ, tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.cancel_iso_hom_left]
    simp_rw [← whiskerLeft_comp_assoc]
    simp_rw [associator_inv_naturality_right_assoc,
      Iso.hom_inv_id_assoc, whisker_exchange_assoc, ← comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_left]
    simp

instance {C : Type*} [Category* C] {D : Type*} [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory D] {F G H : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (α : F ⟶ G) [α.IsMonoidal] :
    (α ▷ H).IsMonoidal where
  unit := by
    simp only [tensorObj_obj, ε_def, tensorHom_def, whiskerRight_id, Category.assoc,
      whiskerRight_app, Iso.cancel_iso_inv_left, Iso.cancel_iso_hom_left]
    have := NatTrans.IsMonoidal.unit (τ := α)
    simp_rw [whisker_exchange, rightUnitor_inv_naturality_assoc, ← comp_whiskerRight_assoc, this]
  tensor X Y := by
    have := NatTrans.IsMonoidal.tensor (τ := α) X Y
    simp only [tensorHom_def, Category.assoc] at this
    simp only [tensorObj_obj, μ_def, tensorHom_def, whiskerRight_tensor, Category.assoc,
      whiskerRight_app, tensor_whiskerLeft]
    simp_rw [whisker_exchange, associator_naturality_left_assoc, ← comp_whiskerRight_assoc,
      this, Iso.inv_hom_id_assoc, comp_whiskerRight_assoc]
    simp only [tensorμ, whiskerRight_tensor, whisker_assoc, comp_whiskerRight, Category.assoc,
      pentagon_inv_inv_hom_hom_inv, pentagon_inv_hom_hom_hom_inv_assoc,
      pentagon_hom_hom_inv_hom_hom_assoc, pentagon_hom_inv_inv_inv_inv_assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id_assoc]
    simp_rw [← comp_whiskerRight_assoc, ← associator_inv_naturality_left_assoc,
      associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, whisker_exchange_assoc,
      comp_whiskerRight_assoc, Iso.hom_inv_id_assoc, inv_hom_whiskerRight_assoc,
      ← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc,
      ← BraidedCategory.braiding_naturality_right]
    monoidal

instance {C : Type*} [Category* C] {D : Type*} [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory D] {F : C ⥤ D} [F.LaxMonoidal] :
    (λ_ F).hom.IsMonoidal where
  unit := by simp
  tensor X Y := by
    simp only [tensorObj_obj, tensorUnit_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, μ_def,
      tensorμ, id_whiskerLeft, braiding_tensorUnit_right, Functor.LaxMonoidal.right_unitality,
      Category.assoc, comp_whiskerRight, whisker_assoc, leftUnitor_inv_whiskerRight,
      whiskerLeft_comp, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, unitMonoidal_μ, tensorHom_def,
      whiskerRight_tensor, leftUnitor_whiskerRight, pentagon_inv_hom_hom_hom_inv_assoc,
      Iso.inv_hom_id, Category.comp_id, Functor.LaxMonoidal.μ_natural_left_assoc,
      leftUnitor_hom_app, Functor.LaxMonoidal.left_unitality,
      Functor.LaxMonoidal.left_unitality_inv_assoc, Iso.map_inv_hom_id, whiskerRight_id,
      triangle_assoc_comp_right_inv, triangle_assoc_comp_right_assoc, tensor_whiskerLeft,
      Functor.LaxMonoidal.μ_natural_right, Iso.cancel_iso_hom_left]
    simp_rw [← comp_whiskerRight_assoc, leftUnitor_tensor_inv_assoc, Iso.hom_inv_id_assoc,
      ← comp_whiskerRight_assoc, Functor.LaxMonoidal.left_unitality_inv_assoc,
      Iso.map_inv_hom_id, id_whiskerRight_assoc,
      ← whiskerLeft_comp_assoc, ← Functor.LaxMonoidal.left_unitality_assoc,
      Iso.hom_inv_id_assoc, whiskerLeft_comp, whisker_assoc_symm_assoc, Category.assoc,
      ← Functor.LaxMonoidal.associativity_assoc, Iso.hom_inv_id_assoc]
    congr 4
    simp [← Functor.map_comp]

instance {C : Type*} [Category* C] {D : Type*} [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory D] {F : C ⥤ D} [F.LaxMonoidal] :
    (ρ_ F).hom.IsMonoidal where
  unit := by simp [unitors_inv_equal]
  tensor X Y := by
    dsimp [tensorμ]
    simp only [μ_def, tensorUnit_obj, tensorμ, braiding_tensorUnit_left,
      Functor.LaxMonoidal.left_unitality, Category.assoc, whiskerRight_id, whiskerLeft_comp,
      whiskerLeft_rightUnitor, whiskerLeft_rightUnitor_inv, pentagon_hom_hom_inv_inv_hom,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, pentagon_hom_inv_inv_inv_hom_assoc,
      unitMonoidal_μ, tensorHom_def, whiskerRight_tensor, triangle,
      Functor.LaxMonoidal.right_unitality, Functor.LaxMonoidal.right_unitality_inv_assoc,
      Iso.map_inv_hom_id_assoc, Functor.LaxMonoidal.μ_natural_right_assoc, Iso.map_inv_hom_id,
      Category.comp_id, comp_whiskerRight, whisker_assoc, Functor.LaxMonoidal.μ_natural_right,
      Functor.map_comp, Functor.LaxMonoidal.associativity_inv_assoc, Iso.cancel_iso_inv_left,
      Iso.cancel_iso_hom_left]
    congr 1
    simp_rw [rightUnitor_tensor_inv_assoc, Iso.inv_hom_id_assoc, ← whisker_exchange_assoc]
    have e₁ := Functor.LaxMonoidal.associativity F X (𝟙_ C) Y
    simp only [whiskerLeft_rightUnitor_inv, tensor_whiskerLeft, whiskerRight_tensor, Category.assoc,
      Iso.hom_inv_id_assoc]
    simp_rw [← comp_whiskerRight_assoc, rightUnitor_tensor_inv_assoc, Iso.inv_hom_id_assoc]
    simp only [whiskerLeft_rightUnitor_inv, comp_whiskerRight, Category.assoc,
      Functor.LaxMonoidal.μ_natural_left, Functor.LaxMonoidal.μ_natural_left_assoc, whiskerRight_id,
      Functor.map_comp, Iso.map_inv_hom_id, Category.comp_id]
    simp_rw [← comp_whiskerRight_assoc, rightUnitor_tensor_inv_assoc, Iso.inv_hom_id_assoc,
      ← cancel_epi ((α_ (F.obj X) (F.obj (𝟙_ C)) (F.obj Y)).hom),
      Iso.hom_inv_id_assoc, tensor_whiskerLeft_assoc,
      associator_inv_naturality_right_assoc, Iso.hom_inv_id_assoc,
      whisker_exchange_assoc]
    simp only [whiskerLeft_rightUnitor_inv,
      whiskerRight_id, Category.assoc, Functor.LaxMonoidal.right_unitality_inv_assoc,
      Iso.map_inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
    rw [← reassoc_of% e₁]
    congr 2
    simp [← Functor.map_comp]

instance {C : Type*} [Category* C] {D : Type*} [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [SymmetricCategory D] {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] :
    (β_ F G).hom.IsMonoidal where
  unit := by
    simp only [tensorObj_obj, ε_def, tensorHom_def, whiskerRight_id, Category.assoc,
      BraidedCategory.braiding, NatIso.ofComponents_hom_app,
      BraidedCategory.braiding_naturality_right, braiding_tensorUnit_right,
      Functor.LaxMonoidal.right_unitality, Functor.LaxMonoidal.right_unitality_inv_assoc,
      Iso.map_inv_hom_id_assoc, Iso.cancel_iso_inv_left, Iso.cancel_iso_hom_left]
    have e₁ := Functor.LaxMonoidal.left_unitality_inv F (𝟙_ _)
    have e₂ := Functor.LaxMonoidal.right_unitality_inv F (𝟙_ _)
    have e₃ := Functor.LaxMonoidal.left_unitality F (𝟙_ _)
    have e₄ := Functor.LaxMonoidal.right_unitality F (𝟙_ _)
    rw [leftUnitor_inv_naturality_assoc, whisker_exchange]
    simp [unitors_inv_equal]
  tensor X Y := by
    simp only [tensorObj_obj, μ_def, tensorμ, tensorHom_def', tensor_whiskerLeft, Category.assoc,
      Iso.inv_hom_id_assoc, BraidedCategory.braiding, NatIso.ofComponents_hom_app,
      BraidedCategory.braiding_naturality_left, BraidedCategory.braiding_tensor_left_hom,
      whiskerRight_tensor, pentagon_hom_hom_inv_hom_hom_assoc, Iso.cancel_iso_hom_left]
    simp_rw [associator_inv_naturality_right_assoc, whisker_exchange, ← whiskerLeft_comp_assoc,
      BraidedCategory.braiding_naturality_right, whiskerLeft_comp_assoc,
      associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
      BraidedCategory.braiding_tensor_right_hom, whiskerLeft_comp_assoc,
      comp_whiskerRight_assoc, SymmetricCategory.braiding_swap_eq_inv_braiding (G.obj X) (F.obj Y),
      whiskerLeft_hom_inv_assoc, ← whiskerLeft_comp_assoc, hom_inv_whiskerRight_assoc,
      whiskerLeft_comp]
    monoidal

end

end CategoryTheory.Monoidal
