/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.Spans.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

@[expose] public section

/-! # Inclusions in spans
Given a category with pullbacks `C`, we construct pseudofunctorial inclusions
`inl : (LocallyDiscrete C) ⥤ᵖ Spans ⊤ ⊤` and `inr : (LocallyDiscrete Cᵒᵖ) ⥤ᵖ Spans ⊤ ⊤`

-/
namespace CategoryTheory.Spans
variable (C : Type*) [Category* C]
open Bicategory
variable [Limits.HasPullbacks C]

@[simps]
noncomputable def inl :
    LocallyDiscrete C ⥤ᵖ (Spans C (⊤ : MorphismProperty C) ⊤) where
  obj c := .mk c.as
  map {c c'} f := Spans.mkHom c.as (𝟙 _) f.as (by tauto) (by tauto)
  map₂ η := Spans.mkHom₂ (𝟙 _) (hᵣ := by simp [LocallyDiscrete.eq_of_hom η])
  mapId x := Spans.mkIso₂ (.refl _)
  mapComp {x y z} f g :=
    Spans.mkIso₂
      { hom := compLiftApex (𝟙 _) f.as
        inv := πₗ ..
        inv_hom_id := by
          ext
          · simp
          · conv_rhs => rw [← Category.comp_id (πᵣ _ _)]
            simpa [-Category.comp_id] using comp_comm _ _ }

open Opposite in
@[simps]
noncomputable def inr :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ (Spans C (⊤ : MorphismProperty C) ⊤) where
  obj c := .mk c.as.unop
  map {c c'} f := Spans.mkHom c'.as.unop f.as.unop (𝟙 _) (by tauto) (by tauto)
  map₂ η := Spans.mkHom₂ (𝟙 _) (hₗ := by simp [LocallyDiscrete.eq_of_hom η])
  mapId x := Spans.mkIso₂ (.refl _)
  mapComp {x y z} f g :=
    Spans.mkIso₂
      { hom := compLiftApex g.as.unop (𝟙 _)
        inv := πᵣ ..
        inv_hom_id := by
          ext
          · conv_rhs => rw [← Category.comp_id (πₗ _ _)]
            simpa [-Category.comp_id] using (comp_comm _ _).symm
          · simp }

end CategoryTheory.Spans
