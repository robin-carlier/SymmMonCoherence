/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

import all SymmMonCoherence.Spans.PseudoFromBurnside.Assoc
public import SymmMonCoherence.Spans.PseudoFromBurnside.Assoc
public import Mathlib.Tactic.CategoryTheory.BicategoricalComp

/-! # Pseudofunctors from the effective Burnside (2,1)-category . -/

namespace CategoryTheory.EffBurnside.PseudoFunctorCore

open CategoryTheory Bicategory

universe w₁ v₁ v₂ u₁ u₂

variable {C : Type v₁} [Category.{u₁} C] {B : Type u₂} [Bicategory.{w₁, v₂} B]
    (P : PseudoFunctorCore C B)

noncomputable section toPseudoFunctor

variable [Limits.HasPullbacks C]

open Spans

section whiskerLeft

lemma 𝔯_whiskerLeft₁ {a b c : EffBurnside C} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (P.𝔯 f g).inv ≫ (P.vComp' (f.of ◁ η.iso.hom).hom (f.of ≫ h.of).l (f.of ≫ g.of).l).hom =
    P.v f.of.l ◁ (P.vComp' (f.of ◁ η.iso.hom).hom (πₗ f.of h.of) (πₗ f.of g.of)).hom ≫
    (α_ (P.v f.of.l) (P.v (πₗ f.of h.of)) (P.v (f.of ◁ η.iso.hom).hom)).inv ≫
      (P.𝔯 f h).inv ▷ P.v (f.of ◁ η.iso.hom).hom :=
  rotate_isos% 0 1
    (inv% P.vComp'₀₂₃_hom
      (f₀₁ := (f.of ◁ η.iso.hom).hom) (f₁₂ := πₗ f.of h.of) (f₂₃ := f.of.l)
      (f₀₂ := πₗ f.of g.of) (f₁₃ := (f.of ≫ h.of).l) (f := (f.of ≫ g.of).l)
      (by simp) (by simp) (by simp))

lemma 𝔩_whiskerLeft₁ {a b c : EffBurnside C} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (P.uComp' (f.of ◁ η.iso.hom).hom (f.of ≫ h.of).r (f.of ≫ g.of).r).hom ≫
      P.u (f.of ◁ η.iso.hom).hom ◁ (P.𝔩 f h).hom =
    (P.uComp' (πᵣ f.of g.of ≫ η.iso.hom.hom) h.of.r (f.of ≫ g.of).r).hom ≫
      (P.uComp' (f.of ◁ η.iso.hom).hom (πᵣ f.of h.of) (πᵣ f.of g.of ≫ η.iso.hom.hom)).hom ▷
        P.u h.of.r ≫
      (α_ (P.u (f.of ◁ η.iso.hom).hom) (P.u (πᵣ f.of h.of)) (P.u h.of.r)).hom :=
  rotate_isos% 0 1 (P.uComp'₀₁₃_hom
    (f₀₁ := (f.of ◁ η.iso.hom).hom) (f₁₂ := πᵣ f.of h.of) (f₂₃ := h.of.r)
    (f₀₂ := πᵣ f.of g.of ≫ η.iso.hom.hom) (f₁₃ := (f.of ≫ h.of).r) (f := (f.of ≫ g.of).r)
    (by simp) (by simp) (by simp))

private lemma isPullback_πₗ_πᵣ_comp_iso_hom
    {a b c : EffBurnside C} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    IsPullback (πₗ f.of g.of) (πᵣ f.of g.of ≫ η.iso.hom.hom) f.of.r h.of.l := by
  have := (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone f.of h.of)
  simp only [compPullbackCone_pt, compPullbackCone_fst, compPullbackCone_snd] at this
  let E := Spans.apexIso (asIso (f ◁ η).iso.hom)
  have :=
    IsPullback.of_iso this (e₁ := E.symm) (e₂ := .refl _) (e₃ := .refl _) (e₄ := .refl _)
      (g' := h.of.l) (f' := f.of.r) (snd' := πᵣ f.of g.of ≫ η.iso.hom.hom ) (fst' := πₗ _ _)
      (by simp [E]) (by simp [E]) (by simp) (by simp)
  exact this

private lemma isPullback_πₗ_comp_iso_hom_πᵣ
    {a b c : EffBurnside C} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    IsPullback (πₗ f.of h.of ≫ η.iso.hom.hom) (πᵣ f.of h.of) g.of.r h.of.l := by
  have := (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone f.of h.of)
  simp only [compPullbackCone_pt, compPullbackCone_fst, compPullbackCone_snd] at this
  have :=
    IsPullback.of_iso this
      (g' := h.of.l) (f' := g.of.r) (snd' := πᵣ f.of h.of) (fst' := πₗ f.of h.of ≫ η.iso.hom.hom)
      (e₁ := .refl _) (e₂ := Spans.apexIso (asIso η.iso.hom)) (e₃ := .refl _) (.refl _)
      (by simp) (by simp) (by simp) (by simp)
  exact this

lemma map₂_whisker_left_aux₁ {a b c : EffBurnside C} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (ρ_ (P.u f.of.r ≫ P.v h.of.l)).inv ≫
    (α_ (P.u f.of.r) (P.v h.of.l) (𝟙 (P.obj h.of.apex))).hom ≫
    (P.u f.of.r ◁ P.v h.of.l ◁ (P.ε η).inv) ≫
    (P.u f.of.r ◁ (α_ (P.v h.of.l) (P.v η.iso.hom.hom) (P.u η.iso.hom.hom)).inv) ≫
    (P.u f.of.r ◁ (P.vComp' η.iso.hom.hom h.of.l g.of.l).inv ▷ P.u η.iso.hom.hom) ≫
    (α_ (P.u f.of.r) (P.v g.of.l) (P.u η.iso.hom.hom)).inv ≫
    ((P.Γ f g).hom ▷ P.u η.iso.hom.hom) ≫
    (α_ (P.v (πₗ f.of g.of)) (P.u (πᵣ f.of g.of)) (P.u η.iso.hom.hom)).hom ≫
      P.v (πₗ f.of g.of) ◁
        (P.uComp' (πᵣ f.of g.of) η.iso.hom.hom (πᵣ f.of g.of ≫ η.iso.hom.hom)).inv =
    (P.Γ f h).hom ≫
    (P.v (πₗ f.of h.of) ◁ (λ_ (P.u (πᵣ f.of h.of))).inv) ≫
    (P.v (πₗ f.of h.of) ◁ (P.ε (f ◁ η)).inv ▷ P.u (πᵣ f.of h.of)) ≫
    (α_ (P.v (πₗ f.of h.of)) (P.v (f.of ◁ η.iso.hom).hom ≫ P.u (f.of ◁ η.iso.hom).hom)
      (P.u (πᵣ f.of h.of))).inv ≫
    ((α_ (P.v (πₗ f.of h.of)) (P.v (f.of ◁ η.iso.hom).hom) (P.u (f.of ◁ η.iso.hom).hom)).inv ▷
      P.u (πᵣ f.of h.of)) ≫
    ((P.vComp' (f.of ◁ η.iso.hom).hom (πₗ f.of h.of) (πₗ f.of g.of)).inv ▷
        P.u (f.of ◁ η.iso.hom).hom ▷ P.u (πᵣ f.of h.of)) ≫
    (α_ (P.v (πₗ f.of g.of)) (P.u (f.of ◁ η.iso.hom).hom) (P.u (πᵣ f.of h.of))).hom ≫
    P.v (πₗ f.of g.of) ◁ (P.uComp' (f.of ◁ η.iso.hom).hom (πᵣ f.of h.of)
      (πᵣ f.of g.of ≫ η.iso.hom.hom)).inv := by
  have :=
    P.baseChange_change_pullback
      (t := πₗ f.of h.of)
      (l := πᵣ f.of h.of)
      (r := f.of.r)
      (b := h.of.l)
      (t' := πₗ f.of g.of)
      (l' := πᵣ f.of g.of ≫ η.iso.hom.hom)
      (e := Spans.apexIso (asIso <| f.of ◁ η.iso.hom))
      (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone ..)
      (isPullback_πₗ_πᵣ_comp_iso_hom ..)
      (by simp)
      (by simp)
  have γ₁ :=
    P.baseChangeIso_comp_vert'
      (u₀₁ :=  πₗ f.of g.of)
      (f₀₂ := πᵣ f.of g.of)
      (f₂₄ := η.iso.hom.hom)
      (f₀₄ := πᵣ f.of g.of ≫ η.iso.hom.hom)
      (f₁₃ := f.of.r)
      (f₃₅ := 𝟙 _)
      (f₁₅ := f.of.r)
      (u₂₃ := g.of.l)
      (u₄₅ := h.of.l)
      (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone ..)
      (IsPullback.of_vert_isIso .mk)
      (isPullback_πₗ_πᵣ_comp_iso_hom ..)
  have γ₂ :=
    P.baseChange_change_pullback
      (t := h.of.l)
      (l := 𝟙 _)
      (r := 𝟙 _)
      (b := h.of.l)
      (t' := g.of.l)
      (l' := η.iso.hom.hom)
      (e := Spans.apexIso η.iso)
      (IsPullback.of_vert_isIso .mk)
      (IsPullback.of_vert_isIso .mk)
      (by simp)
      (by simp)
  rw [γ₂] at γ₁
  rw [γ₁] at this
  dsimp at this
  clear γ₁ γ₂
  rw [← wl% wr% P.ε_inv_def, ← wl% wr% dsimp% P.ε_inv_def (η := (f ◁ η)), ← Γ, ← Γ] at this
  dsimp [bicategoricalComp] at this
  simp only [Category.id_comp, whiskerRight_comp, id_whiskerRight, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, pentagon_hom_inv_inv_inv_inv, whiskerLeft_comp] at this
  simp only [P.uComp'_id_l, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, comp_whiskerRight,
    whisker_assoc, triangle_assoc_comp_right_inv_assoc, P.baseChange_unit_left, whiskerLeft_comp,
    whiskerLeft_rightUnitor_inv, Category.assoc, Iso.trans_inv, whiskerLeftIso_inv, Iso.symm_inv,
    whiskerLeft_rightUnitor, Iso.inv_hom_id_assoc, whiskerLeft_inv_hom_whiskerRight_assoc,
    whiskerLeft_inv_hom_assoc] at this
  simp_rw [← whiskerLeft_comp_assoc (f := P.u f.of.r), ← associator_naturality_right_assoc,
    ← whisker_exchange_assoc, associator_inv_naturality_middle_assoc,
    ← whisker_exchange_assoc, ← associator_inv_naturality_right_assoc,
    ← reassoc_of% wl% leftUnitor_inv_naturality, whiskerLeft_inv_hom_assoc] at this
  simpa using this

set_option maxHeartbeats 300000 in -- rotate_isos is slow...
lemma map₂_whisker_left {a b c : EffBurnside C} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    P.map₂ (f ◁ η) = (P.mapComp f g).hom ≫ (P.map f ◁ P.map₂ η) ≫ (P.mapComp f h).inv := by
  dsimp [map₂, mapComp, bicategoricalIsoComp, bicategoricalComp]
  simp_rw [← P.ε_hom_def]
  simp only [comp_whiskerLeft, comp_whiskerRight, whiskerLeft_comp, Category.assoc,
    Iso.inv_hom_id_assoc, whiskerRight_comp, id_whiskerRight, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id]
  have := rotate_isos% 0 7 (dsimp% P.map₂_whisker_left_aux₁ f η)
  rotate_isos ← 5 0; rotate_isos 0 3
  rw [reassoc_of% wr% P.𝔯_whiskerLeft₁ f η, ← this,
    ← reassoc_of% wl% wr% dsimp% P.ε_hom_def (η := (f ◁ η))]
  clear this
  simp only [cat_nf]
  simp_rw [associator_naturality_left_assoc, ← whiskerLeft_comp_assoc (f := P.v (f.of ≫ h.of).l),
    whisker_exchange_assoc, cancelIso, whiskerLeft_comp_assoc, ← associator_naturality_right,
    ← whiskerLeft_comp_assoc, ← leftUnitor_naturality, ← whisker_exchange_assoc,
    ← associator_inv_naturality_right_assoc, inv_hom_whiskerRight_assoc, cancelIso,
    ← comp_whiskerRight_assoc, associator_inv_naturality_middle_assoc]
  simp only [whiskerLeft_comp, comp_whiskerRight, whisker_assoc, Category.assoc, whiskerRight_comp,
    comp_whiskerLeft, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
    pentagon_inv_hom_hom_hom_hom_assoc, leftUnitor_whiskerRight, pentagon_assoc,
    triangle_assoc_comp_right_inv_assoc, whiskerLeft_whiskerLeft_hom_inv_assoc, cancelIso,
    whiskerLeft_whiskerLeft_inv_hom]
  simp_rw [← whiskerLeft_comp (f := P.v f.of.l), reassoc_of% wl% pentagon_inv,
    ← reassoc_of% wl% associator_inv_naturality_left,
    reassoc_of% wl% associator_inv_naturality_right,
    reassoc_of% wl% whisker_exchange, cancelIso,
    pentagon_inv_assoc, ← associator_inv_naturality_left_assoc,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc, cancelIso]
  congr 2
  simp_rw [pentagon_inv_hom_hom_hom_inv_assoc, ← reassoc_of% wr% associator_inv_naturality_left,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    whisker_exchange_assoc, pentagon_hom_inv_inv_inv_hom_assoc, ← comp_whiskerRight_assoc,
    ← associator_naturality_left_assoc, comp_whiskerRight_assoc,
    ← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
    ← whiskerLeft_comp_assoc, ← whisker_exchange, ← associator_inv_naturality_right_assoc,
    whiskerLeft_comp_assoc, leftUnitor_comp, whiskerLeft_comp,
    whiskerRight_comp, whiskerLeft_comp_assoc, cancelIso,
    ← Category.assoc, cancel_mono, Category.assoc, cancel_epi,
    ← whiskerLeft_comp_assoc, 𝔩_whiskerLeft₁]
  have :=
    P.uComp'₀₂₃_hom
      (f₀₁ := πᵣ f.of g.of) (f₁₂ := η.iso.hom.hom) (f₂₃ := h.of.r)
      (f₀₂ := πᵣ f.of g.of ≫ η.iso.hom.hom) (f₁₃ := g.of.r) (f := (f.of ≫ g.of).r)
      (by simp) (by simp) (by simp)
  rotate_isos ← 2 0 at this
  rotate_isos ← 0 2 at this
  simp only [𝔩, comp_whiskerLeft, whiskerLeft_comp, Category.assoc, Iso.inv_hom_id_assoc, inv%this,
    comp_whiskerRight, whisker_assoc, pentagon_inv, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, whiskerLeft_whiskerLeft_hom_inv_assoc, cancelIso,
    cancel_epi]
  bicategory

end whiskerLeft

section whiskerRight

set_option maxHeartbeats 300000 in -- rotate_isos is slow...
lemma map₂_whisker_right_aux {a b c : EffBurnside C} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (P.Γ g h).inv =
    (P.v (πₗ g.of h.of) ◁ (λ_ (P.u (πᵣ g.of h.of))).inv) ≫
      (P.v (πₗ g.of h.of) ◁ (P.ε (η ▷ h)).inv ▷ P.u (πᵣ g.of h.of)) ≫
      (α_ (P.v (πₗ g.of h.of))
          (P.v (η.iso.hom ▷ h.of).hom ≫ P.u (η.iso.hom ▷ h.of).hom) (P.u (πᵣ g.of h.of))).inv ≫
      ((α_ (P.v (πₗ g.of h.of)) (P.v (η.iso.hom ▷ h.of).hom) (P.u (η.iso.hom ▷ h.of).hom)).inv ▷
        P.u (πᵣ g.of h.of)) ≫
      ((P.vComp' (η.iso.hom ▷ h.of).hom (πₗ g.of h.of) (πₗ f.of h.of ≫ η.iso.hom.hom)).inv ▷
          P.u (η.iso.hom ▷ h.of).hom ▷
            P.u (πᵣ g.of h.of)) ≫
      (α_ (P.v (πₗ f.of h.of ≫ η.iso.hom.hom))
        (P.u (η.iso.hom ▷ h.of).hom) (P.u (πᵣ g.of h.of))).hom ≫
      (P.v (πₗ f.of h.of ≫ η.iso.hom.hom) ◁
        (P.uComp' (η.iso.hom ▷ h.of).hom (πᵣ g.of h.of) (πᵣ f.of h.of)).inv) ≫
      ((P.vComp' (πₗ f.of h.of) η.iso.hom.hom (πₗ f.of h.of ≫ η.iso.hom.hom)).hom ▷
        P.u (πᵣ f.of h.of)) ≫
      (α_ (P.v η.iso.hom.hom) (P.v (πₗ f.of h.of)) (P.u (πᵣ f.of h.of))).hom ≫
      (P.v η.iso.hom.hom ◁ (P.Γ f h).inv) ≫
      (P.v η.iso.hom.hom ◁ (P.uComp' η.iso.hom.hom g.of.r f.of.r).hom ▷ P.v h.of.l) ≫
      (α_ (P.v η.iso.hom.hom) (P.u η.iso.hom.hom ≫ P.u g.of.r) (P.v h.of.l)).inv ≫
      ((α_ (P.v η.iso.hom.hom) (P.u η.iso.hom.hom) (P.u g.of.r)).inv ▷ P.v h.of.l) ≫
      ((P.ε η).hom ▷ P.u g.of.r ▷ P.v h.of.l) ≫
      (α_ (𝟙 (P.obj g.of.apex)) (P.u g.of.r) (P.v h.of.l)).hom ≫
      (λ_ (P.u g.of.r ≫ P.v h.of.l)).hom := by
  have :=
    P.baseChange_change_pullback
      (t := πₗ g.of h.of)
      (l := πᵣ g.of h.of)
      (r := g.of.r)
      (b := h.of.l)
      (t' := πₗ f.of h.of ≫ η.iso.hom.hom)
      (l' := πᵣ f.of h.of)
      (e := Spans.apexIso (asIso <| η.iso.hom ▷ h.of))
      (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone ..)
      (isPullback_πₗ_comp_iso_hom_πᵣ ..)
      (by simp)
      (by simp)
  have γ₁ :=
    P.baseChangeIso_comp_horiz'
      (f₀₁ := πₗ f.of h.of) (f₁₂ := η.iso.hom.hom) (f₀₂ := πₗ f.of h.of ≫ η.iso.hom.hom)
      (f₃₄ := h.of.l) (f₄₅ := 𝟙 _) (f₃₅ := h.of.l)
      (g₀ := πᵣ f.of h.of) (g₁ := f.of.r) (g₂ := g.of.r)
      (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone ..)
      (IsPullback.of_horiz_isIso .mk)
      (isPullback_πₗ_comp_iso_hom_πᵣ ..)
  have γ₂ :=
    P.baseChange_change_pullback
      (t := 𝟙 g.of.apex)
      (l := g.of.r)
      (r := g.of.r)
      (b := 𝟙 _)
      (t' := η.iso.hom.hom)
      (l' := f.of.r)
      (e := Spans.apexIso η.iso)
      (IsPullback.of_horiz_isIso .mk)
      (IsPullback.of_horiz_isIso .mk)
      (by simp)
      (by simp)
  rw [γ₂] at γ₁
  rw [γ₁] at this
  dsimp [bicategoricalComp] at this
  simp only [P.vComp'_id_l, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, whiskerLeft_comp,
    P.baseChange_unit_right, Category.id_comp, whiskerRight_comp, id_whiskerRight, Iso.inv_hom_id,
    Category.comp_id, Category.assoc, pentagon_hom_inv_inv_inv_inv, Iso.trans_inv,
    whiskerRightIso_inv, Iso.symm_inv, comp_whiskerRight, leftUnitor_whiskerRight, whisker_assoc,
    leftUnitor_inv_whiskerRight, Iso.inv_hom_id_assoc, triangle_assoc_comp_right_assoc,
    whiskerLeft_inv_hom_whiskerRight_assoc, whiskerLeft_inv_hom_assoc] at this
  clear γ₁ γ₂
  rw [← Γ, ← Γ, ← reassoc_of% wl% wr% wr% P.ε_inv_def,
    ← reassoc_of% wl% wr% dsimp% P.ε_inv_def (η := η ▷ h)] at this
  simp_rw [leftUnitor_comp, comp_whiskerRight, Category.assoc, cancelIso,
    associator_naturality_left_assoc, ← whiskerLeft_comp_assoc, ← whisker_exchange_assoc,
    id_whiskerLeft, Category.assoc] at this
  simp only [whiskerRight_comp, comp_whiskerRight, Category.assoc, leftUnitor_whiskerRight,
    whiskerLeft_comp, Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc,
    hom_inv_whiskerRight_whiskerRight_assoc, cancelIso, inv_hom_whiskerRight_whiskerRight_assoc,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc] at this
  -- rotate_isos 2 0 at this
  rotate_isos ← 1 0 at this
  rotate_isos ← 0 9 at this
  exact this

set_option maxHeartbeats 300000 in -- rotate_isos is slow...
lemma map₂_whisker_right {a b c : EffBurnside C} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    P.map₂ (η ▷ h) = (P.mapComp f h).hom ≫ (P.map₂ η ▷ P.map h) ≫ (P.mapComp g h).inv := by
  dsimp [map₂, mapComp, bicategoricalIsoComp, mapId, map]
  simp_rw [← P.ε_hom_def, ← dsimp% P.ε_hom_def (η := η ▷ h)]
  simp only [comp_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc, whiskerRight_comp,
    id_whiskerRight, Category.id_comp, Iso.inv_hom_id, Category.comp_id, comp_whiskerRight,
    whisker_assoc, whiskerLeft_comp, leftUnitor_whiskerRight, pentagon_assoc,
    pentagon_inv_inv_hom_hom_inv, whiskerLeft_hom_inv_assoc, pentagon_hom_inv_inv_inv_inv_assoc]
  simp_rw [associator_inv_naturality_right_assoc, whisker_exchange]
  rotate_isos 0 1
  rotate_isos ← 1 0
  dsimp [𝔩, 𝔯]
  simp_rw [← whiskerLeft_comp, ← leftUnitor_naturality, ← whisker_exchange_assoc,
    whiskerLeft_comp]
  simp only [comp_whiskerLeft, whiskerLeft_comp, whiskerRight_comp, Category.assoc,
    whiskerLeft_inv_hom_assoc, inv%(P.map₂_whisker_right_aux η h), Pith.comp_of,
    Pith.whiskerRight_iso_hom, comp_whiskerRight, leftUnitor_inv_whiskerRight, whisker_assoc,
    leftUnitor_whiskerRight, Iso.inv_hom_id_assoc, pentagon_hom_inv_inv_inv_inv_assoc,
    pentagon_inv_assoc, whiskerLeft_hom_inv_assoc, whiskerLeft_hom_inv_whiskerRight_assoc,
    cancelIso, whiskerLeft_inv_hom_whiskerRight_assoc]
  have Δ₁ := P.vComp'₀₂₃_hom
    (f₀₁ := (η.iso.hom ▷ h.of).hom)
    (f₁₂ := πₗ g.of h.of)
    (f₀₂ := πₗ f.of h.of ≫ η.iso.hom.hom)
    (f₂₃ := g.of.l)
    (f₁₃ := (g.of ≫ h.of).l)
    (f := (f.of ≫ h.of).l)
    (by simp) (by simp) (by simp)
  have Δ₂ := P.vComp'₀₁₃_hom
    (f₀₁ := πₗ f.of h.of) (f₁₂ := η.iso.hom.hom) (f₀₂ := πₗ f.of h.of ≫ η.iso.hom.hom)
    (f₂₃ := g.of.l) (f₁₃ := f.of.l) (f := (f.of ≫ h.of).l)
    (by simp) (by simp) (by simp)
  simp_rw [Δ₁, Category.assoc] at Δ₂
  simp_rw [inv% Δ₂, comp_whiskerRight, Category.assoc, cancelIso, ← whiskerLeft_comp_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc, whiskerLeft_comp_assoc]
  clear Δ₁ Δ₂
  simp only [whisker_assoc, comp_whiskerLeft, whiskerRight_comp, whiskerRight_id, comp_whiskerRight,
    Category.assoc, triangle, Iso.hom_inv_id_assoc, inv_hom_whiskerRight_whiskerRight_assoc,
    Iso.inv_hom_id_assoc, pentagon_inv_hom_hom_hom_hom_assoc, whiskerLeft_comp,
    whiskerLeft_hom_inv_assoc, whiskerLeft_hom_inv_whiskerRight_assoc]
  simp_rw [reassoc_of% wr% associator_naturality_left, associator_naturality_left_assoc,
    ← associator_naturality_right_assoc, ← whisker_exchange_assoc, cancelIso,
    whisker_exchange_assoc, associator_naturality_right_assoc, whisker_exchange_assoc]
  simp only [whiskerRight_comp, comp_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, cancel_epi]
  simp_rw [← Category.assoc, cancel_mono, Category.assoc]
  slice_lhs 11 16 => equals (⊗𝟙).hom => bicategory
  slice_rhs 19 22 => equals (⊗𝟙).hom => bicategory
  simp_rw [← Category.assoc, cancel_mono, Category.assoc]
  rotate_isos 2 0
  simp only [pentagon_inv_hom_hom_hom_hom_assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp,
    cancelIso]
  congr 1
  simp_rw [← whiskerLeft_comp_assoc (f := P.v η.iso.hom.hom),
    ← whiskerLeft_comp (f := P.v (πₗ f.of h.of)),
    associator_inv_naturality_right_assoc, ← reassoc_of% wr% associator_inv_naturality_left,
    ← associator_inv_naturality_left_assoc, whisker_exchange_assoc]
  -- simp? [cancel_epi]
  simp only [comp_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp,
    Iso.hom_inv_id_assoc, cancel_epi]
  have Δ₁ := P.uComp'₀₂₃_hom
    (f₀₁ := (η.iso.hom ▷ h.of).hom) (f₁₂ := πᵣ g.of h.of) (f₀₂ := πᵣ f.of h.of)
    (f₂₃ := h.of.r) (f := (f.of ≫ h.of).r) (f₁₃ := (g.of ≫ h.of).r)
    (by simp) (by simp) (by simp)
  simp only [Δ₁, whiskerLeft_comp, Category.assoc, cancelIso]
  bicategory

end whiskerRight

section left_unitor

lemma map₂_left_unitor {a b : EffBurnside C} (f : a ⟶ b) :
    P.map₂ (λ_ f).hom =
    (P.mapComp (𝟙 a) f).hom ≫ ((P.mapId a).hom ▷ P.map f) ≫ (λ_ (P.map f)).hom := by
  dsimp [map₂, mapComp, bicategoricalIsoComp, mapId, map]
  simp only [comp_whiskerLeft, comp_whiskerRight, whiskerLeft_comp, Category.assoc,
    Iso.inv_hom_id_assoc, whiskerRight_comp, id_whiskerRight, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id, pentagon_hom_inv_inv_inv_inv_assoc]
  have := P.baseChange_change_pullback
    (t := f.of.l) (l := 𝟙 f.of.apex) (r := 𝟙 _) (b := f.of.l)
    (t' := πₗ (𝟙 a.as) f.of) (l' := πᵣ (𝟙 a.as) f.of) (e := (Spans.apexIso (λ_ f.of)))
    (.of_vert_isIso .mk)
    (.of_vert_isIso (.mk (by simpa using (Spans.comp_comm (𝟙 a.as) f.of))))
    (by simpa using (Spans.comp_comm (𝟙 a.as) f.of).symm) (by simp)
  simp only [bicategoricalComp, BicategoricalCoherence.whiskerLeft_iso,
    BicategoricalCoherence.left'_iso, BicategoricalCoherence.refl_iso, Iso.refl_trans,
    whiskerLeftIso_hom, Iso.symm_hom, apexIso_hom, leftUnitor_hom_hom,
    BicategoricalCoherence.assoc'_iso, BicategoricalCoherence.assoc_iso,
    BicategoricalCoherence.whiskerRight_iso, Iso.trans_assoc, Iso.trans_hom, whiskerRightIso_hom,
    Iso.refl_hom, whiskerRight_comp, id_whiskerRight, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id, pentagon_hom_inv_inv_inv_inv, Category.assoc] at this
  simp only [Γ, Pith.id_of, id_apex, id_r, inv%this, comp_whiskerRight, whisker_assoc,
    leftUnitor_whiskerRight, whiskerLeft_comp, Category.assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_inv_hom_assoc]
  clear this
  rw [← reassoc_of% wl% wr% dsimp% P.ε_hom_def (η := (λ_ f).hom)]
  simp_rw [← whiskerLeft_comp_assoc]
  rw [← reassoc_of% wr% wr% dsimp% P.ε_hom_def (η := (λ_ f).hom)]
  simp only [whiskerLeft_comp, Category.assoc, inv%P.baseChange_unit_left, comp_whiskerRight,
    whisker_assoc, leftUnitor_inv_whiskerRight, triangle_assoc_comp_right_assoc,
    Iso.inv_hom_id_assoc, leftUnitor_whiskerRight, inv_hom_whiskerRight_assoc, cancelIso,
    whiskerLeft_inv_hom_assoc]
  simp only [𝔯, Pith.id_of, id_apex, id_l]
  have := P.vComp'₀₁₃_hom
    (f₀₁ := πᵣ (𝟙 a.as) f.of)
    (f₁₂ := f.of.l)
    (f₂₃ := 𝟙 _)
    (f := (𝟙 a.as ≫ f.of).l)
    (f₀₂ := πₗ (𝟙 a.as) f.of)
    (f₁₃ := f.of.l)
    (by simpa using (Spans.comp_comm (𝟙 a.as) f.of).symm) (by simp)
    (by simpa using (Spans.comp_comm (𝟙 a.as) f.of).symm)
  simp only [this, comp_whiskerRight, whisker_assoc, Category.assoc, cancel_epi]
  clear this
  simp_rw [← whiskerLeft_comp_assoc,
    ← reassoc_of% wr% associator_inv_naturality_left, ← associator_inv_naturality_left_assoc,
    whisker_exchange_assoc, whiskerLeft_comp_assoc, cancel_epi]
  rotate_isos 3 0
  simp only [P.vComp'_id_l, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, comp_whiskerRight,
    leftUnitor_inv_whiskerRight, Category.assoc, comp_whiskerLeft, whiskerLeft_comp,
    whiskerRight_comp, Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc, whiskerLeft_inv_hom_assoc,
    pentagon_assoc]
  simp_rw [← whiskerLeft_comp_assoc, associator_naturality_left_assoc, ← whisker_exchange_assoc,
    id_whiskerLeft_assoc]
  simp only [whiskerLeft_comp, Category.assoc, whiskerRight_comp, Iso.hom_inv_id_assoc,
    pentagon_inv_hom_hom_hom_hom_assoc, id_whiskerLeft, Iso.inv_hom_id_assoc, cancel_epi]
  simp only [Ψ_inv_eq', comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc, cancelIso,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc, inv_hom_whiskerRight_whiskerRight_assoc,
    Iso.inv_hom_id, Category.comp_id]
  simp_rw [← whiskerLeft_comp_assoc, leftUnitor_comp_assoc, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight, ← leftUnitor_naturality, ← whisker_exchange_assoc, cat_nf, unitors_equal,
    cancelIso, ← Category.assoc, cancel_mono, Category.assoc, ← whiskerLeft_comp_assoc,
    ← whiskerLeft_comp, 𝔩]
  simp only [whiskerLeft_comp, Pith.id_of, P.uComp'_id_l, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, comp_whiskerRight, whisker_assoc, triangle_assoc_comp_right_inv_assoc,
    Category.assoc, pentagon_inv, pentagon_assoc, triangle_assoc_comp_right, comp_whiskerLeft,
    Iso.inv_hom_id_assoc, cancel_epi]
  slice_rhs 3 10 => equals 𝟙 _ => bicategory
  simp


end left_unitor

section right_unitor

lemma map₂_right_unitor {a b : EffBurnside C} (f : a ⟶ b) :
  P.map₂ (ρ_ f).hom =
  (P.mapComp f (𝟙 b)).hom ≫ (P.map f ◁ (P.mapId b).hom) ≫ (ρ_ (P.map f)).hom := by
  dsimp [map₂, mapComp, bicategoricalIsoComp, mapId, map, Γ]
  simp only [comp_whiskerLeft, comp_whiskerRight, whiskerLeft_comp, Category.assoc,
    Iso.inv_hom_id_assoc, whiskerRight_comp, id_whiskerRight, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id]
  have := P.baseChange_change_pullback
    (l := f.of.r) (t := 𝟙 f.of.apex) (r := f.of.r) (b := 𝟙 _)
    (t' := πₗ f.of (𝟙 b.as)) (l' := πᵣ f.of (𝟙 b.as) ) (e := (Spans.apexIso (ρ_ f.of)))
    (.of_horiz_isIso .mk)
    (.of_horiz_isIso .mk)
    (by simp) (by simp)
  simp only [bicategoricalComp, P.baseChange_unit_right, BicategoricalCoherence.whiskerLeft_iso,
    BicategoricalCoherence.left'_iso, BicategoricalCoherence.refl_iso, Iso.refl_trans,
    whiskerLeftIso_hom, Iso.symm_hom, apexIso_hom, rightUnitor_hom_hom,
    BicategoricalCoherence.assoc'_iso, BicategoricalCoherence.assoc_iso,
    BicategoricalCoherence.whiskerRight_iso, Iso.trans_assoc, Iso.trans_hom, whiskerRightIso_hom,
    Iso.refl_hom, whiskerRight_comp, id_whiskerRight, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id, pentagon_hom_inv_inv_inv_inv, Category.assoc] at this
  simp only [inv%this, comp_whiskerRight, whisker_assoc, leftUnitor_whiskerRight, whiskerLeft_comp,
    Category.assoc, triangle_assoc_comp_right_inv_assoc, Iso.inv_hom_id_assoc,
    inv%P.baseChange_unit_left, whiskerLeft_rightUnitor, whiskerLeft_inv_hom_assoc]
  clear this
  rw [← reassoc_of% wl% wr% dsimp% P.ε_hom_def (η := (ρ_ f).hom)]
  simp_rw [← whiskerLeft_comp_assoc,
    ← reassoc_of% wr% wr% dsimp% P.ε_hom_def (η := (ρ_ f).hom), whiskerLeft_comp_assoc,
    ← reassoc_of% wl% associator_inv_naturality_left,
    ← whiskerLeft_comp_assoc, whisker_exchange_assoc, id_whiskerLeft, whiskerLeft_comp_assoc,
    cancelIso, ← whiskerLeft_comp_assoc, ← whisker_exchange, ← leftUnitor_inv_naturality_assoc,
    leftUnitor_comp_assoc, cancelIso, ← whisker_exchange_assoc]
  simp only [whiskerLeft_comp, Category.assoc, whiskerRight_comp, comp_whiskerRight,
    unitors_inv_equal, whiskerRight_id, Iso.inv_hom_id_assoc, comp_whiskerLeft, id_whiskerLeft,
    whiskerLeft_rightUnitor_inv, leftUnitor_whiskerRight, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc, hom_inv_whiskerRight_whiskerRight_assoc]
  simp_rw [leftUnitor_comp, whiskerLeft_comp, comp_whiskerRight, whiskerLeft_comp,
    Category.assoc, cancelIso, ← whiskerLeft_comp_assoc, ← pentagon_hom_inv_inv_inv_inv_assoc,
    ← associator_inv_naturality_left_assoc, whisker_exchange_assoc, whiskerLeft_comp_assoc,
    ← associator_naturality_middle_assoc, ← comp_whiskerRight_assoc, 𝔯, P.vComp'_id_l]
  dsimp
  simp_rw [whiskerLeft_comp_assoc, cancelIso, Category.comp_id, cancel_epi,
    ← whiskerLeft_comp_assoc,]
  dsimp [𝔩]
  have := P.uComp'₀₂₃_hom
    (f₀₁ := πₗ f.of (𝟙 b.as)) (f₁₂ := f.of.r) (f₂₃ := 𝟙 b.as.of) (f₀₂ := πᵣ f.of (𝟙 b.as))
    (f := (f.of ≫ 𝟙 _).r) (f₁₃ := f.of.r)
    (by simp)
    (by simp)
    (by simp)
  -- simp? [this, cancel_epi, P.uComp'_id_l]
  simp only [whiskerLeft_comp, Category.assoc, this, P.uComp'_id_l, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerLeft_rightUnitor_inv, inv_hom_whiskerRight_assoc,
    Iso.inv_hom_id_assoc, whiskerLeft_whiskerLeft_inv_hom_assoc, whiskerRight_comp,
    leftUnitor_whiskerRight, cancel_epi]
  clear this
  rotate_isos ← 2 0
  simp_rw [rightUnitor_comp_assoc, Iso.inv_hom_id_assoc, rightUnitor_comp, cancelIso,
    ← whiskerLeft_comp]
  congr 1
  simp_rw [leftUnitor_comp_assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    ← whisker_exchange_assoc, whiskerRight_id_assoc, Iso.inv_hom_id, Category.comp_id,
    ← Category.assoc, cancel_mono, Category.assoc]
  simp [P.Ψ_inv_eq']

end right_unitor

/-- Assembling the data in a `PseudoFunctorCore C B` into a pseudofunctor `EffBurnside C ⥤ᵖ B`. -/
@[expose, simps]
public noncomputable def toPseudofunctor :
    EffBurnside C ⥤ᵖ B where
  obj x := P.obj' x
  map {x y} S := P.map S
  map₂ {x y} {S S'} η := P.map₂ η
  mapId x := P.mapId x
  mapComp {x y z} S₁ S₂ := P.mapComp S₁ S₂
  map₂_id := P.map₂_id
  map₂_comp := by
    intros c c' f g h η θ
    exact P.map₂_comp ..
  map₂_whisker_left := by
    intros a b c f g h η
    exact P.map₂_whisker_left ..
  map₂_whisker_right := by
    intros a b c f g η h
    exact P.map₂_whisker_right ..
  map₂_associator := by
    intros a b c d f g h
    exact P.map₂_assoc f g h
  map₂_left_unitor := by
    intros a b f
    exact P.map₂_left_unitor ..
  map₂_right_unitor := by
    intros a b f
    exact P.map₂_right_unitor ..

end toPseudoFunctor

end PseudoFunctorCore

end CategoryTheory.EffBurnside
