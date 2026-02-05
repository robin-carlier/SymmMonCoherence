/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

import all SymmMonCoherence.Spans.PseudoFromBurnside.Basic
public import SymmMonCoherence.Spans.PseudoFromBurnside.Basic
public import Mathlib.Tactic.CategoryTheory.BicategoricalComp

/-! # Pseudofunctors from the Burnside (2,1)-category . -/

-- @[expose] public section

namespace CategoryTheory.EffBurnside.PseudoFunctorCore

open CategoryTheory Bicategory

universe w₁ v₁ v₂ u₁ u₂

variable {C : Type v₁} [Category.{u₁} C] {B : Type u₂} [Bicategory.{w₁, v₂} B]
    (P : PseudoFunctorCore C B)

noncomputable section toPseudoFunctor

variable [Limits.HasPullbacks C]

open Spans

section comp_assoc


/- The field map₂_assoc for the pseudofunctor is the most technical to supply.
This amounts to a very big bicategorical computation, which we break down in several lemmas
computing or simplifying some subterms fo the final expression. Even with such sublemmas,
the computation remains painful as we cannot use placeholders in chains of bicategorical
compositions, and we can’t directly perform rewrites, because nothing
can actually be proved about `bicategoricalComp`. -/

section

variable {a b c d : EffBurnside C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)

abbrev lα₁ :=
  P.lComp'
    (α_ f.of g.of h.of).hom.hom
    (f.of ≫ g.of ≫ h.of).r
    ((f.of ≫ g.of) ≫ h.of).r

abbrev rα₁ := P.rComp'
    (α_ f.of g.of h.of).hom.hom
    (f.of ≫ g.of ≫ h.of).l
    ((f.of ≫ g.of) ≫ h.of).l

abbrev lα₂ :=
  P.lComp'
    ((α_ f.of g.of h.of).hom.hom ≫ πᵣ f.of (g.of ≫ h.of))
    (πᵣ g.of h.of)
    (πᵣ (f.of ≫ g.of) h.of)

abbrev rα₂ :=
  P.rComp'
    ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of)
    (πₗ f.of g.of)
    (πₗ f.of (g.of ≫ h.of))

abbrev rα₃ :=
  (P.rComp'
    ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of)
    (f.of ≫ g.of).l
    (f.of ≫ g.of ≫ h.of).l)

abbrev lα₂' :=
  P.lComp'
    (πᵣ f.of (g.of ≫ h.of))
    (πᵣ g.of h.of)
    ((α_ f.of g.of h.of).inv.hom ≫ πᵣ (f.of ≫ g.of) h.of)

abbrev rα₁' :=
  (P.rComp'
    ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of)
    (f.of ≫ g.of).l
    (f.of ≫ g.of ≫ h.of).l)

abbrev lα₃ :=
  P.lComp'
    ((α_ f.of g.of h.of).inv.hom ≫ πᵣ (f.of ≫ g.of) h.of)
    h.of.r
    (f.of ≫ g.of ≫ h.of).r

abbrev lα₄ :=
  P.lComp'
    (α_ f.of g.of h.of).hom.hom
    (πᵣ f.of (g.of ≫ h.of))
    ((α_ f.of g.of h.of).hom.hom ≫ πᵣ f.of (g.of ≫ h.of))

abbrev rα₄ :=
  P.rComp'
    (α_ f.of g.of h.of).hom.hom
    ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of)
    (πₗ (f.of ≫ g.of) h.of)

abbrev η :=
   (P.baseChangeIso
     (α_ f.of g.of h.of).hom.hom (α_ f.of g.of h.of).hom.hom
     (𝟙 (f.of ≫ g.of ≫ h.of).apex) (𝟙 (f.of ≫ g.of ≫ h.of).apex)
     (IsPullback.of_horiz_isIso .mk)).inv ≫ (P.Ψ (f.of ≫ g.of ≫ h.of).apex).inv

lemma isPullback_Θ₁ :
    IsPullback ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) (πᵣ f.of (g.of ≫ h.of))
      (πᵣ f.of g.of) (πₗ g.of h.of) := by
  rw [(IsPullback.paste_horiz_iff
    (h₁₁ := (α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of)
    (h₁₂ := πₗ f.of g.of)
    (h₂₁ := πₗ g.of h.of)
    (h₂₂ := g.of.l)
    (v₁₁ := πᵣ f.of (g.of ≫ h.of))
    (v₁₂ := πᵣ f.of g.of)
    (v₁₃ := f.of.r)
    (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone f.of g.of)
    (by simp)).symm]
  simpa using (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone f.of (g.of ≫ h.of))

lemma isPullback_Θ₂ :
    IsPullback (πₗ (f.of ≫ g.of) h.of) ((α_ f.of g.of h.of).hom.hom ≫ πᵣ f.of (g.of ≫ h.of))
      (πᵣ f.of g.of) (πₗ g.of h.of) := by
  rw [(IsPullback.paste_vert_iff
      (h₁₁ := πₗ (f.of ≫ g.of) h.of) (h₂₁ := πₗ g.of h.of)
      (h₃₁ := h.of.l)
      (v₁₁ := (α_ f.of g.of h.of).hom.hom ≫ πᵣ f.of (g.of ≫ h.of))
      (v₂₁ := πᵣ g.of h.of)
      (v₁₂ := πᵣ f.of g.of)
      (v₂₂ := g.of.r)
      (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone g.of h.of)
      (by simp)).symm]
  simpa using (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone (f.of ≫ g.of) h.of)

abbrev Θ₁ :=
  P.baseChangeIso
    ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) (πᵣ f.of (g.of ≫ h.of))
    (πᵣ f.of g.of) (πₗ g.of h.of) (isPullback_Θ₁ f g h)

abbrev Θ₂ :=
  P.baseChangeIso
    (πₗ (f.of ≫ g.of) h.of) ((α_ f.of g.of h.of).hom.hom ≫ πᵣ f.of (g.of ≫ h.of))
    (πᵣ f.of g.of) (πₗ g.of h.of) (isPullback_Θ₂ f g h)
end

-- syntax (name := bcomp2) (priority := high) term:81
--   ppSpace ppRealGroup("⊚≫" ppHardSpace ppDedent(term:80)) : term
-- macro_rules (kind := bcomp2) | `($a ⊚≫ $b) => `(bicategoricalComp $a $b)
-- @[app_unexpander _root_.CategoryTheory.bicategoricalComp] public meta def unexpandBComp :
--       Lean.PrettyPrinter.Unexpander
--   | `($_ $a $b) => `($a ⊚≫ $b)
--   | _ => throw ()
-- #check bicategoricalComp

lemma assoc₀ {a b c d : EffBurnside C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (P.rα₃ f g h).hom ≫ (P.𝔯 f g).hom ▷
      P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ⊗≫
       (P.r f.of.l ◁ (P.rα₂ f g h).inv ≫ (P.𝔯 f (g ≫ h)).inv) = 𝟙 _ := by
  dsimp [rα₃, bicategoricalComp, 𝔯, rα₂]
  simp [P.rComp'₀₁₃_hom
    (f₀₁ := ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of))
    (f₁₂ := πₗ f.of g.of)
    (f₂₃ := f.of.l)
    (f₀₂ := πₗ f.of (g.of ≫ h.of))
    (f₁₃ := (f.of ≫ g.of).l)
    (f := (f.of ≫ g.of ≫ h.of).l)
    (by simp) (by simp) (by simp)]

lemma assoc₁ {a b c d : EffBurnside C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  (P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₃ f g h).hom) ⊗≫
    (P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₂' f g h).hom ▷ P.l h.of.r) ⊗≫
    (P.r (f.of ≫ g.of ≫ h.of).l ◁ P.l (πᵣ f.of (g.of ≫ h.of)) ◁ (P.𝔩 g h).inv) ⊗≫
    P.r (f.of ≫ (g ≫ h).of).l ◁ (P.𝔩 f (g ≫ h)).inv = 𝟙 _ := by
  dsimp [lα₃, lα₂', 𝔩, bicategoricalComp]
  have := P.lComp'₀₂₃_hom
    (f₀₁ := πᵣ f.of (g.of ≫ h.of))
    (f₁₂ := πᵣ g.of h.of)
    (f₂₃ := h.of.r)
    (f₀₂ := (α_ f.of g.of h.of).inv.hom ≫ πᵣ (f.of ≫ g.of) h.of)
    (f₁₃ := (g.of ≫ h.of).r)
    (f := (f.of ≫ g.of ≫ h.of).r)
    (by simp) (by simp) (by simp)
  simp [this]

lemma assoc₂ {a b c d : EffBurnside C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (P.𝔯 (f ≫ g) h).hom ⊗≫ P.r (f.of ≫ g.of).l ◁ (P.rα₄ f g h).hom ⊗≫
      (P.rα₃ f g h).inv ▷ P.r (α_ f.of g.of h.of).hom.hom = (P.rα₁ f g h).hom := by
  dsimp [rα₃, bicategoricalComp, 𝔯, rα₄, rα₁]
  simp [P.rComp'₀₁₃_hom
    (f₀₁ := (α_ f.of g.of h.of).hom.hom)
    (f₁₂ := (α_ f.of g.of h.of).inv.hom ≫ (πₗ (f.of ≫ g.of) h.of))
    (f₂₃ := (f.of ≫ g.of).l)
    (f₀₂ := πₗ (f.of ≫ g.of) h.of)
    (f₁₃ := (f.of ≫ g.of ≫ h.of).l)
    (f := ((f.of ≫ g.of) ≫ h.of).l)
    (by simp) (by simp) (by simp)]

-- #exit
set_option maxHeartbeats 500000 in -- Calc + bicategory is so slow
lemma aux₀ {a b c d : EffBurnside C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    P.r (f.of ≫ g.of).l ◁
      P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
        P.η f g h ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r =
    𝟙 _ ⊗≫ P.r (f.of ≫ g.of).l ◁ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
      P.r (α_ f.of g.of h.of).hom.hom ◁
        P.l (α_ f.of g.of h.of).hom.hom ◁ (P.lα₂' f g h).inv ▷ P.l h.of.r ⊗≫
    P.r (f.of ≫ g.of).l ◁ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
      P.r (α_ f.of g.of h.of).hom.hom ◁ P.l (α_ f.of g.of h.of).hom.hom ◁ (P.lα₃ f g h).inv ⊗≫
    (P.rα₃ f g h).inv ▷ P.r (α_ f.of g.of h.of).hom.hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷
      P.l (f.of ≫ g.of ≫ h.of).r ⊗≫
    P.r (f.of ≫ g.of ≫ h.of).l ◁ P.η f g h ▷ P.l (f.of ≫ g.of ≫ h.of).r ⊗≫
    P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₃ f g h).hom ⊗≫
    P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₂' f g h).hom ▷ P.l h.of.r ⊗≫
    (P.rα₃ f g h).hom ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫ 𝟙 _ := by
  symm
  calc
    _ = 𝟙 _ ⊗≫ P.r (f.of ≫ g.of).l ◁ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
        P.r (α_ f.of g.of h.of).hom.hom ◁ P.l (α_ f.of g.of h.of).hom.hom ◁
          (P.lα₂' f g h).inv ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
          P.r (α_ f.of g.of h.of).hom.hom ◁ P.l (α_ f.of g.of h.of).hom.hom ◁ (P.lα₃ f g h).inv ⊗≫
        (P.rα₃ f g h).inv ▷ P.r (α_ f.of g.of h.of).hom.hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷
          P.l (f.of ≫ g.of ≫ h.of).r ⊗≫
        P.r (f.of ≫ g.of ≫ h.of).l ◁ P.η f g h ▷ P.l (f.of ≫ g.of ≫ h.of).r ⊗≫
        P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₃ f g h).hom ⊗≫
        P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₂' f g h).hom ▷ P.l h.of.r ⊗≫
        (P.rα₃ f g h).hom ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷
          P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫ 𝟙 _ := rfl
    _ = 𝟙 _ ⊗≫
        (((P.rα₃ f g h).inv ▷ (P.r (α_ f.of g.of h.of).hom.hom ≫ P.l (α_ f.of g.of h.of).hom.hom ≫
          (P.l (πᵣ f.of (g.of ≫ h.of)) ≫ P.l (πᵣ g.of h.of)) ≫ P.l h.of.r)) ≫
          P.r (f.of ≫ g.of ≫ h.of).l ◁ P.r (α_ f.of g.of h.of).hom.hom ◁
            P.l (α_ f.of g.of h.of).hom.hom ◁
          ((P.lα₂' f g h).inv ▷ P.l h.of.r ≫ (P.lα₃ f g h).inv)) ⊗≫
          ((P.r (f.of ≫ g.of ≫ h.of).l ≫ P.r (α_ f.of g.of h.of).hom.hom ≫
              P.l (α_ f.of g.of h.of).hom.hom) ◁
                ((P.lα₃ f g h).hom ≫ (P.lα₂' f g h).hom ▷ P.l h.of.r) ≫
          (P.r (f.of ≫ g.of ≫ h.of).l ◁ P.η f g h ≫ (ρ_ _).hom) ▷
            ((P.l (πᵣ f.of (g.of ≫ h.of)) ≫ P.l (πᵣ g.of h.of)) ≫ P.l h.of.r)) ⊗≫
          (P.rα₃ f g h).hom ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷
            P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange,
          whisker_exchange (θ := ((P.lα₃ f g h).hom ≫ (P.lα₂' f g h).hom ▷ P.l h.of.r))]
        bicategory
    _ = 𝟙 _ ⊗≫
          ((P.rα₃ f g h).inv ▷ (P.r (α_ f.of g.of h.of).hom.hom ≫ P.l (α_ f.of g.of h.of).hom.hom ≫
            (P.l (πᵣ f.of (g.of ≫ h.of)) ≫ P.l (πᵣ g.of h.of)) ≫ P.l h.of.r)) ⊗≫
          P.r (f.of ≫ g.of ≫ h.of).l ◁ P.r (α_ f.of g.of h.of).hom.hom ◁
            P.l (α_ f.of g.of h.of).hom.hom ◁
          ((P.lα₂' f g h).inv ▷ P.l h.of.r ≫ (P.lα₃ f g h).inv ≫
            (P.lα₃ f g h).hom ≫ (P.lα₂' f g h).hom ▷ P.l h.of.r) ⊗≫
          (P.r (f.of ≫ g.of ≫ h.of).l ◁ P.η f g h) ▷
            ((P.l (πᵣ f.of (g.of ≫ h.of)) ≫ P.l (πᵣ g.of h.of)) ≫ P.l h.of.r) ⊗≫
          (P.rα₃ f g h).hom ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷
            P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫
        ((P.rα₃ f g h).inv ▷ ((P.r (α_ f.of g.of h.of).hom.hom ≫ P.l (α_ f.of g.of h.of).hom.hom) ≫
          (P.l (πᵣ f.of (g.of ≫ h.of)) ≫ P.l (πᵣ g.of h.of)) ≫ P.l h.of.r) ≫
        P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.η f g h ▷
          ((P.l (πᵣ f.of (g.of ≫ h.of)) ≫ P.l (πᵣ g.of h.of)) ≫ P.l h.of.r))) ⊗≫
        (P.rα₃ f g h).hom ▷
          (𝟙 _ ≫ (P.l (πᵣ f.of (g.of ≫ h.of)) ≫ P.l (πᵣ g.of h.of)) ≫ P.l h.of.r) ⊗≫ 𝟙 _ := by
      simp only [cancelIso]
      bicategory
    _ = P.r (f.of ≫ g.of).l ◁
            P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
              P.η f g h ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        ((P.rα₃ f g h).inv ▷
          (𝟙 _ ≫ (P.l (πᵣ f.of (g.of ≫ h.of)) ≫ P.l (πᵣ g.of h.of)) ≫ P.l h.of.r) ≫
        (P.rα₃ f g h).hom ▷
          (𝟙 _ ≫ (P.l (πᵣ f.of (g.of ≫ h.of)) ≫ P.l (πᵣ g.of h.of)) ≫ P.l h.of.r)) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
      bicategory
    _ = P.r (f.of ≫ g.of).l ◁
          P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
            P.η f g h ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r := by
      simp only [cancelIso]
      bicategory

/- Auxiliary computation for map₂_assoc -/
lemma cocycle₁ {a b c d : EffBurnside C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    P.r (f.of ≫ g.of).l ◁ P.l (πᵣ f.of g.of) ◁ (P.Γ g h).inv ⊗≫
      (P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ▷ P.l g.of.r ▷ P.r h.of.l ⊗≫
      P.r f.of.l ◁ (P.Γ f g).inv ▷ P.l g.of.r ▷ P.r h.of.l ⊗≫
      P.r f.of.l ◁ P.l f.of.r ◁ P.r g.of.l ◁ (P.Γ g h).hom =
    𝟙 _ ⊗≫ (P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of) ⊗≫
      (P.r f.of.l ◁ (P.Γ f g).inv ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of)) ⊗≫ 𝟙 _ := by
  calc
    _ = P.r (f.of ≫ g.of).l ◁ P.l (πᵣ f.of g.of) ◁ (P.Γ g h).inv ⊗≫
          (P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ▷ P.l g.of.r ▷ P.r h.of.l ⊗≫
          P.r f.of.l ◁ (P.Γ f g).inv ▷ P.l g.of.r ▷ P.r h.of.l ⊗≫
          P.r f.of.l ◁ P.l f.of.r ◁ P.r g.of.l ◁ (P.Γ g h).hom := rfl
    _ = 𝟙 _  ⊗≫ ((P.r (f.of ≫ g.of).l ≫ P.l (πᵣ f.of g.of)) ◁ (P.Γ g h).inv ≫
          ((𝟙 _ ⊗≫ (P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ⊗≫ P.r f.of.l ◁ (P.Γ f g).inv) ▷
          (P.l g.of.r ≫ P.r h.of.l))) ⊗≫
          P.r f.of.l ◁ P.l f.of.r ◁ P.r g.of.l ◁ (P.Γ g h).hom := by bicategory
    _ = 𝟙 _ ⊗≫
          ((P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ⊗≫
            P.r f.of.l ◁ (P.Γ f g).inv) ▷ (P.r (πₗ g.of h.of) ≫ P.l (πᵣ g.of h.of)) ⊗≫
          P.r f.of.l ◁ P.l f.of.r ◁ P.r g.of.l ◁ (P.Γ g h).inv ≫
          P.r f.of.l ◁ P.l f.of.r ◁ P.r g.of.l ◁ (P.Γ g h).hom := by
      rw [whisker_exchange]
      bicategory
    _ = 𝟙 _ ⊗≫ (P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of) ⊗≫
          (P.r f.of.l ◁ (P.Γ f g).inv ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of)) ⊗≫ 𝟙 _ := by
      simp only [cancelIso]
      bicategory

set_option maxHeartbeats 400000 in -- bicategory computations are slow
lemma comp₁ {a b c d : EffBurnside C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (P.μ (f ≫ g) h).hom ⊗≫
      P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
      P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₄ f g h).hom ▷
        P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
      P.r (f.of ≫ g.of).l ◁ (P.rα₄ f g h).hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷
        P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
      P.r (f.of ≫ g.of).l ◁ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
      P.r (α_ f.of g.of h.of).hom.hom ◁ P.l (α_ f.of g.of h.of).hom.hom ◁
        (P.lα₂' f g h).inv ▷ P.l h.of.r ⊗≫
      P.r (f.of ≫ g.of).l ◁ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
        P.r (α_ f.of g.of h.of).hom.hom ◁ P.l (α_ f.of g.of h.of).hom.hom ◁ (P.lα₃ f g h).inv ⊗≫
      (P.rα₃ f g h).inv ▷ P.r (α_ f.of g.of h.of).hom.hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷
        P.l (f.of ≫ g.of ≫ h.of).r =
    P.r ((f.of ≫ g.of) ≫ h.of).l ◁ (P.lα₁ f g h).hom ⊗≫
      (P.rα₁ f g h).hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷ P.l (f.of ≫ g.of ≫ h.of).r := by
  rw [P.μ_hom]
  conv_lhs =>
    equals
      ((P.𝔯 (f ≫ g) h).hom ▷ P.l ((f ≫ g).of ≫ h.of).r ≫
        (P.r (f ≫ g).of.l ≫ P.r (πₗ (f ≫ g).of h.of)) ◁
          ((P.𝔩 (f ≫ g) h).hom ≫ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
            (P.lα₄ f g h).hom ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r)) ⊗≫
        P.r (f.of ≫ g.of).l ◁ (P.rα₄ f g h).hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷
          P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        ((P.r (f.of ≫ g.of).l ≫ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of)) ◁
          (P.r (α_ f.of g.of h.of).hom.hom ◁ P.l (α_ f.of g.of h.of).hom.hom ◁
            (P.lα₂' f g h).inv ▷ P.l h.of.r ⊗≫
          P.r (α_ f.of g.of h.of).hom.hom ◁ P.l (α_ f.of g.of h.of).hom.hom ◁ (P.lα₃ f g h).inv) ≫
        (P.rα₃ f g h).inv ▷ _) ⊗≫ 𝟙 _ => bicategory
  rw [← whisker_exchange, whisker_exchange
    (f := (P.r (f.of ≫ g.of).l ≫ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of)))]
  conv_lhs =>
    equals
      P.r ((f ≫ g).of ≫ h.of).l ◁
        ((P.𝔩 (f ≫ g) h).hom ≫ ((P.lα₂ f g h).hom ▷ P.l h.of.r) ⊗≫
          (P.lα₄ f g h).hom ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r) ⊗≫
        ((P.𝔯 (f ≫ g) h).hom ⊗≫ P.r (f.of ≫ g.of).l ◁ (P.rα₄ f g h).hom ⊗≫
            (P.rα₃ f g h).inv ▷ P.r (α_ f.of g.of h.of).hom.hom) ▷
           P.l (α_ f.of g.of h.of).hom.hom ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷
            P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of ≫ h.of).l ◁
          ((P.r (α_ f.of g.of h.of).hom.hom ◁ P.l (α_ f.of g.of h.of).hom.hom ◁
              (P.lα₂' f g h).inv ▷ P.l h.of.r) ⊗≫
            P.r (α_ f.of g.of h.of).hom.hom ◁
              P.l (α_ f.of g.of h.of).hom.hom ◁ (P.lα₃ f g h).inv) ⊗≫
        𝟙 _ => bicategory
  conv_lhs =>
    equals
      (P.r ((f ≫ g).of ≫ h.of).l ◁
        ((P.𝔩 (f ≫ g) h).hom ≫ ((P.lα₂ f g h).hom ▷ P.l h.of.r) ⊗≫
          (P.lα₄ f g h).hom ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r) ≫
        (P.rα₁ f g h).hom ▷ _) ⊗≫
        P.r (f.of ≫ g.of ≫ h.of).l ◁
          ((P.r (α_ f.of g.of h.of).hom.hom ◁ P.l (α_ f.of g.of h.of).hom.hom ◁
              (P.lα₂' f g h).inv ▷ P.l h.of.r) ⊗≫
            P.r (α_ f.of g.of h.of).hom.hom ◁
              P.l (α_ f.of g.of h.of).hom.hom ◁ (P.lα₃ f g h).inv) ⊗≫
        𝟙 _ => rw [assoc₂]; bicategory
  rw [whisker_exchange]
  conv_rhs => equals
    (((P.rα₁ f g h).hom ▷ P.l ((f ≫ g).of ≫ h.of).r) ≫ _ ◁ (P.lα₁ f g h).hom) ⊗≫ 𝟙 _ =>
    rw [← whisker_exchange]
    bicategory
  simp only [bicategoricalComp, Pith.comp_of, BicategoricalCoherence.assoc_iso,
    BicategoricalCoherence.assoc'_iso, BicategoricalCoherence.whiskerRight_iso,
    BicategoricalCoherence.refl_iso, Iso.trans_hom, whiskerRightIso_hom, Iso.refl_hom,
    whiskerRight_comp, id_whiskerRight, Category.id_comp, Iso.inv_hom_id, Iso.symm_hom,
    Iso.hom_inv_id, whiskerLeft_comp, comp_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
    BicategoricalCoherence.whiskerLeft_iso, whiskerLeftIso_hom, pentagon_hom_hom_inv_hom_hom,
    Iso.trans_assoc, Category.comp_id, Iso.hom_inv_id_assoc, cancel_epi]
  simp_rw [← Category.assoc, cancel_mono, Category.assoc, ← whiskerLeft_comp]
  congr 2
  dsimp [𝔩, lα₂, lα₄, lα₁, lα₂', lα₃]
  have := P.lComp'₀₂₃_hom
    (f₀₁ := πᵣ f.of (g.of ≫ h.of))
    (f₁₂ := πᵣ g.of h.of)
    (f₂₃ := h.of.r)
    (f₀₂ := (α_ f.of g.of h.of).inv.hom ≫ πᵣ (f.of ≫ g.of) h.of)
    (f₁₃ := (g.of ≫ h.of).r)
    (f := (f.of ≫ g.of ≫ h.of).r)
    (by simp) (by simp) (by simp)
  simp only [inv%this, inv_hom_whiskerRight_assoc, whiskerLeft_comp, pentagon_assoc]
  have e₂ := P.lComp'₀₁₃_hom
    (f₀₁ := (α_ f.of g.of h.of).hom.hom )
    (f₁₂ := πᵣ f.of (g.of ≫ h.of))
    (f₂₃ := (g.of ≫ h.of).r)
    (f₀₂ := (α_ f.of g.of h.of).hom.hom ≫ πᵣ f.of (g.of ≫ h.of))
    (f₁₃ := (f.of ≫ g.of ≫ h.of).r)
    (f := ((f.of ≫ g.of) ≫ h.of).r)
    (by simp) (by simp) (by simp)
  have e₃ := P.lComp'₀₁₃_hom
    (f₀₁ := (α_ f.of g.of h.of).hom.hom ≫ πᵣ f.of (g.of ≫ h.of))
    (f₁₂ := πᵣ g.of h.of)
    (f₂₃ := h.of.r)
    (f₀₂ := πᵣ (f.of ≫ g.of) h.of)
    (f₁₃ := (g.of ≫ h.of).r)
    (f := ((f.of ≫ g.of) ≫ h.of).r)
    (by simp) (by simp) (by simp)
  simp only [e₂, e₃, Category.assoc, cancel_epi]
  simp_rw [associator_naturality_left_assoc, cancel_epi, ← Category.assoc, cancel_mono,
    Category.assoc, whisker_exchange_assoc, cancel_epi]
  bicategory

lemma comp₂ {a b c d : EffBurnside C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₃ f g h).hom ⊗≫
        P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₂' f g h).hom ▷ P.l h.of.r ⊗≫
        (P.rα₃ f g h).hom ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
          ((P.𝔯 f g).hom ▷ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ▷
          P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁
          P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
            P.l (πᵣ f.of (g.of ≫ h.of)) ◁ (P.𝔩 g h).inv ⊗≫
        P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷
          P.l (g.of ≫ h.of).r ⊗≫ (P.μ f (g ≫ h)).inv) = (⊗𝟙).hom := by
  rw [P.μ_inv']
  conv_lhs =>
    equals
      P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₃ f g h).hom ⊗≫
        P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₂' f g h).hom ▷ P.l h.of.r ⊗≫
        (((P.rα₃ f g h).hom ≫ (P.𝔯 f g).hom ▷
          P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of)) ▷
            (P.l (πᵣ f.of (g.of ≫ h.of)) ≫ P.l (πᵣ g.of h.of) ≫ P.l h.of.r) ≫
        ((P.r f.of.l ≫ P.r (πₗ f.of g.of)) ≫
          P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of)) ◁
            P.l (πᵣ f.of (g.of ≫ h.of)) ◁ (P.𝔩 g h).inv) ⊗≫
        (P.r f.of.l ◁ (P.rα₂ f g h).inv ≫ (P.𝔯 f (g ≫ h)).inv) ▷
          (P.l (πᵣ f.of (g.of ≫ h.of)) ≫ P.l (g.of ≫ h.of).r) ⊗≫
        P.r (f.of ≫ (g ≫ h).of).l ◁ (P.𝔩 f (g ≫ h)).inv => dsimp; bicategory
  rw [← whisker_exchange]
  conv_lhs =>
    equals
      (P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₃ f g h).hom)
        ⊗≫ (P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₂' f g h).hom ▷ P.l h.of.r)
        ⊗≫ P.r (f.of ≫ g.of ≫ h.of).l ◁ P.l (πᵣ f.of (g.of ≫ h.of)) ◁ (P.𝔩 g h).inv
        ⊗≫ ((P.rα₃ f g h).hom ≫ (P.𝔯 f g).hom ▷
              P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ⊗≫
               (P.r f.of.l ◁ (P.rα₂ f g h).inv ≫ (P.𝔯 f (g ≫ h)).inv)) ▷
            (P.l (πᵣ f.of (g.of ≫ h.of)) ≫ P.l (g.of ≫ h.of).r)
        ⊗≫ P.r (f.of ≫ (g ≫ h).of).l ◁ (P.𝔩 f (g ≫ h)).inv => bicategory
  conv_lhs =>
    equals
      (P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₃ f g h).hom) ⊗≫
        (P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₂' f g h).hom ▷ P.l h.of.r) ⊗≫
        (P.r (f.of ≫ g.of ≫ h.of).l ◁ P.l (πᵣ f.of (g.of ≫ h.of)) ◁ (P.𝔩 g h).inv) ⊗≫
        P.r (f.of ≫ (g ≫ h).of).l ◁ (P.𝔩 f (g ≫ h)).inv =>
    rw [assoc₀, id_whiskerRight]
    bicategory
  rw [assoc₁]
  simp


/- Auxiliary computation for map₂_assoc -/

set_option maxHeartbeats 2000000 in -- Bicategory computations are slow.
lemma cocycle₂ {a b c d : EffBurnside C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (P.μ (f ≫ g) h).hom ⊗≫
      P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
      P.r (f.of ≫ g.of).l ◁ (P.Θ₂ f g h).inv ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
      (P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of) ▷
        P.l h.of.r ⊗≫
      P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ P.l (πᵣ f.of g.of) ◁ P.r (πₗ g.of h.of) ◁ (P.𝔩 g h).inv ⊗≫
      P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ (P.Θ₁ f g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
      P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (g.of ≫ h.of).r ⊗≫
      (P.μ f (g ≫ h)).inv =
    (P.r ((f.of ≫ g.of) ≫ h.of).l ◁ (P.lα₁ f g h).hom) ⊗≫
      (P.rα₁ f g h).hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷ P.l (f.of ≫ g.of ≫ h.of).r ⊗≫
      (P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.η f g h) ▷ P.l (f.of ≫ g.of ≫ h.of).r) ⊗≫ 𝟙 _ := by
  conv_lhs =>
    equals
      (P.μ (f ≫ g) h).hom ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₄ f g h).hom ▷
          P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ (P.rα₄ f g h).hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷
          P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
          (P.η f g h) ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ (P.Θ₁ f g h).inv ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        (P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ P.l (πᵣ f.of g.of) ◁ P.r (πₗ g.of h.of) ◁ (P.𝔩 g h).inv ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ (P.Θ₁ f g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
        P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷
          P.l (g.of ≫ h.of).r ⊗≫ (P.μ f (g ≫ h)).inv =>
    have :
        (P.Θ₂ f g h).inv =
        𝟙 _ ⊗≫
          P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₄ f g h).hom ⊗≫ (P.rComp' (α_ f.of g.of h.of).hom.hom
              ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) (πₗ (f.of ≫ g.of) h.of)).hom ▷
            P.l (α_ f.of g.of h.of).hom.hom ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ⊗≫
          P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
            (P.η f g h) ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ⊗≫ (P.Θ₁ f g h).inv := by
      have := P.baseChange_change_pullback
          ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) (πᵣ f.of (g.of ≫ h.of))
          (πᵣ f.of g.of) (πₗ g.of h.of)
          (πₗ (f.of ≫ g.of) h.of) ((α_ f.of g.of h.of).hom.hom ≫ πᵣ f.of (g.of ≫ h.of))
          (Spans.apexIso (α_ f.of g.of h.of)) (isPullback_Θ₁ f g h) (isPullback_Θ₂ f g h)
          (by simp) (by simp)
      dsimp [bicategoricalComp, η] at this ⊢
      simp only [Category.assoc] at this ⊢
      replace this := inv% this
      simp [this]
    dsimp [η]
    rw [this]
    bicategory
  conv_lhs =>
    equals
      (P.μ (f ≫ g) h).hom ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁
          (P.lα₄ f g h).hom ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ (P.rα₄ f g h).hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷
          P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
          (P.η f g h) ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        ((P.𝔯 f g).hom ▷ _ ≫ _ ◁ (P.Θ₁ f g h).inv) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ ((P.Θ₁ f g h).hom ▷ _ ≫ _ ◁ (P.𝔩 g h).inv) ⊗≫
        P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷
          P.l (g.of ≫ h.of).r ⊗≫ (P.μ f (g ≫ h)).inv =>
    rw [← whisker_exchange (η := (P.𝔯 f g).hom) (θ := (P.Θ₁ f g h).inv),
        ← whisker_exchange (η := (P.Θ₁ f g h).hom) (θ := (P.𝔩 g h).inv)]
    dsimp; bicategory
  conv_lhs =>
    equals
      (P.μ (f ≫ g) h).hom ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₄ f g h).hom ▷
          P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ (P.rα₄ f g h).hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷
          P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
          (P.η f g h) ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        (P.𝔯 f g).hom ▷ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ▷
          P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ ((P.Θ₁ f g h).inv ≫ (P.Θ₁ f g h).hom) ▷
          P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁
          P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
            P.l (πᵣ f.of (g.of ≫ h.of)) ◁ (P.𝔩 g h).inv ⊗≫
        P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷
          P.l (g.of ≫ h.of).r ⊗≫ (P.μ f (g ≫ h)).inv => dsimp; bicategory
  conv_lhs =>
    equals
      ((P.μ (f ≫ g) h).hom ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₄ f g h).hom ▷
          P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ (P.rα₄ f g h).hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷
          P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r) ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
          P.η f g h ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        ((P.𝔯 f g).hom ▷ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ▷
          P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁
          P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
            P.l (πᵣ f.of (g.of ≫ h.of)) ◁ (P.𝔩 g h).inv ⊗≫
        P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷
          P.l (g.of ≫ h.of).r ⊗≫ (P.μ f (g ≫ h)).inv) => rw [Iso.inv_hom_id]; dsimp; bicategory
  conv_lhs =>
    equals
      ((P.μ (f ≫ g) h).hom ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₄ f g h).hom ▷
          P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ (P.rα₄ f g h).hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷
          P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
        P.r (α_ f.of g.of h.of).hom.hom ◁ P.l (α_ f.of g.of h.of).hom.hom ◁
          (P.lα₂' f g h).inv ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
          P.r (α_ f.of g.of h.of).hom.hom ◁ P.l (α_ f.of g.of h.of).hom.hom ◁ (P.lα₃ f g h).inv ⊗≫
        (P.rα₃ f g h).inv ▷ P.r (α_ f.of g.of h.of).hom.hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷
          P.l (f.of ≫ g.of ≫ h.of).r) ⊗≫
        P.r (f.of ≫ g.of ≫ h.of).l ◁ P.η f g h ▷ P.l (f.of ≫ g.of ≫ h.of).r ⊗≫
        (P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₃ f g h).hom ⊗≫
        P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.lα₂' f g h).hom ▷ P.l h.of.r ⊗≫
        (P.rα₃ f g h).hom ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
          ((P.𝔯 f g).hom ▷ P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ▷
          P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁
          P.r ((α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of) ◁
            P.l (πᵣ f.of (g.of ≫ h.of)) ◁ (P.𝔩 g h).inv ⊗≫
        P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷
          P.l (g.of ≫ h.of).r ⊗≫ (P.μ f (g ≫ h)).inv)) => rw [aux₀]; dsimp; bicategory
  rw [P.comp₁ f g h, P.comp₂ f g h]
  bicategory

lemma aux₂ {a b c d : EffBurnside C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    P.r f.of.l ◁ (P.Γ f g).inv ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
      P.r f.of.l ◁ P.l f.of.r ◁ (P.μ g h).inv ⊗≫
      P.r f.of.l ◁ P.l f.of.r ◁ (P.𝔯 g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
      P.r f.of.l ◁ (P.Γ f g).hom ▷ P.r (πₗ g.of h.of) ▷ P.l (g.of ≫ h.of).r =
    𝟙 _ ⊗≫ (P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁
      P.l (πᵣ f.of g.of) ◁ P.r (πₗ g.of h.of) ◁ (P.𝔩 g h).inv) ⊗≫ 𝟙 _ := by
  conv_lhs =>
    equals
      P.r f.of.l ◁ (P.Γ f g).inv ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        (P.r f.of.l ◁ P.l f.of.r ◁ ((P.μ g h).inv ≫ (P.𝔯 g h).hom ▷ P.l (g.of ≫ h.of).r)) ⊗≫
        P.r f.of.l ◁ (P.Γ f g).hom ▷ P.r (πₗ g.of h.of) ▷ P.l (g.of ≫ h.of).r => dsimp; bicategory
  have : (P.μ g h).inv ≫ (P.𝔯 g h).hom ▷ P.l (g.of ≫ h.of).r = _ ◁ (P.𝔩 g h).inv := by
    simp
  rw [this]
  conv_lhs =>
    equals
      P.r f.of.l ◁ (P.Γ f g).inv ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.l f.of.r ◁ P.r g.of.l ◁ P.r (πₗ g.of h.of) ◁ (P.𝔩 g h).inv ⊗≫
        P.r f.of.l ◁ (P.Γ f g).hom ▷ P.r (πₗ g.of h.of) ▷ P.l (g.of ≫ h.of).r => bicategory
  conv_lhs =>
    equals
      𝟙 _ ⊗≫ ((P.r f.of.l ◁ (P.Γ f g).inv ▷ P.r (πₗ g.of h.of)) ▷ _ ≫
        _ ◁ (P.𝔩 g h).inv) ⊗≫
        P.r f.of.l ◁ (P.Γ f g).hom ▷ P.r (πₗ g.of h.of) ▷ P.l (g.of ≫ h.of).r => bicategory
  rw [← whisker_exchange]
  conv_lhs =>
    equals
    𝟙 _ ⊗≫
      P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ P.l (πᵣ f.of g.of) ◁ P.r (πₗ g.of h.of) ◁ (P.𝔩 g h).inv ⊗≫
      (P.r f.of.l ◁ (P.Γ f g).inv ▷ P.r (πₗ g.of h.of) ▷ P.l (g.of ≫ h.of).r ≫
        P.r f.of.l ◁ (P.Γ f g).hom ▷ P.r (πₗ g.of h.of) ▷ P.l (g.of ≫ h.of).r) ⊗≫ 𝟙 _ => bicategory
  simp only [cancelIso]
  bicategory

-- #exit
set_option maxHeartbeats 800000 in -- calc + bicat is very slow
/-- Associativity is by far the most technical point -/
public lemma map₂_assoc
    {a b c d : EffBurnside C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    P.map₂ (α_ f g h).hom =
    (P.mapComp (f ≫ g) h).hom ≫
      ((P.mapComp f g).hom ▷ P.map h) ≫
      (α_ (P.map f) (P.map g) (P.map h)).hom ≫
      (P.map f ◁ (P.mapComp g h).inv) ≫ (P.mapComp f (g ≫ h)).inv := by
  dsimp [map, map₂]
  simp_rw [mapComp_hom, mapComp_inv, ← whisker_exchange_assoc]
  dsimp [bicategoricalComp]
  simp only [cat_nf, cancelIso]
  have vcomp₁ : (P.Γ (f ≫ g) h).hom = _ := P.baseChangeIso_comp_vert'
    (u₀₁ := πₗ (f.of ≫ g.of) h.of)
    (f₀₂ := (α_ f.of g.of h.of).hom.hom ≫ πᵣ f.of (g.of ≫ h.of))
    (f₁₃ := πᵣ f.of g.of)
    (u₂₃ := πₗ g.of h.of) (f₃₅ := g.of.r)
    (f₂₄ := πᵣ g.of h.of)
    (u₄₅ := h.of.l) (f₁₅ := (f.of ≫ g.of).r)
    (f₀₄ := πᵣ _ _)
    (isPullback_Θ₂ f g h)
    (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone _ _)
    (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone _ _)
  have hcomp₂ : (P.Γ f (g ≫ h)).hom = _ := P.baseChangeIso_comp_horiz'
    (f₀₁ := (α_ f.of g.of h.of).inv.hom ≫ πₗ (f.of ≫ g.of) h.of)
    (f₁₂ := πₗ f.of g.of)
    (f₀₂ := πₗ _ _)
    (f₃₄ := πₗ g.of h.of)
    (f₄₅ := g.of.l)
    (f₃₅ := (g.of ≫ h.of).l)
    (g₀ := πᵣ _ _)
    (g₁ := πᵣ _ _)
    (g₂ := f.of.r)
    (isPullback_Θ₁ f g h)
    (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone _ _)
    (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone _ _)
  rw [← Γ] at vcomp₁ hcomp₂
  simp_rw [hcomp₂, inv% vcomp₁, cat_nf, whisker_assoc, cat_nf, cancelIso]
  suffices H :
    (P.r ((f.of ≫ g.of) ≫ h.of).l ◁ (P.lα₁ f g h).hom) ⊗≫
      (P.rα₁ f g h).hom ▷ P.l (α_ f.of g.of h.of).hom.hom ▷ P.l (f.of ≫ g.of ≫ h.of).r ⊗≫
      P.r (f.of ≫ g.of ≫ h.of).l ◁ (P.η f g h) ▷ P.l (f.of ≫ g.of ≫ h.of).r ⊗≫ 𝟙 _ =
    (P.μ (f ≫ g) h).hom ⊗≫
      P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
      P.r (f.of ≫ g.of).l ◁ (P.Θ₂ f g h).inv ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
      P.r (f.of ≫ g.of).l ◁ P.l (πᵣ f.of g.of) ◁ (P.Γ g h).inv ▷ P.l h.of.r ⊗≫
      P.r (f.of ≫ g.of).l ◁ (P.𝔩 f g).inv ▷ P.r h.of.l ▷ P.l h.of.r ⊗≫
      (P.μ f g).hom ▷ P.r h.of.l ▷ P.l h.of.r ⊗≫
      P.r f.of.l ◁ (P.Γ f g).inv ▷ P.l g.of.r ▷ P.r h.of.l ▷ P.l h.of.r ⊗≫
      P.r f.of.l ◁ P.l f.of.r ◁ P.r g.of.l ◁ (P.Γ g h).hom ▷ P.l h.of.r ⊗≫
      P.r f.of.l ◁ P.l f.of.r ◁ (P.μ g h).inv ⊗≫
      P.r f.of.l ◁ P.l f.of.r ◁ (P.𝔯 g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
      P.r f.of.l ◁ (P.Γ f g).hom ▷ P.r (πₗ g.of h.of) ▷ P.l (g.of ≫ h.of).r ⊗≫
      P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ (P.Θ₁ f g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
      P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (g.of ≫ h.of).r ⊗≫
      (P.μ f (g ≫ h)).inv by
    convert H <;> (dsimp; bicategory)
  symm
  conv_lhs =>
    equals
      (P.μ (f ≫ g) h).hom ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ (P.Θ₂ f g h).inv ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.l (πᵣ f.of g.of) ◁ (P.Γ g h).inv ▷ P.l h.of.r ⊗≫
        (P.r (f.of ≫ g.of).l ◁ (P.𝔩 f g).inv ⊗≫ (P.μ f g).hom) ▷ P.r h.of.l ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ (P.Γ f g).inv ▷ P.l g.of.r ▷ P.r h.of.l ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.l f.of.r ◁ P.r g.of.l ◁ (P.Γ g h).hom ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.l f.of.r ◁ (P.μ g h).inv ⊗≫
        P.r f.of.l ◁ P.l f.of.r ◁ (P.𝔯 g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
        P.r f.of.l ◁ (P.Γ f g).hom ▷ P.r (πₗ g.of h.of) ▷ P.l (g.of ≫ h.of).r ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ (P.Θ₁ f g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
        P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (g.of ≫ h.of).r ⊗≫
        (P.μ f (g ≫ h)).inv => dsimp; bicategory
  conv_lhs =>
    equals
      (P.μ (f ≫ g) h).hom ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ (P.Θ₂ f g h).inv ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.l (πᵣ f.of g.of) ◁ (P.Γ g h).inv ▷ P.l h.of.r ⊗≫
        (P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ▷ P.l g.of.r ▷ P.r h.of.l ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ (P.Γ f g).inv ▷ P.l g.of.r ▷ P.r h.of.l ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.l f.of.r ◁ P.r g.of.l ◁ (P.Γ g h).hom ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.l f.of.r ◁ (P.μ g h).inv ⊗≫
        P.r f.of.l ◁ P.l f.of.r ◁ (P.𝔯 g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
        P.r f.of.l ◁ (P.Γ f g).hom ▷ P.r (πₗ g.of h.of) ▷ P.l (g.of ≫ h.of).r ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ (P.Θ₁ f g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
        P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (g.of ≫ h.of).r ⊗≫
        (P.μ f (g ≫ h)).inv =>
    suffices H : 𝟙 _ ⊗≫ (P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ▷ P.l g.of.r ⊗≫ 𝟙 _ =
      (P.r (f.of ≫ g.of).l ◁ (P.𝔩 f g).inv ⊗≫ (P.μ f g).hom) by rw [← H]; dsimp; bicategory
    dsimp [bicategoricalComp, μ]
    simp only [cat_nf, cancelIso, whisker_exchange_assoc]
  conv_lhs =>
    equals
      (P.μ (f ≫ g) h).hom ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ (P.Θ₂ f g h).inv ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        (𝟙 (P.r (f.of ≫ g.of).l ≫ P.l (πᵣ f.of g.of) ≫ P.r (πₗ g.of h.of) ≫ P.l (πᵣ g.of h.of)) ⊗≫
          (P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of) ⊗≫
          (P.r f.of.l ◁ (P.Γ f g).inv ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of)) ⊗≫
          𝟙 (P.r f.of.l ≫ P.l f.of.r ≫ P.r g.of.l ≫ P.r (πₗ g.of h.of) ≫ P.l (πᵣ g.of h.of))) ▷
            P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.l f.of.r ◁ (P.μ g h).inv ⊗≫
        P.r f.of.l ◁ P.l f.of.r ◁ (P.𝔯 g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
        P.r f.of.l ◁ (P.Γ f g).hom ▷ P.r (πₗ g.of h.of) ▷ P.l (g.of ≫ h.of).r ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ (P.Θ₁ f g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
        P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (g.of ≫ h.of).r ⊗≫
        (P.μ f (g ≫ h)).inv =>
    rw [← cocycle₁]; dsimp; bicategory
  conv_lhs =>
    equals
      (P.μ (f ≫ g) h).hom ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ (P.Θ₂ f g h).inv ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        (P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of) ▷
          P.l h.of.r ⊗≫
        (P.r f.of.l ◁ (P.Γ f g).inv ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
          P.r f.of.l ◁ P.l f.of.r ◁ (P.μ g h).inv ⊗≫
          P.r f.of.l ◁ P.l f.of.r ◁ (P.𝔯 g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
          P.r f.of.l ◁ (P.Γ f g).hom ▷ P.r (πₗ g.of h.of) ▷ P.l (g.of ≫ h.of).r) ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ (P.Θ₁ f g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
        P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (g.of ≫ h.of).r ⊗≫
        (P.μ f (g ≫ h)).inv => dsimp; bicategory
  conv_lhs =>
    equals
      (P.μ (f ≫ g) h).hom ⊗≫
        P.r (f.of ≫ g.of).l ◁ P.r (πₗ (f.of ≫ g.of) h.of) ◁ (P.lα₂ f g h).hom ▷ P.l h.of.r ⊗≫
        P.r (f.of ≫ g.of).l ◁ (P.Θ₂ f g h).inv ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        (P.𝔯 f g).hom ▷ P.l (πᵣ f.of g.of) ▷ P.r (πₗ g.of h.of) ▷ P.l (πᵣ g.of h.of) ▷ P.l h.of.r ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ P.l (πᵣ f.of g.of) ◁ P.r (πₗ g.of h.of) ◁ (P.𝔩 g h).inv ⊗≫
        P.r f.of.l ◁ P.r (πₗ f.of g.of) ◁ (P.Θ₁ f g h).hom ▷ P.l (g.of ≫ h.of).r ⊗≫
        P.r f.of.l ◁ (P.rα₂ f g h).inv ▷ P.l (πᵣ f.of (g.of ≫ h.of)) ▷ P.l (g.of ≫ h.of).r ⊗≫
        (P.μ f (g ≫ h)).inv => rw [aux₂]; dsimp; bicategory
  rw [P.cocycle₂ f g h]

end comp_assoc
end toPseudoFunctor

end PseudoFunctorCore

end CategoryTheory.EffBurnside
