module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
public import SymmMonCoherence.ForMathlib.CategoryTheory.Bicategory.Adjunction.Pseudofunctor
public import SymmMonCoherence.ForMathlib.Tactic.CategoryTheory.CancelIso
public import SymmMonCoherence.ForMathlib.Tactic.CategoryTheory.RotateIso
public import SymmMonCoherence.ForMathlib.Tactic.CategoryTheory.BicategoryElaborators
public import SymmMonCoherence.ForMathlib.Tactic.CategoryTheory.CatNFElaborator
public import SymmMonCoherence.ForMathlib.Tactic.DsimpPercent

universe w₁ w₂ v₁ v₂ u₁ u₂

@[expose] public section

attribute [push]
  CategoryTheory.Bicategory.inv_whiskerLeft
  CategoryTheory.Bicategory.inv_whiskerRight
  CategoryTheory.IsIso.inv_comp
  CategoryTheory.IsIso.inv_inv
  CategoryTheory.IsIso.Iso.inv_inv
  CategoryTheory.IsIso.Iso.inv_hom
  CategoryTheory.NatIso.inv_inv_app
  -- CategoryTheory.MonoidalCategory.inv_whiskerLeft
  -- CategoryTheory.MonoidalCategory.inv_whiskerRight
  -- CategoryTheory.MonoidalCategory.inv_tensor

attribute [push ←]
  CategoryTheory.Functor.map_inv
  CategoryTheory.NatIso.isIso_inv_app
  CategoryTheory.op_inv
  CategoryTheory.unop_inv
  CategoryTheory.PrelaxFunctor.map₂_inv

attribute [cat_nf]
  -- CategoryTheory.PrelaxFunctor.map₂_inv
  CategoryTheory.PrelaxFunctor.map₂_comp
  -- CategoryTheory.Bicategory.inv_whiskerLeft
  -- CategoryTheory.Bicategory.inv_whiskerRight
  CategoryTheory.Bicategory.comp_whiskerLeft
  CategoryTheory.Bicategory.whiskerLeft_comp
  CategoryTheory.Bicategory.comp_whiskerRight
  CategoryTheory.Bicategory.whiskerRight_comp
  CategoryTheory.Bicategory.id_whiskerRight
  CategoryTheory.Bicategory.whiskerRight_id
  CategoryTheory.Bicategory.id_whiskerLeft
  CategoryTheory.Bicategory.whiskerLeft_id


open CategoryTheory in
@[push]
theorem _root_.CategoryTheory.NatIso.inv_hom_app {C : Type*} [Category* C] {D : Type*} [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) (X : C) : inv (e.hom.app X) = e.inv.app X := by
  cat_disch

namespace CategoryTheory

namespace Bicategory

open Bicategory

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]

section

variable {a b : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : a ⟶ b} {r₂ : b ⟶ a}
  (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)
/-- Relating the conjugateEquiv of adjunctions when
replacing the left adjunction by an isomorphic one. -/
lemma conjugateEquiv_congrIso_left {l₁' : a ⟶ b} {r₁' : b ⟶ a} (adj₁' : l₁' ⊣ r₁')
    (e₁ : l₁ ≅ l₁') (e₂ : r₁' ≅ r₁) (h : (Bicategory.conjugateIsoEquiv adj₁' adj₁) e₁ = e₂)
    (φ : l₂ ⟶ l₁) :
    conjugateEquiv adj₁ adj₂ φ = e₂.inv ≫ conjugateEquiv adj₁' adj₂ (φ ≫ e₁.hom) := by
  subst h
  simp [conjugateIsoEquiv_apply_inv, conjugateEquiv_comp]

/-- Relating the conjugateEquiv of adjunctions when
replacing the right adjunction by an isomorphic one. -/
lemma conjugateEquiv_congrIso_right {l₂' : a ⟶ b} {r₂' : b ⟶ a} (adj₂' : l₂' ⊣ r₂')
    (e₁ : l₂' ≅ l₂) (e₂ : r₂ ≅ r₂') (h : (Bicategory.conjugateIsoEquiv adj₂ adj₂') e₁ = e₂)
    (φ : l₂ ⟶ l₁) :
    conjugateEquiv adj₁ adj₂ φ = conjugateEquiv adj₁ adj₂' (e₁.hom ≫ φ) ≫ e₂.inv := by
  subst h
  simp [conjugateIsoEquiv_apply_inv, conjugateEquiv_comp]

/-- Relating the inverse of conjugateEquiv of adjunctions when
replacing the left adjunction by an isomorphic one. -/
lemma conjugateEquiv_symm_congrIso_left {l₁' : a ⟶ b} {r₁' : b ⟶ a} (adj₁' : l₁' ⊣ r₁')
    (e₁ : l₁ ≅ l₁') (e₂ : r₁' ≅ r₁) (h : (Bicategory.conjugateIsoEquiv adj₁' adj₁) e₁ = e₂)
    (ψ : r₁ ⟶ r₂) :
    (conjugateEquiv adj₁ adj₂).symm ψ = (conjugateEquiv adj₁' adj₂).symm (e₂.hom ≫ ψ) ≫ e₁.inv := by
  replace h := congr((Bicategory.conjugateIsoEquiv adj₁' adj₁).symm $h)
  simp only [Equiv.symm_apply_apply] at h
  subst h
  simp [conjugateIsoEquiv_symm_apply_inv, conjugateEquiv_symm_comp]

/-- Relating the inverse of conjugateEquiv of adjunctions when
replacing the right adjunction by an isomorphic one. -/
lemma conjugateEquiv_symm_congrIso_right {l₂' : a ⟶ b} {r₂' : b ⟶ a} (adj₂' : l₂' ⊣ r₂')
    (e₁ : l₂' ≅ l₂) (e₂ : r₂ ≅ r₂') (h : (Bicategory.conjugateIsoEquiv adj₂ adj₂') e₁ = e₂)
    (ψ : r₁ ⟶ r₂) :
    (conjugateEquiv adj₁ adj₂).symm ψ = e₁.inv ≫ (conjugateEquiv adj₁ adj₂').symm (ψ ≫ e₂.hom) := by
  replace h := congr((Bicategory.conjugateIsoEquiv adj₂ adj₂').symm $h)
  simp only [Equiv.symm_apply_apply] at h
  subst h
  simp [conjugateIsoEquiv_symm_apply_inv, conjugateEquiv_symm_comp]

  -- replace h := congr((Bicategory.conjugateIsoEquiv adj₁' adj₁).symm $h)
  -- simp only [Equiv.symm_apply_apply] at h
  -- subst h
  -- simp [conjugateIsoEquiv_symm_apply_inv, conjugateEquiv_symm_comp]
end

section mateEquivHComp

variable {a : B} {b : B} {c : B} {d : B} {e : B} {f : B}
variable {g : a ⟶ d} {h : b ⟶ e} {k : c ⟶ f}
variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : d ⟶ e} {r₂ : e ⟶ d}
variable {l₃ : b ⟶ c} {r₃ : c ⟶ b} {l₄ : e ⟶ f} {r₄ : f ⟶ e}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃) (adj₄ : l₄ ⊣ r₄)

/-- The mates equivalence commutes with horizontal composition of squares. -/
theorem mateEquiv_symm_hcomp (α : r₁ ≫ g ⟶ h ≫ r₂) (β : r₃ ≫ h ⟶ k ≫ r₄) :
    (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄)).symm (rightAdjointSquare.hcomp α β) =
      leftAdjointSquare.hcomp ((mateEquiv adj₁ adj₂).symm α) ((mateEquiv adj₃ adj₄).symm β) := by
  obtain ⟨α, rfl⟩ := (mateEquiv adj₁ adj₂).surjective α
  obtain ⟨β, rfl⟩ := (mateEquiv adj₃ adj₄).surjective β
  apply (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄)).injective
  simpa using mateEquiv_hcomp .. |>.symm

end mateEquivHComp

section

variable {a b c : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
  {l₂ : b ⟶ c} {r₂ : c ⟶ b} (adj₂ : l₂ ⊣ r₂)
  {C : Type u₂} [Bicategory.{w₂, v₂} C] (F : B ⥤ᵖ C)

-- syntax (name := comp2) (priority := high) term:81
--   ppSpace ppRealGroup("⊚≫" ppHardSpace ppDedent(term:80)) : term
-- macro_rules (kind := comp2) | `($a ⊚≫ $b) => `(CategoryStruct.comp $a $b)
-- @[app_unexpander CategoryStruct.comp] meta def unexpandComp : Lean.PrettyPrinter.Unexpander
--   | `($_ $a $b) => `($a ⊚≫ $b)
--   | _ => throw ()

-- set_option trace.Meta.Tactic.simp true in
/-- Given `adj₁ : l₁ ⊣ r₁` and `adj₂ : l₂ ⊣ r₂`,
the adjunctions `F.mapAdj (adj₁.comp adj₂)` and `(F.mapAdj adj₁).comp (F.mapAdj adj₂)`
are isomorphic in the sense that the isomorphisms `F.mapComp l₁ l₂` and `F.mapComp r₂ r₁`
induce an isomorphism between these adjunctions, i.e. are conjugate via the adjunctions. -/
lemma Pseudofunctor.conjugateEquiv_mapAdj_comp_mapComp_hom :
    conjugateEquiv ((F.mapAdj adj₁).comp (F.mapAdj adj₂)) (F.mapAdj (adj₁.comp adj₂))
      (F.mapComp l₁ l₂).hom =
      (F.mapComp r₂ r₁).inv := by
  rw [conjugateEquiv_apply']
  dsimp [bicategoricalComp]
  simp only [Category.id_comp, whiskerRight_comp, id_whiskerRight, Iso.inv_hom_id, Category.comp_id,
    PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_whisker_right,
    F.mapComp_id_left_hom, Category.assoc, whiskerLeft_comp, Pseudofunctor.map₂_associator,
    Pseudofunctor.map₂_associator_inv, Iso.inv_hom_id_assoc, whiskerLeft_inv_hom_assoc, cancelIso,
    comp_whiskerLeft, comp_whiskerRight, whisker_assoc, leftUnitor_whiskerRight,
    pentagon_inv_hom_hom_hom_inv_assoc]
  /- Bring in the right triangle identity for adj₁ -/
  have rt₁ :
    (F.map r₁ ◁ (F.mapId a).inv)
      ≫ (_ ◁ F.map₂ adj₁.unit)
      ≫ (_ ◁ (F.mapComp l₁ r₁).hom)
      ≫ (α_ _ _ _).inv
      ≫ ((F.mapComp r₁ l₁).inv ▷ _)
      ≫ (F.map₂ adj₁.counit ▷ _)
      ≫ (F.mapId b).hom ▷ _ =
    (ρ_ _).hom ≫ (λ_ _).inv := by
     rw [← dsimp% (F.mapAdj adj₁).right_triangle]
     bicategory
  simp_rw [← whiskerLeft_comp_assoc (F.map r₂), pentagon_inv_assoc,
    ← associator_inv_naturality_left_assoc,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc, reassoc_of% rt₁,
    whiskerLeft_comp, whiskerLeft_rightUnitor, Category.assoc, id_whiskerLeft,
    cancelIso]
  /- Now a version of the right triangle identity for adj₂ -/
  have rt₂:
      (F.map r₂ ◁ (F.mapId b).inv ▷ F.map r₁)
        ≫ (_ ◁ F.map₂ adj₂.unit ▷ _)
        ≫ (_ ◁ (F.mapComp l₂ r₂).hom ▷ _)
        ≫ (_ ◁ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv
        ≫ ((F.mapComp r₂ l₂).inv ▷ _)
        ≫ (F.map₂ adj₂.counit ▷ _)
        ≫ ((F.mapId c).hom ▷ _) ≫ (λ_ _).hom =
      (α_ _ _ _).inv ≫ (ρ_ _).hom ▷ _ := by
    rw [← dsimp% rotate_isos% 0 1 (((F.mapAdj adj₂).right_triangle) ▷% F.map r₁)]
    bicategory
  simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_inv_hom_assoc]
  simp_rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, id_whiskerLeft_assoc,
    Iso.inv_hom_id, reassoc_of% rt₂]
  bicategory

@[inherit_doc Pseudofunctor.conjugateEquiv_mapAdj_comp_mapComp_hom]
lemma Pseudofunctor.conjugateEquiv_symm_mapAdj_comp_mapComp_inv :
    (conjugateEquiv ((F.mapAdj adj₁).comp (F.mapAdj adj₂)) (F.mapAdj (adj₁.comp adj₂))).symm
      (F.mapComp r₂ r₁).inv =
      (F.mapComp l₁ l₂).hom := by
  apply (conjugateEquiv ((F.mapAdj adj₁).comp (F.mapAdj adj₂))
    (F.mapAdj (adj₁.comp adj₂))).injective
  simp [Pseudofunctor.conjugateEquiv_mapAdj_comp_mapComp_hom]

@[inherit_doc Pseudofunctor.conjugateEquiv_mapAdj_comp_mapComp_hom]
lemma Pseudofunctor.conjugateEquiv_mapAdj_symm_comp_mapComp_hom' :
    (conjugateEquiv (F.mapAdj (adj₁.comp adj₂)) ((F.mapAdj adj₁).comp (F.mapAdj adj₂))).symm
      (F.mapComp r₂ r₁).hom =
      (F.mapComp l₁ l₂).inv:= by
  have := Bicategory.conjugateEquiv_symm_comm (adj₁ := ((F.mapAdj adj₁).comp (F.mapAdj adj₂)))
    (adj₂ := (F.mapAdj (adj₁.comp adj₂)))
    (α := (F.mapComp r₂ r₁).inv) (β := (F.mapComp r₂ r₁).hom)
  rw [Pseudofunctor.conjugateEquiv_symm_mapAdj_comp_mapComp_inv] at this
  simpa [← Iso.eq_comp_inv] using this

@[inherit_doc Pseudofunctor.conjugateEquiv_mapAdj_comp_mapComp_hom]
lemma Pseudofunctor.conjugateEquiv_mapAdj_comp_mapComp_inv' :
    (conjugateEquiv (F.mapAdj (adj₁.comp adj₂)) ((F.mapAdj adj₁).comp (F.mapAdj adj₂)))
      (F.mapComp l₁ l₂).inv =
      (F.mapComp r₂ r₁).hom := by
  apply (conjugateEquiv (F.mapAdj (adj₁.comp adj₂))
    ((F.mapAdj adj₁).comp (F.mapAdj adj₂))).symm.injective
  simp [Pseudofunctor.conjugateEquiv_mapAdj_symm_comp_mapComp_hom']

end

end CategoryTheory.Bicategory
