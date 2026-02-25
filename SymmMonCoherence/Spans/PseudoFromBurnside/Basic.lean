/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.Spans.EffBurnside
public import SymmMonCoherence.Spans.Inclusions
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
public import SymmMonCoherence.ForMathlib.CategoryTheory.Bicategory.Adjunction.Pseudofunctor
public import SymmMonCoherence.ForMathlib.Tactic.CategoryTheory.CancelIso
public import SymmMonCoherence.ForMathlib.Tactic.CategoryTheory.InvElaborator
public import SymmMonCoherence.ForMathlib.CategoryTheory.Bicategory.Adjunction.Mates
public import Mathlib.Tactic.DepRewrite

/-! # Pseudofunctors from the effective Burnside (2,1)-category. -/

@[expose] public section

namespace CategoryTheory.EffBurnside

open Bicategory
universe w₁ v₁ v₂ u₁ u₂
variable (C : Type u₁) [Category.{v₁} C]

/-- A helper structure to construct pseudofunctors out of the effective Burnside
category of a category. This is essentially the data of two pseudofunctors
`u : LocallyDiscrete C ⥤ᵖ B` and `v : LocallyDiscrete Cᵒᵖ ⥤ᵖ B` that
(definitionally) share the same action on objects, along with the extra data
of a base change isomorphism `u r ≫ v b ≅ v t ≫ u l` when
```
     t
 c₀----> c₁
 |       |
l|       |r
 v       v
 c₂----> c₃
     b
```
is a pullback square in `C`,
which must furthermore satisfy compatibilities with respect to pasting of squares.

In the paper, these are called "Pith-Beck-Chevalley systems". -/
structure PseudofunctorCore (B : Type u₂) [Bicategory.{w₁, v₂} B] where
  /-- The action on objects. -/
  obj : C → B
  /-- The left action on morphisms, it corresponds to the action of the pseudofunctor
  on spans of the form `inl.map _` -/
  u {x y : C} : (x ⟶ y) → (obj x ⟶ obj y)
  /-- The right action on morphisms, it corresponds to the action of the pseudofunctor
  on spans of the form `inr.map _` -/
  v {x y : C} : (x ⟶ y) → (obj y ⟶ obj x)
  /-- The left structure isomorphism on identities. -/
  uId' {x : C} (f : x ⟶ x) (hf : f = 𝟙 x := by cat_disch) : u f ≅ 𝟙 (obj x)
  /-- The right structure isomorphism on identities. -/
  vId' {x : C} (f : x ⟶ x) (hf : f = 𝟙 x := by cat_disch) : v f ≅ 𝟙 (obj x)
  /-- The left structure isomorphism on compositions. -/
  uComp' {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (hfg : f ≫ g = h := by cat_disch) :
    u h ≅ u f ≫ u g
  /-- The right structure isomorphism on compositions. -/
  vComp' {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (hfg : f ≫ g = h := by cat_disch) :
    v h ≅ v g ≫ v f
  -- pseudofunctoriality of l
  u_associator {c₀ c₁ c₂ c₃ : C} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) (h : c₂ ⟶ c₃) :
      (uComp' (f ≫ g) h ((f ≫ g) ≫ h)).hom ≫
        (uComp' f g (f ≫ g)).hom ▷ u h ≫ (α_ (u f) (u g) (u h)).hom ≫
        u f ◁ (uComp' g h (g ≫ h)).inv ≫ (uComp' f (g ≫ h) (f ≫ g ≫ h)).inv =
      eqToHom (by simp) := by
    cat_disch
  u_left_unitor {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
      (uComp' (𝟙 c₀) f (𝟙 c₀ ≫ f)).hom ≫ (uId' (𝟙 c₀)).hom ▷ u f ≫ (λ_ (u f)).hom =
        eqToHom (by simp) := by
    cat_disch
  u_right_unitor {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
      (uComp' f (𝟙 c₁) (f ≫ 𝟙 c₁)).hom ≫ u f ◁ (uId' (𝟙 c₁)).hom ≫ (ρ_ (u f)).hom =
      eqToHom (by simp) := by
    cat_disch
  -- pseudofunctoriality of r
  -- the forms here are tailored for use in LocallyDiscrete.mkPseudofunctor
  v_associator {c₀ c₁ c₂ c₃ : C} (f : c₁ ⟶ c₀) (g : c₂ ⟶ c₁) (h : c₃ ⟶ c₂) :
      (vComp' h (g ≫ f) (h ≫ g ≫ f)).hom ≫ (vComp' g f (g ≫ f)).hom ▷ v h ≫
        (α_ (v f) (v g) (v h)).hom ≫
        v f ◁ (vComp' h g (h ≫ g)).inv ≫ (vComp' (h ≫ g) f ((h ≫ g) ≫ f)).inv =
      eqToHom (by simp) := by
    cat_disch
  v_left_unitor {c₀ c₁ : C} (f : c₁ ⟶ c₀) :
      (vComp' f (𝟙 c₀) (f ≫ 𝟙 c₀)).hom ≫ (vId' (𝟙 c₀)).hom ▷ v f ≫ (λ_ (v f)).hom =
      eqToHom (by simp) := by
    cat_disch
  v_right_unitor {c₀ c₁ : C} (f : c₁ ⟶ c₀) :
      (vComp' (𝟙 c₁) f (𝟙 c₁ ≫ f)).hom ≫ v f ◁ (vId' (𝟙 c₁)).hom ≫ (ρ_ (v f)).hom =
      eqToHom (by simp) := by
    cat_disch
  /-- The base change isomorphism on cartesian squares
  ```
       t
   c₀ ----> c₁
   |        |
  l|        |r
   v        v
   c₂ ----> c₃
       b
  ``` -/
  baseChangeIso {c₀ c₁ c₂ c₃ : C} (t : c₀ ⟶ c₁) (l : c₀ ⟶ c₂) (r : c₁ ⟶ c₃) (b : c₂ ⟶ c₃)
    (S : IsPullback t l r b) :
    u r ≫ v b ≅ v t ≫ u l
  baseChangeIso_unit_vert {x y : C} (f : x ⟶ y) :
    (baseChangeIso f (𝟙 x) (𝟙 y) f (IsPullback.of_vert_isIso .mk)).hom =
    (uId' (𝟙 y)).hom ▷ v f ≫ (λ_ _).hom ≫ (ρ_ _).inv ≫ v f ◁ (uId' (𝟙 x)).inv
  baseChangeIso_unit_horiz {x y : C} (f : x ⟶ y) :
    (baseChangeIso (𝟙 x) f f (𝟙 y) (IsPullback.of_horiz_isIso .mk)).hom =
    u f ◁ (vId' (𝟙 y)).hom ≫ (ρ_ _).hom  ≫ (λ_ _).inv ≫ (vId' (𝟙 x)).inv ▷ u f
  /-- Compatibility of the base change isomorphism with horizontal pasting of squares:
  ```
       f₀₁      f₁₂
    c₀ ---> c₁ ---> c₂
    |       |       |
  v₀|  S₁ v₁|   S₂  |v₂
    v       v       v
    c₃ ---> c₄ ---> c₅
       f₃₄      f₄₅
  ``` -/
  baseChangeIso_comp_horiz {c₀ c₁ c₂ c₃ c₄ c₅ : C}
    {f₀₁ : c₀ ⟶ c₁} {f₁₂ : c₁ ⟶ c₂}
    {v₀ : c₀ ⟶ c₃} {v₁ : c₁ ⟶ c₄} {v₂ : c₂ ⟶ c₅}
    {f₃₄ : c₃ ⟶ c₄} {f₄₅ : c₄ ⟶ c₅}
    (S₁ : IsPullback f₀₁ v₀ v₁ f₃₄) (S₂ : IsPullback f₁₂ v₁ v₂ f₄₅) :
    (baseChangeIso (f₀₁ ≫ f₁₂) v₀ v₂ (f₃₄ ≫ f₄₅) (S₁.paste_horiz S₂)).hom =
      u v₂ ◁ (vComp' f₃₄ f₄₅ (f₃₄ ≫ f₄₅)).hom ≫
      (α_ (u v₂) (v f₄₅) (v f₃₄)).inv ≫
      (baseChangeIso f₁₂ v₁ v₂ f₄₅ S₂).hom ▷ v f₃₄ ≫
      (α_ (v f₁₂) (u v₁) (v f₃₄)).hom ≫
      v f₁₂ ◁ (baseChangeIso f₀₁ v₀ v₁ f₃₄ S₁).hom ≫
      (α_ (v f₁₂) (v f₀₁) (u v₀)).inv ≫
      (vComp' f₀₁ f₁₂ (f₀₁ ≫ f₁₂)).inv ▷ u v₀
  /-- Compatibility of the base change isomorphism with vertical pasting of squares:
  ```
        h₀
   c₀ ----> c₁
   |        |
   |f₀₂ S₁  |f₁₃
   v        v
   c₂ ----->c₃
   |    h₁  |
   |f₂₄ S₂  |f₃₅
   v        v
   c₄ ----->c₅
        h₂
  ``` -/
  baseChangeIso_comp_vert {c₀ c₁ c₂ c₃ c₄ c₅ : C}
    {h₀ : c₀ ⟶ c₁} {f₀₂ : c₀ ⟶ c₂} {f₁₃ : c₁ ⟶ c₃} {h₁ : c₂ ⟶ c₃}
    {h₂ : c₄ ⟶ c₅} {f₂₄ : c₂ ⟶ c₄} {f₃₅ : c₃ ⟶ c₅}
    (S₁ : IsPullback h₀ f₀₂ f₁₃ h₁) (S₂ : IsPullback h₁ f₂₄ f₃₅ h₂) :
    (baseChangeIso h₀ (f₀₂ ≫ f₂₄) (f₁₃ ≫ f₃₅) h₂ (S₁.paste_vert S₂)).hom =
      (uComp' f₁₃ f₃₅ (f₁₃ ≫ f₃₅)).hom ▷ v h₂ ≫
      (α_ (u f₁₃) (u f₃₅) (v h₂)).hom ≫
      u f₁₃ ◁ (baseChangeIso h₁ f₂₄ f₃₅ h₂ S₂).hom ≫
      (α_ (u f₁₃) (v h₁) (u f₂₄)).inv ≫
      (baseChangeIso h₀ f₀₂ f₁₃ h₁ S₁).hom ▷ u f₂₄ ≫
      (α_ (v h₀) (u f₀₂) (u f₂₄)).hom ≫
      v h₀ ◁ (uComp' f₀₂ f₂₄ (f₀₂ ≫ f₂₄)).inv

namespace PseudofunctorCore

variable {C} {B : Type u₂} [Bicategory.{w₁, v₂} B] (P : PseudofunctorCore C B)

/- It is useful to bundle `u` and `v` as pseudofunctors now so that we can apply some general
results about pseudofunctors from a strict bicategory to them within the proofs in
toPseudofunctor, but we keep most of this private, as they become
useless once we have.
Even as abbrev, the definitional equality
`uPseudofunctor.obj = PseudofunctorCore.vPseudofunctor.obj` does
not hold at reducible transparency. -/

/-- Bundling the data in `u` and related fields as a pseudofunctor
`LocallyDiscrete C ⥤ᵖ B`. -/
private abbrev uPseudofunctor :
    LocallyDiscrete C ⥤ᵖ B :=
  LocallyDiscrete.mkPseudofunctor (B₀ := C) (C := B)
    (obj := P.obj)
    (map := P.u)
    (mapId := fun x ↦ (P.uId' (𝟙 x)))
    (mapComp := fun f g ↦ P.uComp' f g (f ≫ g))
    (map₂_associator := P.u_associator)
    (map₂_left_unitor := P.u_left_unitor)
    (map₂_right_unitor := P.u_right_unitor)

/-- Bundling the data in `v` and related fields as a pseudofunctor
`(LocallyDiscrete C)ᵒᵖ ⥤ᵖ B`. -/
private abbrev vPseudofunctor :
    (LocallyDiscrete Cᵒᵖ) ⥤ᵖ B :=
  LocallyDiscrete.mkPseudofunctor (B₀ := Cᵒᵖ) (C := B)
    (obj := fun x ↦ P.obj x.unop)
    (map := fun {x y} f ↦ P.v f.unop)
    (mapId := fun x ↦ P.vId' (𝟙 x.unop))
    (mapComp := fun {x y z} f g ↦ P.vComp' g.unop f.unop _ rfl)
    (map₂_associator := by
      intros
      simpa using P.v_associator _ _ _)
    (map₂_left_unitor := by
      intros
      simpa using P.v_left_unitor _)
    (map₂_right_unitor := by
      intros
      simpa using P.v_right_unitor _)

private lemma uPseudofunctor_obj (x : C) :
    P.uPseudofunctor.obj ⟨x⟩ = P.obj x := rfl

private lemma uPseudofunctor_map
    {x y : C} (f : x ⟶ y) :
    P.uPseudofunctor.map f.toLoc = P.u f :=
  rfl

private lemma uPseudofunctor_mapId'
    {x : C} (f : x ⟶ x) (hf : f = 𝟙 x := by cat_disch) :
    P.uPseudofunctor.mapId' f.toLoc = P.uId' f hf := by
  subst hf
  simp [Pseudofunctor.mapId']

private lemma uPseudofunctor_mapComp'
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (hfg : f ≫ g = h := by cat_disch) :
    P.uPseudofunctor.mapComp' f.toLoc g.toLoc h.toLoc = P.uComp' f g h hfg := by
  subst hfg
  simp [Pseudofunctor.mapComp']

private lemma vPseudofunctor_obj (x : C) :
    P.vPseudofunctor.obj ⟨Opposite.op x⟩ = P.obj x := rfl

private lemma vPseudofunctor_map
    {x y : C} (f : x ⟶ y) :
    P.vPseudofunctor.map f.op.toLoc = P.v f :=
  rfl

private lemma vPseudofunctor_mapId'
    {x : C} (f : x ⟶ x) (hf : f = 𝟙 x := by cat_disch) :
    P.vPseudofunctor.mapId' f.op.toLoc = P.vId' f hf := by
  subst hf
  simp [Pseudofunctor.mapId']

private lemma vPseudofunctor_mapComp'
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (hfg : f ≫ g = h := by cat_disch) :
    P.vPseudofunctor.mapComp' g.op.toLoc f.op.toLoc h.op.toLoc = P.vComp' f g h hfg := by
  subst hfg
  simp [Pseudofunctor.mapComp']

/-- This is a version of `Pseudofunctor.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom` for
`uComp'`. -/
@[reassoc]
private lemma uComp'_associativity'
    {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁)
    (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃) (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f : c₀ ⟶ c₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (hf : f₀₁ ≫ f₁₃ = f) :
  (P.uComp' f₀₁ f₁₃ f).hom ≫ P.u f₀₁ ◁ (P.uComp' f₁₂ f₂₃ f₁₃).hom =
  (P.uComp' f₀₂ f₂₃ f).hom ≫
    (P.uComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ P.u f₂₃ ≫ (α_ _ _ _).hom := by
  simp only [← uPseudofunctor_mapComp',
    ← uPseudofunctor_obj, ← uPseudofunctor_map]
  exact P.uPseudofunctor.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom _ _ _ _ _ _ _
    (by grind) (by grind)

@[reassoc]
private lemma uComp'_id_l
    {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    P.uComp' f (𝟙 c₁) f (by grind) = (ρ_ _).symm ≪≫ whiskerLeftIso _ (P.uId' (𝟙 c₁)).symm := by
  simp only [← uPseudofunctor_mapComp', ← uPseudofunctor_mapId',
    ← uPseudofunctor_obj, ← uPseudofunctor_map]
  simpa [← uPseudofunctor_mapId'] using P.uPseudofunctor.mapComp'_comp_id f.toLoc

@[reassoc]
private lemma uComp'_id_r
    {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    P.uComp' (𝟙 c₀) f f (by grind) = (λ_ _).symm ≪≫ whiskerRightIso (P.uId' (𝟙 c₀)).symm _ := by
  simp only [← uPseudofunctor_mapComp', ← uPseudofunctor_mapId',
    ← uPseudofunctor_obj, ← uPseudofunctor_map]
  simpa [← uPseudofunctor_mapId'] using P.uPseudofunctor.mapComp'_id_comp f.toLoc

/-- This is a version of `Pseudofunctor.mapComp'₀₁₃_hom` for
`uComp'`. -/
@[reassoc]
private lemma uComp'₀₁₃_hom
    {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁)
    (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃) (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f : c₀ ⟶ c₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (hf : f₀₁ ≫ f₁₃ = f) :
  (P.uComp' f₀₁ f₁₃ f).hom =
  (P.uComp' f₀₂ f₂₃ f).hom ≫ (P.uComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ P.u f₂₃ ≫
    (α_ _ _ _).hom ≫ P.u f₀₁ ◁ (P.uComp' f₁₂ f₂₃ f₁₃).inv := by
  simp only [← uPseudofunctor_mapComp',
    ← uPseudofunctor_obj, ← uPseudofunctor_map]
  exact P.uPseudofunctor.mapComp'₀₁₃_hom _ _ _ _ _ _ _
    (by grind) (by grind)

/-- This is a version of `Pseudofunctor.mapComp'₀₂₃_hom` for
`uComp'`. -/
@[reassoc]
private lemma uComp'₀₂₃_hom
    {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁)
    (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃) (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f : c₀ ⟶ c₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (hf : f₀₁ ≫ f₁₃ = f) :
  (P.uComp' f₀₂ f₂₃ f).hom =
  (P.uComp' f₀₁ f₁₃ f).hom ≫ P.u f₀₁ ◁ (P.uComp' f₁₂ f₂₃ f₁₃).hom ≫
    (α_ _ _ _).inv ≫ (P.uComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ P.u f₂₃ := by
  simp only [← uPseudofunctor_mapComp',
    ← uPseudofunctor_obj, ← uPseudofunctor_map]
  exact P.uPseudofunctor.mapComp'₀₂₃_hom _ _ _ _ _ _ _
    (by grind) (by grind)

@[reassoc]
private lemma vComp'_id_l
    {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    P.vComp' f (𝟙 c₁) f (by grind) = (λ_ _).symm ≪≫ whiskerRightIso (P.vId' (𝟙 c₁)).symm _ := by
  simp only [← vPseudofunctor_mapComp', ← vPseudofunctor_mapId',
    ← vPseudofunctor_obj, ← vPseudofunctor_map]
  simpa [← vPseudofunctor_mapId'] using
    P.vPseudofunctor.mapComp'_id_comp f.op.toLoc

@[reassoc]
private lemma vComp'_id_r
    {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    P.vComp' (𝟙 c₀) f f (by grind) = (ρ_ _).symm ≪≫ whiskerLeftIso _ (P.vId' (𝟙 c₀)).symm := by
  simp only [← vPseudofunctor_mapComp', ← vPseudofunctor_mapId',
    ← vPseudofunctor_obj, ← vPseudofunctor_map]
  simpa [← vPseudofunctor_mapId'] using
    P.vPseudofunctor.mapComp'_comp_id f.op.toLoc

/-- This is a version of `Pseudofunctor.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom` for
`vComp'`. -/
@[reassoc]
private lemma vComp'_associativity'
    {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁)
    (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃) (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f : c₀ ⟶ c₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (hf : f₀₁ ≫ f₁₃ = f) :
  (P.vComp' f₀₂ f₂₃ f).hom ≫ P.v f₂₃ ◁ (P.vComp' f₀₁ f₁₂ f₀₂ h₀₂).hom =
  (P.vComp' f₀₁ f₁₃ f).hom ≫
    (P.vComp' f₁₂ f₂₃ f₁₃).hom ▷ P.v f₀₁ ≫ (α_ _ _ _).hom := by
  simp only [← vPseudofunctor_mapComp',
    ← vPseudofunctor_obj, ← vPseudofunctor_map]
  exact P.vPseudofunctor.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom _ _ _ _ _ _ _
    (by grind) (by grind)

/-- This is a version of `Pseudofunctor.mapComp'₀₁₃_hom` for
`vComp'`. -/
@[reassoc]
private lemma vComp'₀₁₃_hom
    {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁)
    (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃) (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f : c₀ ⟶ c₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (hf : f₀₁ ≫ f₁₃ = f) :
  (P.vComp' f₀₁ f₁₃ f).hom =
  (P.vComp' f₀₂ f₂₃ f).hom ≫ P.v f₂₃ ◁ (P.vComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ≫
    (α_ _ _ _).inv ≫ (P.vComp' f₁₂ f₂₃ f₁₃).inv ▷ P.v f₀₁ := by
  simp only [← vPseudofunctor_mapComp',
    ← vPseudofunctor_obj, ← vPseudofunctor_map]
  exact P.vPseudofunctor.mapComp'₀₂₃_hom _ _ _ _ _ _ _
    (by grind) (by grind)

/-- This is a version of `Pseudofunctor.mapComp'₀₂₃_hom` for
`vComp'`. -/
@[reassoc]
private lemma vComp'₀₂₃_hom
    {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁)
    (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃) (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f : c₀ ⟶ c₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (hf : f₀₁ ≫ f₁₃ = f) :
  (P.vComp' f₀₂ f₂₃ f).hom =
  (P.vComp' f₀₁ f₁₃ f).hom ≫ (P.vComp' f₁₂ f₂₃ f₁₃).hom ▷ P.v f₀₁ ≫
    (α_ _ _ _).hom ≫ P.v f₂₃ ◁ (P.vComp' f₀₁ f₁₂ f₀₂ h₀₂).inv := by
  simp only [← vPseudofunctor_mapComp',
    ← vPseudofunctor_obj, ← vPseudofunctor_map]
  exact P.vPseudofunctor.mapComp'₀₁₃_hom _ _ _ _ _ _ _
    (by grind) (by grind)

-- TODO better name
private lemma baseChange_id_eq (x : C) :
    (P.baseChangeIso (𝟙 x) (𝟙 x) (𝟙 x) (𝟙 x) (IsPullback.of_horiz_isIso .mk)).hom =
      (P.uId' (𝟙 x)).hom ▷ P.v (𝟙 x) ≫ (λ_ _).hom ≫ (P.vId' (𝟙 x)).hom ≫
      (P.vId' (𝟙 x)).inv ≫ (ρ_ _).inv ≫ P.v (𝟙 x) ◁ (P.uId' (𝟙 x)).inv := by
  simp [P.baseChangeIso_unit_vert (𝟙 x)]

/-- A version of `baseChange_comp` that allows specifying the composites.
It corresponds to the following diagram:
```
      f₀₁      f₁₂
  c₀ ----> c₁ ----> c₂
  |        |        |
g₀|   S₁ g₁|   S₂ g₂|
  v        v        v
  c₃ ----> c₄ ----> c₅
      f₃₄      f₄₅
```
where both squares are pullbacks, and `f₀₂` (resp `f₃₅`) is the composite of the top
(resp bottom) row.
-/
private lemma baseChangeIso_comp_horiz'
    {c₀ c₁ c₂ c₃ c₄ c₅ : C}
    (f₀₁ : c₀ ⟶ c₁) (f₁₂ : c₁ ⟶ c₂) (f₀₂ : c₀ ⟶ c₂)
    (f₃₄ : c₃ ⟶ c₄) (f₄₅ : c₄ ⟶ c₅) (f₃₅ : c₃ ⟶ c₅)
    (g₀ : c₀ ⟶ c₃) (g₁ : c₁ ⟶ c₄) (g₂ : c₂ ⟶ c₅)
    (S₁ : IsPullback f₀₁ g₀ g₁ f₃₄) (S₂ : IsPullback f₁₂ g₁ g₂ f₄₅) (S₃ : IsPullback f₀₂ g₀ g₂ f₃₅)
    (hf : f₀₁ ≫ f₁₂ = f₀₂ := by cat_disch) (hf' : f₃₄ ≫ f₄₅ = f₃₅ := by cat_disch) :
    (P.baseChangeIso f₀₂ g₀ g₂ f₃₅ S₃).hom =
      P.u g₂ ◁ (P.vComp' f₃₄ f₄₅ f₃₅ hf').hom ≫
      (α_ (P.u g₂) (P.v f₄₅) (P.v f₃₄)).inv ≫
      (P.baseChangeIso f₁₂ g₁ g₂ f₄₅ S₂).hom ▷ P.v f₃₄ ≫
      (α_ (P.v f₁₂) (P.u g₁) (P.v f₃₄)).hom ≫
      P.v f₁₂ ◁ (P.baseChangeIso f₀₁ g₀ g₁ f₃₄ S₁).hom ≫
      (α_ (P.v f₁₂) (P.v f₀₁) (P.u g₀)).inv ≫
      (P.vComp' f₀₁ f₁₂ f₀₂ hf).inv ▷ P.u g₀ := by
  subst_vars
  apply P.baseChangeIso_comp_horiz

/-- A version of `baseChange_comp_vert` that allows specifying the composites.
It corresponds to the following diagram:
```
        u₀₁
    c₀ ----> c₁
    |        |
f₀₂ |   S₁   | f₁₃
    v        v
    c₂ ----> c₃
    |   u₂₃  |
f₂₄ |   S₂   | f₃₅
    v        v
    c₄ ----> c₅
        u₄₅
```
where both squares are pullbacks, and `f₀₄` (resp `f₁₅`) is the composite of the left
(resp right) column.
-/
private lemma baseChangeIso_comp_vert'
    {c₀ c₁ c₂ c₃ c₄ c₅ : C}
    (u₀₁ : c₀ ⟶ c₁) (u₂₃ : c₂ ⟶ c₃) (u₄₅ : c₄ ⟶ c₅)
    (f₀₂ : c₀ ⟶ c₂) (f₂₄ : c₂ ⟶ c₄) (f₀₄ : c₀ ⟶ c₄)
    (f₁₃ : c₁ ⟶ c₃) (f₃₅ : c₃ ⟶ c₅) (f₁₅ : c₁ ⟶ c₅)
    (S₁ : IsPullback u₀₁ f₀₂ f₁₃ u₂₃) (S₂ : IsPullback u₂₃ f₂₄ f₃₅ u₄₅)
    (S₃ : IsPullback u₀₁ f₀₄ f₁₅ u₄₅)
    (hv : f₀₂ ≫ f₂₄ = f₀₄ := by cat_disch) (hh : f₁₃ ≫ f₃₅ = f₁₅ := by cat_disch) :
    (P.baseChangeIso u₀₁ f₀₄ f₁₅ u₄₅ S₃).hom =
      (P.uComp' f₁₃ f₃₅ f₁₅ hh).hom ▷ P.v u₄₅ ≫
      (α_ (P.u f₁₃) (P.u f₃₅) (P.v u₄₅)).hom ≫
      P.u f₁₃ ◁ (P.baseChangeIso u₂₃ f₂₄ f₃₅ u₄₅ S₂).hom ≫
      (α_ (P.u f₁₃) (P.v u₂₃) (P.u f₂₄)).inv ≫
      (P.baseChangeIso u₀₁ f₀₂ f₁₃ u₂₃ S₁).hom ▷ P.u f₂₄ ≫
      (α_ (P.v u₀₁) (P.u f₀₂) (P.u f₂₄)).hom ≫
      P.v u₀₁ ◁ (P.uComp' f₀₂ f₂₄ f₀₄ hv).inv := by
  subst_vars
  apply P.baseChangeIso_comp_vert

section Adjunction

section Ψ

/-- A shorthand for the isomorphism 𝟙 (P.obj z) ≅ P.u (𝟙 z) ≫ P.v (𝟙 z)
coming from unitality of the pseudofunctors. We’ll be seeing this
composition a lot, so it’s better to give it a name. -/
def Ψ (z : C) :
    𝟙 (P.obj z) ≅ P.u (𝟙 z) ≫ P.v (𝟙 z) :=
  (P.uId' (𝟙 _)).symm ≪≫ (ρ_ _).symm ≪≫ whiskerLeftIso _ (P.vId' (𝟙 _)).symm

/-- A shorthand for the isomorphism 𝟙 (P.obj z) ≅ P.v (𝟙 z) ≫ P.u (𝟙 z)
coming from unitality of the pseudofunctors. We’ll be seeing this
composition a lot, so it’s better to give it a name. -/
def Ψ' (z : C) :
    𝟙 (P.obj z) ≅ P.v (𝟙 z) ≫ P.u (𝟙 z) :=
  (P.vId' (𝟙 _)).symm ≪≫ (ρ_ _).symm ≪≫ whiskerLeftIso _ (P.uId' (𝟙 _)).symm

/-- A restatement of `baseChange_id_eq` in terms of `Ψ` and `Ψ'` -/
lemma Ψ_baseChange_id (z : C) :
    P.Ψ z ≪≫ P.baseChangeIso (𝟙 z) (𝟙 z) (𝟙 z) (𝟙 z) (IsPullback.of_horiz_isIso .mk) = P.Ψ' z := by
  dsimp [Ψ, Ψ']
  ext
  simp [baseChange_id_eq, whisker_exchange_assoc]

-- rotating the equality above

lemma Ψ_baseChange_id_hom (z : C) :
    (P.Ψ z).hom ≫ (P.baseChangeIso (𝟙 z) (𝟙 z) (𝟙 z) (𝟙 z) (IsPullback.of_horiz_isIso .mk)).hom =
    (P.Ψ' z).hom :=
  congr($(P.Ψ_baseChange_id z).hom)

lemma baseChange_id_Ψ_inv (z : C) :
    (P.baseChangeIso (𝟙 z) (𝟙 z) (𝟙 z) (𝟙 z) (IsPullback.of_horiz_isIso .mk)).inv ≫ (P.Ψ z).inv =
    (P.Ψ' z).inv :=
  congr($(P.Ψ_baseChange_id z).inv)

lemma Ψ'_baseChange_id_hom (z : C) :
    (P.Ψ' z).hom ≫ (P.baseChangeIso (𝟙 z) (𝟙 z) (𝟙 z) (𝟙 z) (IsPullback.of_horiz_isIso .mk)).inv =
    (P.Ψ z).hom :=
  Eq.symm <| rotate_isos% ← 0 1 (P.Ψ_baseChange_id_hom z)

lemma baseChange_id_Ψ'_inv (z : C) :
    (P.baseChangeIso (𝟙 z) (𝟙 z) (𝟙 z) (𝟙 z) (IsPullback.of_horiz_isIso .mk)).hom ≫ (P.Ψ' z).inv =
    (P.Ψ z).inv :=
  Eq.symm <| rotate_isos% 1 0 (P.baseChange_id_Ψ_inv z)

@[reassoc]
lemma Ψ_eq (z : C) :
    P.Ψ z =
    (P.vId' (𝟙 _)).symm ≪≫ (λ_ _).symm ≪≫ whiskerRightIso (P.uId' (𝟙 _)).symm _ := by
  ext
  dsimp [Ψ]
  rotate_isos 0 1
  simp [whisker_exchange]

@[reassoc]
lemma Ψ_hom_eq (z : C) :
    (P.Ψ z).hom =
    (P.uId' (𝟙 z)).inv ≫ (ρ_ (P.u (𝟙 z))).inv ≫ P.u (𝟙 z) ◁ (P.vId' (𝟙 z)).inv := by
  dsimp [Ψ]

@[reassoc]
lemma Ψ_inv_eq (z : C) :
    (P.Ψ z).inv =
    P.u (𝟙 z) ◁ (P.vId' (𝟙 z)).hom ≫ (ρ_ (P.u (𝟙 z))).hom ≫ (P.uId' (𝟙 z)).hom := by
  simp [Ψ]

@[reassoc]
lemma Ψ_hom_eq' (z : C) :
    (P.Ψ z).hom = (P.vId' (𝟙 z)).inv ≫ (λ_ _).inv ≫ (P.uId' (𝟙 z)).inv ▷ P.v (𝟙 z) :=
  congr($(P.Ψ_eq z).hom)

@[reassoc]
lemma Ψ_inv_eq' (z : C) :
    (P.Ψ z).inv =
    (P.uId' (𝟙 z)).hom ▷ P.v (𝟙 z) ≫ (λ_ (P.v (𝟙 z))).hom ≫ (P.vId' (𝟙 z)).hom := by
  simpa using congr($(P.Ψ_eq z).inv)

@[reassoc]
lemma Ψ'_eq (z : C) :
    P.Ψ' z =
    (P.uId' (𝟙 _)).symm ≪≫ (λ_ _).symm ≪≫ whiskerRightIso (P.vId' (𝟙 _)).symm _ := by
  ext
  dsimp [Ψ']
  rotate_isos 0 1
  simp [whisker_exchange]

@[reassoc]
lemma Ψ'_hom_eq (z : C) :
    (P.Ψ' z).hom = (P.vId' (𝟙 z)).inv ≫ (ρ_ (P.v (𝟙 z))).inv ≫ P.v (𝟙 z) ◁ (P.uId' (𝟙 z)).inv := by
  dsimp [Ψ']

@[reassoc]
lemma Ψ'_inv_eq (z : C) :
    (P.Ψ' z).inv = P.v (𝟙 z) ◁ (P.uId' (𝟙 z)).hom ≫ (ρ_ (P.v (𝟙 z))).hom ≫ (P.vId' (𝟙 z)).hom := by
  simp [Ψ']

@[reassoc]
lemma Ψ'_hom_eq' (z : C) :
    (P.Ψ' z).hom = (P.uId' (𝟙 z)).inv ≫ (λ_ _).inv ≫ (P.vId' (𝟙 z)).inv ▷ _ :=
  congr($(P.Ψ'_eq z).hom)

@[reassoc]
lemma Ψ'_inv_eq' (z : C) :
    (P.Ψ' z).inv = (P.vId' (𝟙 z)).hom ▷ P.u (𝟙 z) ≫ (λ_ (P.u (𝟙 z))).hom ≫ (P.uId' (𝟙 z)).hom := by
  simpa using congr($(P.Ψ'_eq z).inv)

end Ψ

section

variable {c₀ c₁ : C} (e : c₀ ≅ c₁)

/- We are intentionally not making some of the lemma simp so that we don’t end up with expressions
that are too big. For the same reason, these are `defs` and not abbrev so that we have
more control on whether or not they unfold. -/

/- Shorthand for the unit of the equivalence `P.obj c₀ ≌ P.obj c₁` induced by `e` via `P.u`. -/
def η_u : 𝟙 (P.obj c₀) ≅ P.u e.hom ≫ P.u e.inv := (P.uId' (𝟙 c₀)).symm ≪≫ P.uComp' e.hom e.inv _

lemma η_u_hom : (P.η_u e).hom = (P.uId' (𝟙 c₀)).inv ≫ (P.uComp' e.hom e.inv _).hom := rfl
lemma η_u_inv : (P.η_u e).inv =  (P.uComp' e.hom e.inv _).inv ≫ (P.uId' (𝟙 c₀)).hom := rfl

/- Shorthand for the counit of the equivalence `P.obj c₀ ≌ P.obj c₁` induced by `e` via `P.u`. -/
def ε_u : P.u e.inv ≫ P.u e.hom ≅ 𝟙 (P.obj c₁) := (P.uComp' e.inv e.hom _).symm ≪≫ P.uId' (𝟙 _)

lemma ε_u_hom : (P.ε_u e).hom = (P.uComp' e.inv e.hom _).inv ≫ (P.uId' (𝟙 _)).hom := rfl
lemma ε_u_inv : (P.ε_u e).inv = (P.uId' (𝟙 _)).inv ≫ (P.uComp' e.inv e.hom _).hom := rfl

/- Shorthand for the unit of the equivalence `P.obj c₁ ≌ P.obj c₀` induced by `e` via `P.v`. -/
def η_v : 𝟙 (P.obj c₁) ≅ P.v e.hom ≫ P.v e.inv := (P.vId' (𝟙 c₁)).symm ≪≫ P.vComp' e.inv e.hom _

lemma η_v_hom : (P.η_v e).hom = (P.vId' (𝟙 c₁)).inv ≫ (P.vComp' e.inv e.hom _).hom := rfl
lemma η_v_inv : (P.η_v e).inv = (P.vComp' e.inv e.hom _).inv ≫ (P.vId' (𝟙 c₁)).hom := rfl

/- Shorthand for the counit of the equivalence `P.obj c₁ ≌ P.obj c₀` induced by `e` via `P.v`. -/
def ε_v : P.v e.inv ≫ P.v e.hom ≅ 𝟙 (P.obj c₀) := (P.vComp' e.hom e.inv _).symm ≪≫ P.vId' (𝟙 _)

lemma ε_v_hom : (P.ε_v e).hom = (P.vComp' e.hom e.inv _).inv ≫ (P.vId' (𝟙 _)).hom := rfl
lemma ε_v_inv : (P.ε_v e).inv = (P.vId' (𝟙 _)).inv ≫ (P.vComp' e.hom e.inv _).hom := rfl

end

/- A shorthand for a term we’re going to write a lot. -/
local macro "⊠" : term => `(term| IsPullback.of_horiz_isIso .mk)

/- The equivalence data coming from an isomorphism `e : c₀ ≌ c₁` and the base change isomorphism.
This contains the data of an adjunction `P.u e.hom ⊣ P.v e.hom`.
This equivalence is made reducible so that typeclass synthesis
(and hence `bicategoricalComp`) is happy with peeking at its 1-cells. -/
@[reducible]
def baseChangeEquivalenceOfIso {c₀ c₁ : C} (e : c₀ ≅ c₁) :
    P.obj c₀ ≌ P.obj c₁ where
  hom := P.u e.hom
  inv := P.v e.hom
  unit :=
    P.Ψ' _ ≪≫ (P.baseChangeIso (𝟙 _) (𝟙 _) e.hom e.hom ⊠).symm
  counit :=
    (P.baseChangeIso e.hom e.hom (𝟙 _) (𝟙 _) ⊠).symm ≪≫ (P.Ψ _).symm
  left_triangle := by
    ext
    dsimp [leftZigzagIso, leftZigzag, bicategoricalComp]
    simp only [comp_whiskerRight, Category.assoc,
      whiskerRight_comp, id_whiskerRight, Category.id_comp,
      Iso.inv_hom_id, Category.comp_id, whiskerLeft_comp]
    have bc'' := P.baseChangeIso_comp_vert'
      (u₀₁ := 𝟙 _) (u₂₃ := e.hom) (u₄₅ := 𝟙 _)
      (f₀₂ := 𝟙 _) (f₁₃ := e.hom) (f₃₅ := 𝟙 _)
      (f₂₄ := e.hom) (f₀₄ := e.hom) (f₁₅ := e.hom)
      ⊠ ⊠ ⊠ (by simp) (by simp)
    simp only [P.baseChangeIso_unit_horiz, P.uComp'_id_l, Iso.trans_hom, Iso.symm_hom,
      whiskerLeftIso_hom, comp_whiskerRight, whisker_assoc, triangle_assoc_comp_right_inv_assoc,
      P.uComp'_id_r, Iso.trans_inv, whiskerRightIso_inv, Iso.symm_inv, whiskerLeft_comp,
      Category.assoc, Iso.inv_hom_id_assoc] at bc''
    rotate_isos 1 0 at bc''; rotate_isos ← 0 1 at bc''
    simp_rw [← reassoc_of% wl% Ψ_hom_eq',
      ← associator_naturality_middle_assoc, whisker_exchange,
      ← associator_naturality_left_assoc, whiskerRight_id, comp_whiskerRight_assoc,
      ← reassoc_of% wr% Ψ'_inv_eq] at bc''
    simp [inv% bc'']

/- A key equation for proving that the to-be-defined pseudofunctor
`EffBurnside C ⥤ᵖ B` attached to `P : PseudofunctorCore C B` respects
composition of 2-morphisms. -/
lemma baseChangeEquivalenceOfIso_counit_hom_comp
    {x y z : C} (f : x ≅ y) (g : y ≅ z) (h : x ≅ z)
    (hfg : f ≪≫ g = h := by cat_disch) :
    (P.baseChangeEquivalenceOfIso h).counit.hom =
    _ ◁ (P.uComp' f.hom g.hom h.hom).hom ≫ (P.vComp' f.hom g.hom h.hom).hom ▷ _ ⊗≫
      P.v g.hom ◁ (P.baseChangeEquivalenceOfIso f).counit.hom ▷ P.u g.hom ⊗≫
      (P.baseChangeEquivalenceOfIso g).counit.hom := by
  dsimp [bicategoricalComp]
  simp only [cat_nf, cancelIso]
  have hcomp := P.baseChangeIso_comp_horiz'
    (f₀₁ := f.hom) (f₁₂ := g.hom) (f₀₂ := h.hom)
    (f₃₄ := 𝟙 _) (f₄₅ := 𝟙 _) (f₃₅ := 𝟙 _)
    (g₀ := h.hom) (g₁ := g.hom) (g₂ := 𝟙 _)
    ⊠ ⊠ ⊠
  have vcomp := P.baseChangeIso_comp_vert'
    (f₀₂ := f.hom) (f₂₄ := g.hom) (f₀₄ := h.hom)
    (f₁₃ := 𝟙 _) (f₃₅ := g.hom) (f₁₅ := g.hom)
    (u₀₁ := f.hom) (u₂₃ := 𝟙 _) (u₄₅ := 𝟙 _)
    ⊠ ⊠ ⊠
  rw [reassoc_of% wl% vcomp] at hcomp
  rw [reassoc_of% inv% hcomp]
  simp_rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc,
    ← pentagon_inv_hom_hom_hom_inv_assoc, associator_inv_naturality_left_assoc,
    cancel_epi, pentagon_inv_hom_hom_hom_inv_assoc]
  rotate_isos ← 2 0
  simp only [pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, cancel_epi]
  rotate_isos 0 1
  simp_rw [P.vComp'_id_r, Iso.trans_inv, whiskerLeftIso_inv, Iso.symm_inv,
    whiskerLeft_comp, ← associator_naturality_right_assoc, ← whisker_exchange_assoc,
    whiskerRight_id_assoc, rightUnitor_comp_inv_assoc, cancelIso, Category.comp_id]
  rotate_isos 0 1
  simp only [P.uComp'_id_r, Iso.trans_inv, whiskerRightIso_inv, Iso.symm_inv, comp_whiskerRight,
    leftUnitor_whiskerRight, whiskerLeft_comp, comp_whiskerLeft, Category.assoc,
    Iso.inv_hom_id_assoc]
  simp_rw [← reassoc_of% wl% associator_inv_naturality_left, cancelIso,
    reassoc_of% wl% whisker_exchange, reassoc_of% wl% id_whiskerLeft, cancelIso]
  have := (P.baseChangeEquivalenceOfIso g).adjunction.left_triangle
  dsimp [leftZigzag, bicategoricalComp] at this
  have := (P.baseChangeEquivalenceOfIso g).adjunction.right_triangle
  dsimp [rightZigzag, bicategoricalComp] at this
  simp only [whiskerRight_comp, whiskerLeft_comp, inv%P.baseChangeIso_unit_horiz g.hom,
    whiskerLeft_rightUnitor_inv, Category.assoc, whiskerLeft_whiskerLeft_inv_hom_assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id, whiskerLeft_hom_inv_assoc]
  simp_rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp]
  congr 1
  simp_rw [cat_nf, leftUnitor_comp_assoc, cancelIso, P.Ψ_inv_eq']
  bicategory

/-- A technical compatibility of base change isomorphisms: given two pullback
squares
```
      t
  c₀ ---> c₁
  |       |
l |       | r
  v       v
  c₂ ---> c₃
      b
```
and
```
      t'
  c₀'---> c₁
  |       |
l'|       | r
  v       v
  c₂ ---> c₃
      b
```
as well as an isomorphism `e : c₀' ≅ c₀` compatible with the projections
(which is then unique), the base change isomorphism for the second
square can be expressed in terms of the first and the one for the square involving `e`. -/
lemma baseChange_change_pullback {c₀ c₀' c₁ c₂ c₃ : C}
    (t : c₀ ⟶ c₁) (l : c₀ ⟶ c₂) (r : c₁ ⟶ c₃) (b : c₂ ⟶ c₃)
    (t' : c₀' ⟶ c₁) (l' : c₀' ⟶ c₂)
    (e : c₀' ≅ c₀) (h₁ : IsPullback t l r b) (h₂ : IsPullback t' l' r b)
    (tr₁ : e.hom ≫ t = t') (tr₂ : e.hom ≫ l = l') :
    (P.baseChangeIso t' l' r b h₂).hom =
      (P.baseChangeIso t l r b h₁).hom ⊗≫
      (P.v t ◁ (P.Ψ _).hom ▷ P.u l ≫
      P.v t ◁ (P.baseChangeIso e.hom e.hom (𝟙 _) (𝟙 _) ⊠).hom ▷ P.u l) ⊗≫
      (P.vComp' e.hom t t').inv ▷ P.u e.hom ▷ P.u l ⊗≫
      P.v t' ◁ (P.uComp' e.hom l l').inv ⊗≫ 𝟙 _ := by
  have horiz₁ :=
    P.baseChangeIso_comp_horiz'
      (f₀₁ := 𝟙 _) (f₁₂ := t) (f₀₂ := 𝟙 _ ≫ t)
      (g₀ := l) (g₁ := l) (g₂ := r)
      (f₃₄ := 𝟙 _) (f₄₅ := b) (f₃₅ := b)
      (IsPullback.of_horiz_isIso .mk) h₁ (by convert h₁; simp)
  have horiz₂ :=
    P.baseChangeIso_comp_horiz'
      (f₀₁ := e.hom) (f₁₂ := t) (f₀₂ := t')
      (g₀ := e.hom) (g₁ := 𝟙 _) (g₂ := 𝟙 _)
      (f₃₄ := 𝟙 _) (f₄₅ := t) (f₃₅ := 𝟙 _ ≫ t)
      (IsPullback.of_horiz_isIso .mk) (IsPullback.of_vert_isIso .mk)
      (IsPullback.of_vert_isIso .mk)
  have vert :=
    P.baseChangeIso_comp_vert'
      (u₀₁ := t') (f₀₂ := e.hom) (f₂₄ := l) (f₀₄ := l')
      (f₁₃ := 𝟙 _) (f₃₅ := r) (f₁₅ := r) (u₂₃ := 𝟙 _ ≫ t) (u₄₅ := b)
      (IsPullback.of_vert_isIso .mk) (by convert h₁; simp) h₂
  rw [horiz₂] at vert
  simp only [cat_nf] at vert
  conv_rhs at vert => enter [2,2,1]; rw [horiz₁]
  simp only [cat_nf] at vert
  simp only [P.baseChangeIso_unit_vert, P.baseChangeIso_unit_horiz,
    P.uComp'_id_r, P.vComp'_id_r, cat_nf, whisker_assoc, cancelIso] at vert
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, comp_whiskerRight,
    leftUnitor_inv_whiskerRight, Category.assoc, whiskerLeftIso_hom, whiskerLeft_comp,
    whiskerLeft_rightUnitor_inv, whiskerLeft_rightUnitor, leftUnitor_whiskerRight,
    pentagon_inv_assoc] at vert
  rw [vert]
  clear vert
  simp only [bicategoricalComp, BicategoricalCoherence.whiskerLeft_iso,
    BicategoricalCoherence.left'_iso, BicategoricalCoherence.refl_iso, Iso.refl_trans,
    whiskerLeftIso_hom, Iso.symm_hom, BicategoricalCoherence.whiskerRight_iso, whiskerRightIso_hom,
    Iso.refl_hom, whiskerRight_comp, id_whiskerRight, Category.id_comp, Iso.inv_hom_id,
    BicategoricalCoherence.assoc'_iso, BicategoricalCoherence.assoc_iso, Iso.trans_assoc,
    Iso.trans_hom, Category.comp_id, pentagon_hom_inv_inv_inv_inv, Category.assoc]
  simp_rw [← Category.assoc, cancel_mono, Category.assoc,
    reassoc_of% wl% associator_inv_naturality_right, reassoc_of% wl% whisker_exchange,
    cancelIso, rightUnitor_comp_inv_assoc, rightUnitor_comp_inv,
    cat_nf, cancelIso, rightUnitor_comp, cat_nf, cancelIso, associator_naturality_left_assoc,
    ← whisker_exchange_assoc, id_whiskerLeft, cat_nf, cancelIso, cancel_epi]
  slice_lhs 1 3 => equals 𝟙 _ => bicategory
  simp only [Category.id_comp, Category.assoc, pentagon_inv_inv_hom_inv_inv, id_whiskerLeft,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, Ψ_eq, Iso.trans_hom, Iso.symm_hom,
    whiskerRightIso_hom, comp_whiskerRight, leftUnitor_inv_whiskerRight, whiskerLeft_comp,
    cancel_epi]
  simp_rw [← Category.assoc, cancel_mono, Category.assoc]
  bicategory

end Adjunction

noncomputable section toPseudoFunctor

variable [Limits.HasPullbacks C]

abbrev obj' (x : EffBurnside C) : B := P.obj x.as.of

abbrev map {x y : EffBurnside C} (S : x ⟶ y) : P.obj' x ⟶ P.obj' y := P.v S.of.l ≫ P.u S.of.r

abbrev map₂ {x y : EffBurnside C} {S S' : x ⟶ y}
    (η : S ⟶ S') : P.map S ⟶ P.map S' :=
  letI e_iso : S.of.apex ≅ S'.of.apex := Spans.apexIso η.iso
  (P.vComp' e_iso.hom S'.of.l _).hom ▷ (P.u S.of.r) ≫
  (P.v S'.of.l ≫ P.v e_iso.hom) ◁ (P.uComp' e_iso.hom S'.of.r _).hom ≫
  (α_ _ _ _).hom ≫
  (P.v S'.of.l) ◁ (α_ (P.v e_iso.hom) (P.u e_iso.hom) (P.u S'.of.r)).inv ≫
  (P.v S'.of.l) ◁ (P.baseChangeEquivalenceOfIso e_iso).counit.hom ▷ (P.u S'.of.r) ≫
  (P.v S'.of.l) ◁ (λ_ (P.u S'.of.r)).hom

noncomputable abbrev mapId (x : EffBurnside C) : P.map (𝟙 x) ≅ 𝟙 (P.obj' x) :=
    (P.baseChangeEquivalenceOfIso (Iso.refl _)).counit

-- TODO: maybe 𝔯 and 𝔩 could be local notations instead?

/-- A shorthand for a kind of isomorphism that will show up a few times. -/
@[reducible]
def 𝔯 {x y z : EffBurnside C} (f : x ⟶ y) (g : y ⟶ z) :
    P.v (f.of ≫ g.of).l ≅ P.v f.of.l ≫ P.v (Spans.πₗ f.of g.of) :=
  P.vComp' (Spans.πₗ f.of g.of) f.of.l (f.of ≫ g.of).l

/-- A shorthand for a kind of isomorphism that will show up a few times. -/
@[reducible]
def 𝔩 {x y z : EffBurnside C} (f : x ⟶ y) (g : y ⟶ z) :
    P.u (f.of ≫ g.of).r ≅ P.u (Spans.πᵣ f.of g.of) ≫ P.u g.of.r :=
  P.uComp' (Spans.πᵣ f.of g.of) g.of.r (f.of ≫ g.of).r

/-- A shorthand for a morphism that we will be seeing a lot. -/
@[reducible]
def μ {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :
    P.map (S₁ ≫ S₂) ≅
    (P.v S₁.of.l ≫ P.v (Spans.πₗ S₁.of S₂.of)) ≫ P.u (Spans.πᵣ S₁.of S₂.of) ≫ P.u S₂.of.r :=
  whiskerRightIso (P.𝔯 S₁ S₂) _ ≪≫ whiskerLeftIso _ (P.𝔩 S₁ S₂)

lemma μ_hom {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :
    (P.μ S₁ S₂).hom = (P.𝔯 S₁ S₂).hom ▷ _ ≫ _ ◁ (P.𝔩 S₁ S₂).hom :=
  rfl

lemma μ_inv {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :
    (P.μ S₁ S₂).inv = _ ◁ (P.𝔩 S₁ S₂).inv ≫ (P.𝔯 S₁ S₂).inv ▷ _ :=
  rfl

lemma μ_hom' {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :
    (P.μ S₁ S₂).hom = _ ◁ (P.𝔩 S₁ S₂).hom ≫ (P.𝔯 S₁ S₂).hom ▷ _ := by
  rw [whisker_exchange]
  exact P.μ_hom _ _

lemma μ_inv' {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :
    (P.μ S₁ S₂).inv = (P.𝔯 S₁ S₂).inv ▷ _ ≫ _ ◁ (P.𝔩 S₁ S₂).inv := by
  rw [← whisker_exchange]
  exact P.μ_inv _ _

/-- A shorthand for a morphism that we will be seeing a lot. -/
abbrev Γ {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :=
  P.baseChangeIso (Spans.πₗ S₁.of S₂.of) (Spans.πᵣ S₁.of S₂.of) S₁.of.r S₂.of.l
    (IsPullback.of_isLimit (Spans.isLimitCompPullbackCone S₁.of S₂.of))

/-- The `mapComp` field of the to-be-defined pseudofunctor
`EffBurnside C ⥤ᵖ B` attached to `P : PseudofunctorCore C B` -/
noncomputable abbrev mapComp {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :
    P.map (S₁ ≫ S₂) ≅ P.map S₁ ≫ P.map S₂ :=
  (P.μ S₁ S₂) ≪⊗≫
    (whiskerLeftIso (P.v S₁.of.l) (whiskerRightIso (P.Γ S₁ S₂).symm (P.u S₂.of.r))) ≪⊗≫ .refl _

lemma mapComp_hom {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :
    (P.mapComp S₁ S₂).hom =
    (P.μ S₁ S₂).hom ⊗≫ (P.v S₁.of.l) ◁ (P.Γ S₁ S₂).inv ▷ (P.u S₂.of.r) ⊗≫ 𝟙 _ :=
  rfl

lemma mapComp_inv {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :
    (P.mapComp S₁ S₂).inv =
    𝟙 _ ⊗≫ (P.v S₁.of.l) ◁ (P.Γ S₁ S₂).hom ▷ (P.u S₂.of.r) ⊗≫ (P.μ S₁ S₂).inv := by
  dsimp [bicategoricalIso, mapComp, bicategoricalIsoComp]
  bicategory

lemma map₂_id {a b : EffBurnside C} (f : a ⟶ b) : P.map₂ (𝟙 f) = 𝟙 (P.map f) := by
  dsimp [map₂]
  rw [inv% P.baseChange_id_eq]
  simp only [cat_nf, cancelIso, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
    whiskerRightIso_hom, P.uComp'_id_r, P.vComp'_id_r]
  simp_rw [← reassoc_of% wl% associator_inv_naturality_middle, cancelIso,
    associator_naturality_middle_assoc,
    ← reassoc_of% wl% whisker_exchange, reassoc_of% wl% associator_inv_naturality_left,
    reassoc_of% wl% wr% whiskerRight_id, P.Ψ_inv_eq', cat_nf, cancelIso]
  bicategory

/-- A shorthand for the counit of the base change adjunction deduced by a 2-morphism in
`EffBurnside C`: having it as a standalone definition prevents some
unwanted unfoldings. -/
private def ε {c c' : EffBurnside C} {f g : c ⟶ c'} (η : f ⟶ g) :
    P.v (η.iso.hom.hom) ≫ P.u (η.iso.hom.hom) ≅ 𝟙 (P.obj g.of.apex) :=
  (P.baseChangeEquivalenceOfIso (Spans.apexIso η.iso)).counit

private lemma ε_hom_def {c c' : EffBurnside C} {f g : c ⟶ c'} (η : f ⟶ g) :
   (P.ε η).hom =
     (P.baseChangeIso η.iso.hom.hom η.iso.hom.hom (𝟙 _) (𝟙 _)
       (IsPullback.of_horiz_isIso .mk)).inv ≫ (P.Ψ _).inv := rfl

private lemma ε_inv_def {c c' : EffBurnside C} {f g : c ⟶ c'} (η : f ⟶ g) :
   (P.ε η).inv =
     (P.Ψ _).hom ≫ (P.baseChangeIso η.iso.hom.hom η.iso.hom.hom (𝟙 _) (𝟙 _)
       (IsPullback.of_horiz_isIso .mk)).hom := rfl

lemma map₂_comp {c c' : EffBurnside C} {f g h : c ⟶ c'} (η : f ⟶ g) (θ : g ⟶ h) :
    P.map₂ (η ≫ θ) = P.map₂ η ≫ P.map₂ θ := by
  dsimp [map₂]
  simp_rw [dsimp% P.baseChangeEquivalenceOfIso_counit_hom_comp
    (Spans.apexIso η.iso) (Spans.apexIso θ.iso) (hfg := rfl), ← ε_hom_def]
  simp only [comp_whiskerLeft, bicategoricalComp, whiskerRight_comp,
    BicategoricalCoherence.assoc_iso, BicategoricalCoherence.whiskerLeft_iso,
    BicategoricalCoherence.assoc'_iso, BicategoricalCoherence.whiskerRight_iso,
    BicategoricalCoherence.refl_iso, Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    Iso.refl_hom, id_whiskerRight, Category.id_comp, Iso.inv_hom_id, Iso.symm_hom,
    BicategoricalCoherence.left_iso, Iso.trans_refl, Category.assoc,
    pentagon_hom_hom_inv_hom_hom_assoc, comp_whiskerRight, whisker_assoc, leftUnitor_whiskerRight,
    whiskerLeft_comp, Iso.inv_hom_id_assoc, whiskerLeft_inv_hom_assoc]
  simp_rw [← Category.assoc, cancel_mono, Category.assoc]
  rotate_isos ← 1 0
  rotate_isos 0 3
  have :=
    (inv% P.vComp'₀₁₃_hom
      (f₀₁ := η.iso.hom.hom)
      (f₁₂ := θ.iso.hom.hom)
      (f₂₃ := h.of.l)
      (f₁₃ := g.of.l)
      (f := f.of.l)
      (f₀₂ := (η.iso.hom.hom ≫ θ.iso.hom.hom))
      (by simp) (by simp) (by simp))
  rw [this]
  simp only [comp_whiskerRight, whisker_assoc, Category.assoc, inv_hom_whiskerRight_assoc,
    Iso.inv_hom_id_assoc]
  simp_rw [← whiskerLeft_comp_assoc, ← pentagon_hom_inv_inv_inv_inv_assoc,
    ← associator_inv_naturality_left_assoc, whisker_exchange_assoc, whiskerLeft_comp_assoc,
    ← associator_naturality_middle_assoc]
  simp only [comp_whiskerLeft_symm_assoc, cancelIso, whisker_exchange, whisker_exchange_assoc]
  simp_rw [← whiskerLeft_comp, whiskerRight_comp_symm_assoc, cancelIso,
    ← leftUnitor_naturality, ← whisker_exchange_assoc]
  simp only [whiskerRight_comp, comp_whiskerLeft, Category.assoc, whiskerLeft_comp,
    comp_whiskerRight, pentagon_assoc, pentagon_hom_inv_inv_inv_inv_assoc,
    whiskerLeft_hom_inv_assoc, pentagon_hom_hom_inv_hom_hom_assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc]
  simp_rw [← Category.assoc, cancel_mono, Category.assoc]
  rotate_isos 5 0
  rotate_isos ← 0 6
  simp_rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, cancelIso]
  have :=
    (P.uComp'₀₁₃_hom
      (f₀₁ := η.iso.hom.hom)
      (f₁₂ := θ.iso.hom.hom)
      (f₂₃ := h.of.r)
      (f₁₃ := g.of.r)
      (f := f.of.r)
      (f₀₂ := (η.iso.hom.hom ≫ θ.iso.hom.hom))
      (by simp) (by simp) (by simp))
  simp only [this, whiskerLeft_comp, comp_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
    whiskerRight_comp, comp_whiskerRight, Iso.hom_inv_id_assoc,
    hom_inv_whiskerRight_whiskerRight_assoc, cancelIso, Category.comp_id]
  bicategory

end toPseudoFunctor

end PseudofunctorCore

end CategoryTheory.EffBurnside
