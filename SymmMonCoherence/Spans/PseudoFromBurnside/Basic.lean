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

/-! # Pseudofunctors from the effective Burnside (2,1)-category . -/

@[expose] public section

namespace CategoryTheory.EffBurnside

open Bicategory
universe w₁ v₁ v₂ u₁ u₂
variable (C : Type u₁) [Category.{v₁} C]

/-- A helper structure to construct pseudofunctors out of the effective Burnside
(2,1)-category of a category. This is essentially the data of two pseudofunctors
`l : LocallyDiscrete C ⥤ᵖ B` and `r : (LocallyDiscrete C)ᵒᵖ ⥤ᵖ B` that
 (definitionally) share the same action on objects, with the extra data of a natural
isomorphism `l e.hom ≅ r e.inv` when `e` is an isomorphism in `C` (which gives
rise to an adjoint equivalence) and the data of a
base change isomorphism  `l f ≫ r g ≅ r u ≫ l v` when
```
     u
 x ----> y
 |       |
v|       |f
 v       v
 z ----> t
     g
```
is a pullback square in `C`,
which must furthermore satisfies compatibilities with respect to pasting of squares. -/
structure PseudoFunctorCore (B : Type u₂) [Bicategory.{w₁, v₂} B] where
  /-- The action on objects. -/
  obj : C → B
  /-- The left action on morphism, it corresponds to the action of the pseudofunctor
  on spans of the form `inl.map _` -/
  l {x y : C} : (x ⟶ y) → (obj x ⟶ obj y)
  /-- The right action on morphism, it corresponds to the action of the pseudofunctor
  on spans of the form `inr.map _` -/
  r {x y : C} : (x ⟶ y) → (obj y ⟶ obj x)
  /-- The left structure isomorphism on identities. -/
  lId' {x : C} (f : x ⟶ x) (hf : f = 𝟙 x := by cat_disch) : l f ≅ 𝟙 (obj x)
  /-- The right structure isomorphism on identities. -/
  rId' {x : C} (f : x ⟶ x) (hf : f = 𝟙 x := by cat_disch) : r f ≅ 𝟙 (obj x)
  /-- The left structure isomorphism on compositions. -/
  lComp' {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (hfg : f ≫ g = h := by cat_disch) :
    l h ≅ l f ≫ l g
  /-- The right structure isomorphism on compositions. -/
  rComp' {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (hfg : f ≫ g = h := by cat_disch) :
    r h ≅ r g ≫ r f
  -- pseudofunctoriality of l
  l_associator {c₀ c₁ c₂ c₃ : C} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) (h : c₂ ⟶ c₃) :
      (lComp' (f ≫ g) h ((f ≫ g) ≫ h)).hom ≫
        (lComp' f g (f ≫ g)).hom ▷ l h ≫ (α_ (l f) (l g) (l h)).hom ≫
        l f ◁ (lComp' g h (g ≫ h)).inv ≫ (lComp' f (g ≫ h) (f ≫ g ≫ h)).inv =
      eqToHom (by simp) := by
    cat_disch
  l_left_unitor {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
      (lComp' (𝟙 c₀) f (𝟙 c₀ ≫ f)).hom ≫ (lId' (𝟙 c₀)).hom ▷ l f ≫ (λ_ (l f)).hom =
        eqToHom (by simp) := by
    cat_disch
  l_right_unitor {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
      (lComp' f (𝟙 c₁) (f ≫ 𝟙 c₁)).hom ≫ l f ◁ (lId' (𝟙 c₁)).hom ≫ (ρ_ (l f)).hom =
      eqToHom (by simp) := by
    cat_disch
  -- pseudofunctoriality of r
  -- the forms here are tailored for use in LocallyDiscrete.mkPseudofunctor
  r_associator {c₀ c₁ c₂ c₃ : C} (f : c₁ ⟶ c₀) (g : c₂ ⟶ c₁) (h : c₃ ⟶ c₂) :
      (rComp' h (g ≫ f) (h ≫ g ≫ f)).hom ≫ (rComp' g f (g ≫ f)).hom ▷ r h ≫
        (α_ (r f) (r g) (r h)).hom ≫
        r f ◁ (rComp' h g (h ≫ g)).inv ≫ (rComp' (h ≫ g) f ((h ≫ g) ≫ f)).inv =
      eqToHom (by simp) := by
    cat_disch
  r_left_unitor {c₀ c₁ : C} (f : c₁ ⟶ c₀) :
      (rComp' f (𝟙 c₀) (f ≫ 𝟙 c₀)).hom ≫ (rId' (𝟙 c₀)).hom ▷ r f ≫ (λ_ (r f)).hom =
      eqToHom (by simp) := by
    cat_disch
  r_right_unitor {c₀ c₁ : C} (f : c₁ ⟶ c₀) :
      (rComp' (𝟙 c₁) f (𝟙 c₁ ≫ f)).hom ≫ r f ◁ (rId' (𝟙 c₁)).hom ≫ (ρ_ (r f)).hom =
      eqToHom (by simp) := by
    cat_disch
  /-- The base change isomorphism on cartesian squares
  ```
      u
  x ----> y
  |       |
 v|       |f
  v       v
  z ----> t
      g
  ``` -/
  /- Note that if we were trying to define pseudofunctors out of the full bicategory of spans
  (rather than its pith), we would need to specify a base-change 2-morphism for every square, and
  not just pullback squares as the spans (Spans.inl _).map f and (Spans.inr _).map f
  are always adjoint to each other, but the data of this adjunction only
  lifts to the pith when `f` is an isomorphism in C (in this case, we will
  use this base change isomorphism to produce an isomorphism `l e.hom ≅ l e.inv`
  compatible with compositions and identities, see `isoOfIso` and related declarations below). -/
  baseChangeIso {x y z t : C} (u : x ⟶ y) (v : x ⟶ z) (f : y ⟶ t) (g : z ⟶ t)
    (S : IsPullback u v f g) :
    l f ≫ r g ≅ r u ≫ l v
  baseChange_unit_left {x y : C} (f : x ⟶ y) :
    (baseChangeIso f (𝟙 x) (𝟙 y) f (IsPullback.of_vert_isIso .mk)).hom =
    (lId' (𝟙 y)).hom ▷ r f ≫ (λ_ _).hom ≫ (ρ_ _).inv ≫ r f ◁ (lId' (𝟙 x)).inv
  baseChange_unit_right {x y : C} (f : x ⟶ y) :
    (baseChangeIso (𝟙 x) f f (𝟙 y) (IsPullback.of_horiz_isIso .mk)).hom =
    l f ◁ (rId' (𝟙 y)).hom ≫ (ρ_ _).hom  ≫ (λ_ _).inv ≫ (rId' (𝟙 x)).inv ▷ l f
  /-- Compatibility of the base change isomorphism with horizontal pasting of squares:
  ```
       u        f
   x ----> y ----> m
   |  S₁   |  S₂   |
  v|      h|      k|
   v       v       v
   z ----> t ----> n
       g        p
  ``` -/
  baseChange_comp_horiz {x y z t m n : C}
    {u : x ⟶ y} {v : x ⟶ z} {h : y ⟶ t} {g : z ⟶ t}
    {f : y ⟶ m} {k : m ⟶ n} {p : t ⟶ n}
    (S₁ : IsPullback u v h g) (S₂ : IsPullback f h k p) :
    (baseChangeIso (u ≫ f) v k (g ≫ p) (S₁.paste_horiz S₂)).hom =
      l k ◁ (rComp' g p (g ≫ p)).hom ≫
      (α_ (l k) (r p) (r g)).inv ≫
      (baseChangeIso f h k p S₂).hom ▷ r g ≫
      (α_ (r f) (l h) (r g)).hom ≫
      r f ◁ (baseChangeIso u v h g S₁).hom ≫
      (α_ (r f) (r u) (l v)).inv ≫
      (rComp' u f (u ≫ f)).inv ▷ l v
  /-- Compatibility of the base change isomorphism with vertical pasting of squares:
  ```
        u
   x ----> y
   |       |
  v|      f|
   v       v
   z ----> t
   |  g    |
  p|      h|
   v       v
   a ----> b
        k
  ``` -/
  baseChange_comp_vert {x y z t a b : C}
    {u : x ⟶ y} {v : x ⟶ z} {f : y ⟶ t} {g : z ⟶ t}
    {p : z ⟶ a} {h : t ⟶ b} {k : a ⟶ b}
    (S₁ : IsPullback u v f g) (S₂ : IsPullback g p h k) :
    (baseChangeIso u (v ≫ p) (f ≫ h) k (S₁.paste_vert S₂)).hom =
      (lComp' f h (f ≫ h)).hom ▷ r k ≫
      (α_ (l f) (l h) (r k)).hom ≫
      l f ◁ (baseChangeIso g p h k S₂).hom ≫
      (α_ (l f) (r g) (l p)).inv ≫
      (baseChangeIso u v f g S₁).hom ▷ l p ≫
      (α_ (r u) (l v) (l p)).hom ≫
      r u ◁ (lComp' v p (v ≫ p)).inv

namespace PseudoFunctorCore

variable {C} {B : Type u₂} [Bicategory.{w₁, v₂} B] (P : PseudoFunctorCore C B)

/- It is useful to bundle `r` and `l` as pseudofunctors now so that we can apply some general
results about pseudofunctors from a strict bicategory to them within the proofs in
toPseudofunctor, but we keep most of this private, as they become
useless once we have.
Even as abbrev, the definitional equality
`lPseudofunctor.obj = PseudoFunctorCore.rPseudofunctor.obj` does
not hold at reducible transparency. -/

/-- Bundling the data in `l` and related fields as a pseudofunctor
`LocallyDiscrete C ⥤ᵖ B`. -/
private abbrev lPseudofunctor :
    LocallyDiscrete C ⥤ᵖ B :=
  LocallyDiscrete.mkPseudofunctor (B₀ := C) (C := B)
    (obj := P.obj)
    (map := P.l)
    (mapId := fun x ↦ (P.lId' (𝟙 x)))
    (mapComp := fun f g ↦ P.lComp' f g (f ≫ g))
    (map₂_associator := P.l_associator)
    (map₂_left_unitor := P.l_left_unitor)
    (map₂_right_unitor := P.l_right_unitor)

/-- Bundling the data in `r` and related fields as a pseudofunctor
`(LocallyDiscrete C)ᵒᵖ ⥤ᵖ B`. -/
private abbrev rPseudofunctor :
    (LocallyDiscrete Cᵒᵖ) ⥤ᵖ B :=
  LocallyDiscrete.mkPseudofunctor (B₀ := Cᵒᵖ) (C := B)
    (obj := fun x ↦ P.obj x.unop)
    (map := fun {x y} f ↦ P.r f.unop)
    (mapId := fun x ↦ P.rId' (𝟙 x.unop))
    (mapComp := fun {x y z} f g ↦ P.rComp' g.unop f.unop _ rfl)
    (map₂_associator := by
      intros
      simpa using P.r_associator _ _ _)
    (map₂_left_unitor := by
      intros
      simpa using P.r_left_unitor _)
    (map₂_right_unitor := by
      intros
      simpa using P.r_right_unitor _)

private lemma lPseudofunctor_obj (x : C) :
    P.lPseudofunctor.obj ⟨x⟩ = P.obj x := rfl

private lemma lPseudofunctor_map
    {x y : C} (f : x ⟶ y) :
    P.lPseudofunctor.map f.toLoc = P.l f :=
  rfl

private lemma lPseudofunctor_mapId'
    {x : C} (f : x ⟶ x) (hf : f = 𝟙 x := by cat_disch) :
    P.lPseudofunctor.mapId' f.toLoc = P.lId' f hf := by
  subst hf
  simp [Pseudofunctor.mapId']

private lemma lPseudofunctor_mapComp'
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (hfg : f ≫ g = h := by cat_disch) :
    P.lPseudofunctor.mapComp' f.toLoc g.toLoc h.toLoc = P.lComp' f g h hfg := by
  subst hfg
  simp [Pseudofunctor.mapComp']

private lemma rPseudofunctor_obj (x : C) :
    P.rPseudofunctor.obj ⟨Opposite.op x⟩ = P.obj x := rfl

private lemma rPseudofunctor_map
    {x y : C} (f : x ⟶ y) :
    P.rPseudofunctor.map f.op.toLoc = P.r f :=
  rfl

private lemma rPseudofunctor_mapId'
    {x : C} (f : x ⟶ x) (hf : f = 𝟙 x := by cat_disch) :
    P.rPseudofunctor.mapId' f.op.toLoc = P.rId' f hf := by
  subst hf
  simp [Pseudofunctor.mapId']

private lemma rPseudofunctor_mapComp'
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (hfg : f ≫ g = h := by cat_disch) :
    P.rPseudofunctor.mapComp' g.op.toLoc f.op.toLoc h.op.toLoc = P.rComp' f g h hfg := by
  subst hfg
  simp [Pseudofunctor.mapComp']

/-- This is a version of `Pseudofunctor.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom` for
`lComp'`. -/
@[reassoc]
private lemma lComp'_associativity'
    {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁)
    (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃) (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f : c₀ ⟶ c₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (hf : f₀₁ ≫ f₁₃ = f) :
  (P.lComp' f₀₁ f₁₃ f).hom ≫ P.l f₀₁ ◁ (P.lComp' f₁₂ f₂₃ f₁₃).hom =
  (P.lComp' f₀₂ f₂₃ f).hom ≫
    (P.lComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ P.l f₂₃ ≫ (α_ _ _ _).hom := by
  simp only [← lPseudofunctor_mapComp',
    ← lPseudofunctor_obj, ← lPseudofunctor_map]
  exact P.lPseudofunctor.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom _ _ _ _ _ _ _
    (by grind) (by grind)

@[reassoc]
private lemma lComp'_id_l
    {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    P.lComp' f (𝟙 c₁) f (by grind) = (ρ_ _).symm ≪≫ whiskerLeftIso _ (P.lId' (𝟙 c₁)).symm := by
  simp only [← lPseudofunctor_mapComp', ← lPseudofunctor_mapId',
    ← lPseudofunctor_obj, ← lPseudofunctor_map]
  simpa [← lPseudofunctor_mapId'] using P.lPseudofunctor.mapComp'_comp_id f.toLoc

@[reassoc]
private lemma lComp'_id_r
    {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    P.lComp' (𝟙 c₀) f f (by grind) = (λ_ _).symm ≪≫ whiskerRightIso (P.lId' (𝟙 c₀)).symm _ := by
  simp only [← lPseudofunctor_mapComp', ← lPseudofunctor_mapId',
    ← lPseudofunctor_obj, ← lPseudofunctor_map]
  simpa [← lPseudofunctor_mapId'] using P.lPseudofunctor.mapComp'_id_comp f.toLoc

/-- This is a version of `Pseudofunctor.mapComp'₀₁₃_hom` for
`lComp'`. -/
@[reassoc]
private lemma lComp'₀₁₃_hom
    {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁)
    (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃) (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f : c₀ ⟶ c₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (hf : f₀₁ ≫ f₁₃ = f) :
  (P.lComp' f₀₁ f₁₃ f).hom =
  (P.lComp' f₀₂ f₂₃ f).hom ≫ (P.lComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ P.l f₂₃ ≫
    (α_ _ _ _).hom ≫ P.l f₀₁ ◁ (P.lComp' f₁₂ f₂₃ f₁₃).inv := by
  simp only [← lPseudofunctor_mapComp',
    ← lPseudofunctor_obj, ← lPseudofunctor_map]
  exact P.lPseudofunctor.mapComp'₀₁₃_hom _ _ _ _ _ _ _
    (by grind) (by grind)

/-- This is a version of `Pseudofunctor.mapComp'₀₂₃_hom` for
`lComp'`. -/
@[reassoc]
private lemma lComp'₀₂₃_hom
    {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁)
    (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃) (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f : c₀ ⟶ c₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (hf : f₀₁ ≫ f₁₃ = f) :
  (P.lComp' f₀₂ f₂₃ f).hom =
  (P.lComp' f₀₁ f₁₃ f).hom ≫ P.l f₀₁ ◁ (P.lComp' f₁₂ f₂₃ f₁₃).hom ≫
    (α_ _ _ _).inv ≫ (P.lComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ P.l f₂₃ := by
  simp only [← lPseudofunctor_mapComp',
    ← lPseudofunctor_obj, ← lPseudofunctor_map]
  exact P.lPseudofunctor.mapComp'₀₂₃_hom _ _ _ _ _ _ _
    (by grind) (by grind)

@[reassoc]
private lemma rComp'_id_l
    {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    P.rComp' f (𝟙 c₁) f (by grind) = (λ_ _).symm ≪≫ whiskerRightIso (P.rId' (𝟙 c₁)).symm _ := by
  simp only [← rPseudofunctor_mapComp', ← rPseudofunctor_mapId',
    ← rPseudofunctor_obj, ← rPseudofunctor_map]
  simpa [← rPseudofunctor_mapId'] using
    P.rPseudofunctor.mapComp'_id_comp f.op.toLoc

@[reassoc]
private lemma rComp'_id_r
    {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    P.rComp' (𝟙 c₀) f f (by grind) = (ρ_ _).symm ≪≫ whiskerLeftIso _ (P.rId' (𝟙 c₀)).symm := by
  simp only [← rPseudofunctor_mapComp', ← rPseudofunctor_mapId',
    ← rPseudofunctor_obj, ← rPseudofunctor_map]
  simpa [← rPseudofunctor_mapId'] using
    P.rPseudofunctor.mapComp'_comp_id f.op.toLoc

/-- This is a version of `Pseudofunctor.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom` for
`rComp'`. -/
@[reassoc]
private lemma rComp'_associativity'
    {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁)
    (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃) (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f : c₀ ⟶ c₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (hf : f₀₁ ≫ f₁₃ = f) :
  (P.rComp' f₀₂ f₂₃ f).hom ≫ P.r f₂₃ ◁ (P.rComp' f₀₁ f₁₂ f₀₂ h₀₂).hom =
  (P.rComp' f₀₁ f₁₃ f).hom ≫
    (P.rComp' f₁₂ f₂₃ f₁₃).hom ▷ P.r f₀₁ ≫ (α_ _ _ _).hom := by
  simp only [← rPseudofunctor_mapComp',
    ← rPseudofunctor_obj, ← rPseudofunctor_map]
  exact P.rPseudofunctor.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom _ _ _ _ _ _ _
    (by grind) (by grind)

/-- This is a version of `Pseudofunctor.mapComp'₀₁₃_hom` for
`rComp'`. -/
@[reassoc]
private lemma rComp'₀₁₃_hom
    {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁)
    (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃) (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f : c₀ ⟶ c₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (hf : f₀₁ ≫ f₁₃ = f) :
  (P.rComp' f₀₁ f₁₃ f).hom =
  (P.rComp' f₀₂ f₂₃ f).hom ≫ P.r f₂₃ ◁ (P.rComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ≫
    (α_ _ _ _).inv ≫ (P.rComp' f₁₂ f₂₃ f₁₃).inv ▷ P.r f₀₁ := by
  simp only [← rPseudofunctor_mapComp',
    ← rPseudofunctor_obj, ← rPseudofunctor_map]
  exact P.rPseudofunctor.mapComp'₀₂₃_hom _ _ _ _ _ _ _
    (by grind) (by grind)

/-- This is a version of `Pseudofunctor.mapComp'₀₁₃_hom` for
`rComp'`. -/
@[reassoc]
private lemma rComp'₀₂₃_hom
    {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁)
    (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃) (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f : c₀ ⟶ c₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (hf : f₀₁ ≫ f₁₃ = f) :
  (P.rComp' f₀₂ f₂₃ f).hom =
  (P.rComp' f₀₁ f₁₃ f).hom ≫ (P.rComp' f₁₂ f₂₃ f₁₃).hom ▷ P.r f₀₁ ≫
    (α_ _ _ _).hom ≫ P.r f₂₃ ◁ (P.rComp' f₀₁ f₁₂ f₀₂ h₀₂).inv := by
  simp only [← rPseudofunctor_mapComp',
    ← rPseudofunctor_obj, ← rPseudofunctor_map]
  exact P.rPseudofunctor.mapComp'₀₁₃_hom _ _ _ _ _ _ _
    (by grind) (by grind)

-- TODO better name
private lemma baseChange_id_eq (x : C) :
    (P.baseChangeIso (𝟙 x) (𝟙 x) (𝟙 x) (𝟙 x) (IsPullback.of_horiz_isIso .mk)).hom =
      (P.lId' (𝟙 x)).hom ▷ P.r (𝟙 x) ≫ (λ_ _).hom ≫ (P.rId' (𝟙 x)).hom ≫
      (P.rId' (𝟙 x)).inv ≫ (ρ_ _).inv ≫ P.r (𝟙 x) ◁ (P.lId' (𝟙 x)).inv := by
  simp [P.baseChange_unit_left (𝟙 x)]

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
      P.l g₂ ◁ (P.rComp' f₃₄ f₄₅ f₃₅ hf').hom ≫
      (α_ (P.l g₂) (P.r f₄₅) (P.r f₃₄)).inv ≫
      (P.baseChangeIso f₁₂ g₁ g₂ f₄₅ S₂).hom ▷ P.r f₃₄ ≫
      (α_ (P.r f₁₂) (P.l g₁) (P.r f₃₄)).hom ≫
      P.r f₁₂ ◁ (P.baseChangeIso f₀₁ g₀ g₁ f₃₄ S₁).hom ≫
      (α_ (P.r f₁₂) (P.r f₀₁) (P.l g₀)).inv ≫
      (P.rComp' f₀₁ f₁₂ f₀₂ hf).inv ▷ P.l g₀ := by
  subst_vars
  apply P.baseChange_comp_horiz

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
      (P.lComp' f₁₃ f₃₅ f₁₅ hh).hom ▷ P.r u₄₅ ≫
      (α_ (P.l f₁₃) (P.l f₃₅) (P.r u₄₅)).hom ≫
      P.l f₁₃ ◁ (P.baseChangeIso u₂₃ f₂₄ f₃₅ u₄₅ S₂).hom ≫
      (α_ (P.l f₁₃) (P.r u₂₃) (P.l f₂₄)).inv ≫
      (P.baseChangeIso u₀₁ f₀₂ f₁₃ u₂₃ S₁).hom ▷ P.l f₂₄ ≫
      (α_ (P.r u₀₁) (P.l f₀₂) (P.l f₂₄)).hom ≫
      P.r u₀₁ ◁ (P.lComp' f₀₂ f₂₄ f₀₄ hv).inv := by
  subst_vars
  apply P.baseChange_comp_vert

/-- The interchange law for pasting of squares.
Parameters are labelled according to their source/targets.
There are extra parameters for better control of the type of morphisms that
appears.

```
        f₀₁      f₁₂
    c₀------> c₁ -----> c₂
    |         |         |
    | f₀₃     | f₁₄     | f₂₅
    |         |         |
    v   f₃₄   v   f₄₅   v
    c₃------> c₄------> c₅
    |         |         |
    | f₃₆     | f₄₇     | f₅₈
    |         |         |
    v   f₆₇   v   f₇₈   v
    c₆------> c₇------> c₈

```
-/
private lemma baseChangeIso_interchange
    {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : C}
    -- horizontal morphisms
    (f₀₁ : c₀ ⟶ c₁) (f₁₂ : c₁ ⟶ c₂) (f₀₂ : c₀ ⟶ c₂)
    (f₃₄ : c₃ ⟶ c₄) (f₄₅ : c₄ ⟶ c₅) (f₃₅ : c₃ ⟶ c₅)
    (f₆₇ : c₆ ⟶ c₇) (f₇₈ : c₇ ⟶ c₈) (f₆₈ : c₆ ⟶ c₈)
    -- verticalrizontal morphisms
    (f₀₃ : c₀ ⟶ c₃) (f₁₄ : c₁ ⟶ c₄) (f₂₅ : c₂ ⟶ c₅)
    (f₃₆ : c₃ ⟶ c₆) (f₄₇ : c₄ ⟶ c₇) (f₅₈ : c₅ ⟶ c₈)
    (f₀₆ : c₀ ⟶ c₆) (f₁₇ : c₁ ⟶ c₇) (f₂₈ : c₂ ⟶ c₈)
    -- Pullbacks
    (top_left : IsPullback f₀₁ f₀₃ f₁₄ f₃₄) (top_right : IsPullback f₁₂ f₁₄ f₂₅ f₄₅)
    (bot_left : IsPullback f₃₄ f₃₆ f₄₇ f₆₇) (bot_right : IsPullback f₄₅ f₄₇ f₅₈ f₇₈)
    -- horizontal composites
    (h₀₁₂ : f₀₁ ≫ f₁₂ = f₀₂ := by cat_disch)
    (h₃₄₅ : f₃₄ ≫ f₄₅ = f₃₅ := by cat_disch)
    (h₆₇₈ : f₆₇ ≫ f₇₈ = f₆₈ := by cat_disch)
    -- vertical composites
    (h₀₃₆ : f₀₃ ≫ f₃₆ = f₀₆ := by cat_disch)
    (h₁₄₇ : f₁₄ ≫ f₄₇ = f₁₇ := by cat_disch)
    (h₂₅₈ : f₂₅ ≫ f₅₈ = f₂₈ := by cat_disch) :
    /- LHS is the simp NF of pasting vertically the horizontal
    compositions of the two squares. RHS is the result of
    pasting horizontally the vertical compositions. -/
  (P.lComp' f₂₅ f₅₈ f₂₈ h₂₅₈).hom ▷ P.r f₆₈ ≫
    (α_ (P.l f₂₅) (P.l f₅₈) (P.r f₆₈)).hom ≫
    P.l f₂₅ ◁ P.l f₅₈ ◁ (P.rComp' f₆₇ f₇₈ f₆₈ h₆₇₈).hom ≫
    P.l f₂₅ ◁ (α_ (P.l f₅₈) (P.r f₇₈) (P.r f₆₇)).inv ≫
    P.l f₂₅ ◁ (P.baseChangeIso f₄₅ f₄₇ f₅₈ f₇₈ bot_right).hom ▷ P.r f₆₇ ≫
    P.l f₂₅ ◁ (α_ (P.r f₄₅) (P.l f₄₇) (P.r f₆₇)).hom ≫
    P.l f₂₅ ◁ P.r f₄₅ ◁ (P.baseChangeIso f₃₄ f₃₆ f₄₇ f₆₇ bot_left).hom ≫
    (α_ (P.l f₂₅) (P.r f₄₅) (P.r f₃₄ ≫ P.l f₃₆)).inv ≫
    (α_ (P.l f₂₅ ≫ P.r f₄₅) (P.r f₃₄) (P.l f₃₆)).inv ≫
    (P.baseChangeIso f₁₂ f₁₄ f₂₅ f₄₅ top_right).hom ▷ P.r f₃₄ ▷ P.l f₃₆ ≫
    (α_ (P.r f₁₂) (P.l f₁₄) (P.r f₃₄)).hom ▷ P.l f₃₆ ≫
    (α_ (P.r f₁₂) (P.l f₁₄ ≫ P.r f₃₄) (P.l f₃₆)).hom ≫
    P.r f₁₂ ◁ (P.baseChangeIso f₀₁ f₀₃ f₁₄ f₃₄ top_left).hom ▷ P.l f₃₆ ≫
    (α_ (P.r f₁₂) (P.r f₀₁ ≫ P.l f₀₃) (P.l f₃₆)).inv ≫
    (α_ (P.r f₁₂) (P.r f₀₁) (P.l f₀₃)).inv ▷ P.l f₃₆ ≫
    (P.rComp' f₀₁ f₁₂ f₀₂ h₀₁₂).inv ▷ P.l f₀₃ ▷ P.l f₃₆ ≫
    (α_ (P.r f₀₂) (P.l f₀₃) (P.l f₃₆)).hom ≫
    P.r f₀₂ ◁ (P.lComp' f₀₃ f₃₆ f₀₆ h₀₃₆).inv =
  P.l f₂₈ ◁ (P.rComp' f₆₇ f₇₈ f₆₈ h₆₇₈).hom ≫
    (α_ (P.l f₂₈) (P.r f₇₈) (P.r f₆₇)).inv ≫
    (P.lComp' f₂₅ f₅₈ f₂₈ h₂₅₈).hom ▷ P.r f₇₈ ▷ P.r f₆₇ ≫
    (α_ (P.l f₂₅) (P.l f₅₈) (P.r f₇₈)).hom ▷ P.r f₆₇ ≫
    (α_ (P.l f₂₅) (P.l f₅₈ ≫ P.r f₇₈) (P.r f₆₇)).hom ≫
    P.l f₂₅ ◁ (P.baseChangeIso f₄₅ f₄₇ f₅₈ f₇₈ bot_right).hom ▷ P.r f₆₇ ≫
    (α_ (P.l f₂₅) (P.r f₄₅ ≫ P.l f₄₇) (P.r f₆₇)).inv ≫
    (α_ (P.l f₂₅) (P.r f₄₅) (P.l f₄₇)).inv ▷ P.r f₆₇ ≫
    (P.baseChangeIso f₁₂ f₁₄ f₂₅ f₄₅ top_right).hom ▷ P.l f₄₇ ▷ P.r f₆₇ ≫
    (α_ (P.r f₁₂ ≫ P.l f₁₄) (P.l f₄₇) (P.r f₆₇)).hom ≫
    (α_ (P.r f₁₂) (P.l f₁₄) (P.l f₄₇ ≫ P.r f₆₇)).hom ≫
    P.r f₁₂ ◁ P.l f₁₄ ◁ (P.baseChangeIso f₃₄ f₃₆ f₄₇ f₆₇ bot_left).hom ≫
    P.r f₁₂ ◁ (α_ (P.l f₁₄) (P.r f₃₄) (P.l f₃₆)).inv ≫
    P.r f₁₂ ◁ (P.baseChangeIso f₀₁ f₀₃ f₁₄ f₃₄ top_left).hom ▷ P.l f₃₆ ≫
    P.r f₁₂ ◁ (α_ (P.r f₀₁) (P.l f₀₃) (P.l f₃₆)).hom ≫
    P.r f₁₂ ◁ P.r f₀₁ ◁ (P.lComp' f₀₃ f₃₆ f₀₆ h₀₃₆).inv ≫
    (α_ (P.r f₁₂) (P.r f₀₁) (P.l f₀₆)).inv ≫
    (P.rComp' f₀₁ f₁₂ f₀₂ h₀₁₂).inv ▷ P.l f₀₆ := by
  have bot : IsPullback f₃₅ f₃₆ f₅₈ f₆₈ := by
    subst_vars
    apply IsPullback.paste_horiz bot_left bot_right
  have top : IsPullback f₀₂ f₀₃ f₂₅ f₃₅ := by
    subst_vars
    apply IsPullback.paste_horiz top_left top_right
  have left : IsPullback f₀₁ f₀₆ f₁₇ f₆₇ := by
    subst_vars
    apply IsPullback.paste_vert top_left bot_left
  have right : IsPullback f₁₂ f₁₇ f₂₈ f₇₈ := by
    subst_vars
    apply IsPullback.paste_vert top_right bot_right
  have total : IsPullback f₀₂ f₀₆ f₂₈ f₆₈ := by
    subst_vars
    apply IsPullback.paste_horiz left right
  have hcomp_top :=
    P.baseChangeIso_comp_horiz' _ _ _ _ _ _ _ _ _ top_left top_right top h₀₁₂ h₃₄₅
  have hcomp_bot :=
    P.baseChangeIso_comp_horiz' _ _ _ _ _ _ _ _ _ bot_left bot_right bot h₃₄₅ h₆₇₈
  have vcomp_hcomp :=
    P.baseChangeIso_comp_vert' _ _ _ _ _ _ _ _ _ top bot total (by grind) (by grind)
  have vcomp_left :=
    P.baseChangeIso_comp_vert' _ _ _ _ _ _ _ _ _ top_left bot_left left h₀₃₆ h₁₄₇
  have vcomp_right :=
    P.baseChangeIso_comp_vert' _ _ _ _ _ _ _ _ _ top_right bot_right right h₁₄₇ h₂₅₈
  have hcomp_vcomp :=
    P.baseChangeIso_comp_horiz' _ _ _ _ _ _ _ _ _ left right total (by grind) (by grind)
  rw [reassoc_of% wl% hcomp_bot, reassoc_of% wr% hcomp_top] at vcomp_hcomp
  rw [reassoc_of% wl% vcomp_left, reassoc_of% wr% vcomp_right] at hcomp_vcomp
  rw [hcomp_vcomp] at vcomp_hcomp
  simpa using vcomp_hcomp.symm

  -- rw [reassoc_of% wl% hcomp_bot, reassoc_of% wr% hcomp_top,
  --   reassoc_of% wl% vcomp_left, reassoc_of% wr% vcomp_right] at vcomp_hcomp
  -- simpa using vcomp_hcomp

section Adjunction

-- syntax (name := comp2) (priority := high) term:81
--   ppSpace ppRealGroup("⊸" ppHardSpace ppDedent(term:80)) : term
-- macro_rules (kind := comp2) | `($a ⊸ $b) => `(CategoryStruct.comp $a $b)
-- @[app_unexpander CategoryStruct.comp] meta def unexpandComp : Lean.PrettyPrinter.Unexpander
--   | `($_ $a $b) => `($a ⊸ $b)
--   | _ => throw ()
--
section Ψ

/-- A shorthand for the isomorphism 𝟙 (P.obj z) ≅ P.l (𝟙 z) ≫ P.r (𝟙 z)
coming from unitality of the pseudofunctors. We’ll be seeing this
composition a lot, so it’s beter to give it a name. -/
def Ψ (z : C) :
    𝟙 (P.obj z) ≅ P.l (𝟙 z) ≫ P.r (𝟙 z) :=
    (P.lId' (𝟙 _)).symm ≪≫ (ρ_ _).symm ≪≫ whiskerLeftIso _ (P.rId' (𝟙 _)).symm

/-- A shorthand for the isomorphism 𝟙 (P.obj z) ≅ P.r (𝟙 z) ≫ P.l (𝟙 z)
coming from unitality of the pseudofunctors. We’ll be seeing this
composition a lot, so it’s beter to give it a name. -/
def Ψ' (z : C) :
    𝟙 (P.obj z) ≅ P.r (𝟙 z) ≫ P.l (𝟙 z) :=
    (P.rId' (𝟙 _)).symm ≪≫ (ρ_ _).symm ≪≫ whiskerLeftIso _ (P.lId' (𝟙 _)).symm

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

/-- The square

<MISSING DIAGRAM>

commutes. -/
@[reassoc]
lemma Ψ_eq (z : C) :
    P.Ψ z =
    (P.rId' (𝟙 _)).symm ≪≫ (λ_ _).symm ≪≫ whiskerRightIso (P.lId' (𝟙 _)).symm _ := by
  ext
  dsimp [Ψ]
  rotate_isos 0 1
  simp [whisker_exchange]

@[reassoc]
lemma Ψ_hom_eq (z : C) :
    (P.Ψ z).hom =
    (P.lId' (𝟙 z)).inv ≫ (ρ_ (P.l (𝟙 z))).inv ≫ P.l (𝟙 z) ◁ (P.rId' (𝟙 z)).inv := by
  dsimp [Ψ]

@[reassoc]
lemma Ψ_inv_eq (z : C) :
    (P.Ψ z).inv =
    P.l (𝟙 z) ◁ (P.rId' (𝟙 z)).hom ≫ (ρ_ (P.l (𝟙 z))).hom ≫ (P.lId' (𝟙 z)).hom := by
  simp [Ψ]

@[reassoc]
lemma Ψ_hom_eq' (z : C) :
    (P.Ψ z).hom = (P.rId' (𝟙 z)).inv ≫ (λ_ _).inv ≫ (P.lId' (𝟙 z)).inv ▷ P.r (𝟙 z) :=
  congr($(P.Ψ_eq z).hom)

@[reassoc]
lemma Ψ_inv_eq' (z : C) :
    (P.Ψ z).inv =
    (P.lId' (𝟙 z)).hom ▷ P.r (𝟙 z) ≫ (λ_ (P.r (𝟙 z))).hom ≫ (P.rId' (𝟙 z)).hom := by
  simpa using congr($(P.Ψ_eq z).inv)

/-- The square

<MISSING DIAGRAM>

commutes. -/
@[reassoc]
lemma Ψ'_eq (z : C) :
    P.Ψ' z =
    (P.lId' (𝟙 _)).symm ≪≫ (λ_ _).symm ≪≫ whiskerRightIso (P.rId' (𝟙 _)).symm _ := by
  ext
  dsimp [Ψ']
  rotate_isos 0 1
  simp [whisker_exchange]

@[reassoc]
lemma Ψ'_hom_eq (z : C) :
    (P.Ψ' z).hom = (P.rId' (𝟙 z)).inv ≫ (ρ_ (P.r (𝟙 z))).inv ≫ P.r (𝟙 z) ◁ (P.lId' (𝟙 z)).inv := by
  dsimp [Ψ']

@[reassoc]
lemma Ψ'_inv_eq (z : C) :
    (P.Ψ' z).inv = P.r (𝟙 z) ◁ (P.lId' (𝟙 z)).hom ≫ (ρ_ (P.r (𝟙 z))).hom ≫ (P.rId' (𝟙 z)).hom := by
  simp [Ψ']

@[reassoc]
lemma Ψ'_hom_eq' (z : C) :
    (P.Ψ' z).hom = (P.lId' (𝟙 z)).inv ≫ (λ_ _).inv ≫ (P.rId' (𝟙 z)).inv ▷ _ :=
  congr($(P.Ψ'_eq z).hom)

@[reassoc]
lemma Ψ'_inv_eq' (z : C) :
    (P.Ψ' z).inv = (P.rId' (𝟙 z)).hom ▷ P.l (𝟙 z) ≫ (λ_ (P.l (𝟙 z))).hom ≫ (P.lId' (𝟙 z)).hom := by
  simpa using congr($(P.Ψ'_eq z).inv)

end Ψ

section

variable {c₀ c₁ : C} (e : c₀ ≅ c₁)

/- We are intentionally not making some of the lemma simp so that we don’t end up with expressions
that are too big. For the same reason, these are `defs` and not abbrev so that we have
more control on wether or not they unfold. -/

/- Shorthand of the unit of the equivalence `P.obj c₀ ≌ P.obj c₁` induced by `e` via `P.l`. -/
def η_l : 𝟙 (P.obj c₀) ≅ P.l e.hom ≫ P.l e.inv := (P.lId' (𝟙 c₀)).symm ≪≫ P.lComp' e.hom e.inv _

lemma η_l_hom : (P.η_l e).hom = (P.lId' (𝟙 c₀)).inv ≫ (P.lComp' e.hom e.inv _).hom := rfl
lemma η_l_inv : (P.η_l e).inv =  (P.lComp' e.hom e.inv _).inv ≫ (P.lId' (𝟙 c₀)).hom := rfl

/- Shorthand of the counit of the equivalence `P.obj c₀ ≌ P.obj c₁` induced by `e` via `P.l`. -/
def ε_l : P.l e.inv ≫ P.l e.hom ≅ 𝟙 (P.obj c₁) := (P.lComp' e.inv e.hom _).symm ≪≫ P.lId' (𝟙 _)

lemma ε_l_hom : (P.ε_l e).hom = (P.lComp' e.inv e.hom _).inv ≫ (P.lId' (𝟙 _)).hom := rfl
lemma ε_l_inv : (P.ε_l e).inv = (P.lId' (𝟙 _)).inv ≫ (P.lComp' e.inv e.hom _).hom := rfl

/- Shorthand of the unit of the equivalence `P.obj c₁ ≌ P.obj c₀` induced by `e` via `P.r`. -/
def η_r : 𝟙 (P.obj c₁) ≅ P.r e.hom ≫ P.r e.inv := (P.rId' (𝟙 c₁)).symm ≪≫ P.rComp' e.inv e.hom _

lemma η_r_hom : (P.η_r e).hom = (P.rId' (𝟙 c₁)).inv ≫ (P.rComp' e.inv e.hom _).hom := rfl
lemma η_r_inv : (P.η_r e).inv = (P.rComp' e.inv e.hom _).inv ≫ (P.rId' (𝟙 c₁)).hom := rfl

/- Shorthand of the counit of the equivalence `P.obj c₁ ≌ P.obj c₀` induced by `e` via `P.r`. -/
def ε_r : P.r e.inv ≫ P.r e.hom ≅ 𝟙 (P.obj c₀) := (P.rComp' e.hom e.inv _).symm ≪≫ P.rId' (𝟙 _)

lemma ε_r_hom : (P.ε_r e).hom = (P.rComp' e.hom e.inv _).inv ≫ (P.rId' (𝟙 _)).hom := rfl
lemma ε_r_inv : (P.ε_r e).inv = (P.rId' (𝟙 _)).inv ≫ (P.rComp' e.hom e.inv _).hom := rfl

end
-- syntax (name := comp2) (priority := high) term:81
--   ppSpace ppRealGroup("⊚≫" ppHardSpace ppDedent(term:80)) : term
-- macro_rules (kind := comp2) | `($a ⊚≫ $b) => `(CategoryStruct.comp $a $b)
-- @[app_unexpander CategoryStruct.comp] meta def unexpandComp : Lean.PrettyPrinter.Unexpander
--   | `($_ $a $b) => `($a ⊚≫ $b)
--   | _ => throw ()
-- syntax (name := wl2) (priority := high) term:81
--   ppSpace ppRealGroup("⊚◁" ppHardSpace ppDedent(term:80)) : term
-- macro_rules (kind := wl2) | `($a ⊚◁ $b) => `(Bicategory.whiskerLeft $a $b)
-- @[app_unexpander Bicategory.whiskerLeft] meta def unexpandwl2 : Lean.PrettyPrinter.Unexpander
--   | `($_ $a $b) => `($a ⊚◁ $b)
--   | _ => throw ()
--
-- syntax (name := wl3) (priority := high) term:80
--   ppSpace ppRealGroup("⊚▷" ppHardSpace ppDedent(term:81)) : term
-- macro_rules (kind := wl3) | `($a ⊚▷ $b) => `(Bicategory.whiskerRight $a $b)
-- @[app_unexpander Bicategory.whiskerRight] meta def unexpandwl3 : Lean.PrettyPrinter.Unexpander
--   | `($_ $a $b) => `($a ⊚▷ $b)
--   | _ => throw ()

/- In this section, we build three equivalence data:
- Given an isomorphism `e : x ≅ y`, an equivalence `P.obj x ≌ P.obj y` coming
  from the pseudofunctoriality of `l`.
- Given an isomorphism `e : x ≅ y`, an equivalence `P.obj x ≌ P.obj y`
  from the pseudofunctoriality of `r`.
- Given an isomorphism `e : x ≅ y`, an equivalence `P.obj x ≌ P.obj y`
  from the base change isomorphism applied to the pullback.

hence, we extract out of these the following three adjunctions data
- An adjunction `P.l e.hom ⊣ P.l e.inv`,
- An adjunction `P.l e.hom ⊣ P.r e.hom`,
- An adjunction `P.r e.hom ⊣ P.r e.inv`.
and the units/counits of these adjunctions are all isomorphisms.
And we use the calculus of mates to show that this implies an isomorphism
`P.l e.hom ≅ P.r e.hom`. -/

/- The equivalences and are made reducible so that typeclass synthesis
(and hence bicategoricalComp) is happy with peeking at their 1-cells -/

/- A shorthand for a term we’re going to write a lot. -/
local macro "⊠" : term => `(term| IsPullback.of_horiz_isIso .mk)

/- The equivalence datum coming from an isomorphism `e : c₀ ≌ c₁` and the pseudofunctoriality
of `l`. -/
@[simps, reducible]
def lEquivalenceOfIso {c₀ c₁ : C} (e : c₀ ≅ c₁) :
    P.obj c₀ ≌ P.obj c₁ where
  hom := P.l e.hom
  inv := P.l e.inv
  unit := P.η_l e
  counit := P.ε_l e
  left_triangle := by
    ext
    simp only [leftZigzagIso_hom, leftZigzag, bicategoricalComp, Iso.trans_hom, Iso.symm_hom,
      η_l_hom, ε_l_hom,
      comp_whiskerRight, BicategoricalCoherence.assoc_iso, BicategoricalCoherence.whiskerRight_iso,
      BicategoricalCoherence.refl_iso, whiskerRightIso_hom, Iso.refl_hom, whiskerRight_comp,
      id_whiskerRight, Category.id_comp, Iso.inv_hom_id, Category.comp_id, whiskerLeft_comp,
      Category.assoc]
    have := P.lComp'_associativity' e.hom e.inv e.hom (𝟙 _) (𝟙 _) e.hom
      (by simp) (by simp) (by simp)
    simp only [P.lComp'_id_l, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, Category.assoc,
      P.lComp'_id_r, whiskerRightIso_hom] at this
    rw [Iso.eq_inv_comp, Eq.comm, ← IsIso.eq_inv_comp, ← Iso.eq_comp_inv] at this
    simp [this]

/- The equivalence datum coming from an isomorphism `e : c₀ ≌ c₁` and the pseudofunctoriality
of `r`. -/
@[reducible]
def rEquivalenceOfIso {c₀ c₁ : C} (e : c₀ ≅ c₁) :
    P.obj c₁ ≌ P.obj c₀ where
  hom := P.r e.hom
  inv := P.r e.inv
  unit := P.η_r e
  counit := P.ε_r e
  left_triangle := by
    ext
    simp only [η_r_hom, ε_r_hom,
      leftZigzagIso_hom, leftZigzag, bicategoricalComp, Iso.trans_hom, Iso.symm_hom,
      comp_whiskerRight, BicategoricalCoherence.assoc_iso, BicategoricalCoherence.whiskerRight_iso,
      BicategoricalCoherence.refl_iso, whiskerRightIso_hom, Iso.refl_hom, whiskerRight_comp,
      id_whiskerRight, Category.id_comp, Iso.inv_hom_id, Category.comp_id, whiskerLeft_comp,
      Category.assoc]
    have := P.rComp'₀₂₃_hom e.hom e.inv e.hom (𝟙 _) (𝟙 _) e.hom
      (by simp) (by simp) (by simp)
    simp only [P.rComp'_id_r, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, P.rComp'_id_l,
      whiskerRightIso_hom, Category.assoc] at this
    rw [Iso.eq_inv_comp, Eq.comm, ← IsIso.eq_inv_comp, Eq.comm, ← IsIso.comp_inv_eq] at this
    simp [← this]

/- The equivalence datum coming from an isomorphism `e : c₀ ≌ c₁` and the base change isomorphism.
This contains the data of an adjunction `P.l e.hom ⊣ P.r e.hom` -/
@[reducible]
def baseChangeEquivalenceOfIso {c₀ c₁ : C} (e : c₀ ≅ c₁) :
    P.obj c₀ ≌ P.obj c₁ where
  hom := P.l e.hom
  inv := P.r e.hom
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
    simp only [P.baseChange_unit_right, P.lComp'_id_l, Iso.trans_hom, Iso.symm_hom,
      whiskerLeftIso_hom, comp_whiskerRight, whisker_assoc, triangle_assoc_comp_right_inv_assoc,
      P.lComp'_id_r, Iso.trans_inv, whiskerRightIso_inv, Iso.symm_inv, whiskerLeft_comp,
      Category.assoc, Iso.inv_hom_id_assoc] at bc''
    rotate_isos 1 0 at bc''; rotate_isos ← 0 1 at bc''
    simp_rw [← reassoc_of% wl% Ψ_hom_eq',
      ← associator_naturality_middle_assoc, whisker_exchange,
      ← associator_naturality_left_assoc, whiskerRight_id, comp_whiskerRight_assoc,
      ← reassoc_of% wr% Ψ'_inv_eq] at bc''
    simp [inv% bc'']

/- The compatibility isomorphism `P.l e.hom ≅ P.r e.inv` when e is an isomorphism. -/
def isoOfIso {c₀ c₁ : C} (e : c₀ ≅ c₁) :
    P.l e.hom ≅ P.r e.inv :=
  ((Bicategory.conjugateIsoEquiv
    (P.baseChangeEquivalenceOfIso e).adjunction
      (P.rEquivalenceOfIso e).symm.adjunction).symm (.refl _)).symm

lemma isoOfIso_hom_eq {c₀ c₁ : C} (e : c₀ ≅ c₁) :
    (P.isoOfIso e).hom =
      (λ_ (P.l e.hom)).inv
      ≫ (P.ε_r e).inv ▷ P.l e.hom
      ≫ (α_ (P.r e.inv) (P.r e.hom) (P.l e.hom)).hom
      ≫ P.r e.inv ◁ (P.baseChangeIso e.hom e.hom (𝟙 c₁) (𝟙 c₁) ⊠).inv
      ≫ P.r e.inv ◁ (P.Ψ _).inv
      ≫ (ρ_ (P.r e.inv)).hom := by
  simp [isoOfIso, Bicategory.conjugateEquiv_symm_apply']

lemma isoOfIso_inv_eq {c₀ c₁ : C} (e : c₀ ≅ c₁) :
    (P.isoOfIso e).inv =
    (λ_ (P.r e.inv)).inv
      ≫ (P.Ψ' c₀).hom ▷ P.r e.inv
      ≫ (P.baseChangeIso (𝟙 c₀) (𝟙 c₀) e.hom e.hom ⊠).inv ▷ P.r e.inv
      ≫ (α_ (P.l e.hom) (P.r e.hom) (P.r e.inv)).hom
      ≫ P.l e.hom ◁ (P.η_r e).inv
      ≫ (ρ_ (P.l e.hom)).hom := by
  simp [isoOfIso, Bicategory.conjugateEquiv_symm_apply']

@[simps]
def _root_.CategoryTheory.Bicategory.LocallyDiscrete.equivalenceOfIso {C : Type*} [Category* C]
    {x y : C} (f : x ≅ y) : LocallyDiscrete.mk x ≌ LocallyDiscrete.mk y where
  hom := f.hom.toLoc
  inv := f.inv.toLoc
  unit := Discrete.eqToIso (by simp)
  counit := Discrete.eqToIso (by simp)

lemma isoOfIso_refl (c : C) :
    (P.lId' (𝟙 _)).inv ≫ (P.isoOfIso (Iso.refl c)).hom ≫ (P.rId' (𝟙 _)).hom = 𝟙 _ := by
  rw [← Category.assoc, Iso.comp_hom_eq_id, Iso.inv_comp_eq]
  simp only [Iso.refl_inv, Iso.refl_hom, isoOfIso_hom_eq]
  simp_rw [reassoc_of% wl% P.baseChange_id_Ψ_inv c]
  simp only [P.ε_r_inv, Iso.refl_inv, Iso.refl_hom, P.rComp'_id_r, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, comp_whiskerRight, whisker_assoc, triangle_assoc_comp_right_inv_assoc,
    P.Ψ'_inv_eq, whiskerLeft_comp, whiskerLeft_rightUnitor, Category.assoc, Iso.inv_hom_id_assoc]
  simp_rw [rightUnitor_comp_assoc, cancelIso, ← reassoc_of% wl% whisker_exchange,
    reassoc_of% wl% id_whiskerLeft, cancelIso,
    reassoc_of% wl% whiskerRight_id, cancelIso, ← whisker_exchange_assoc]
  bicategory

-- TODO: generalize to for an arbitrary pseudofunctor.
/-- An auxiliary computation for isoOfIso_trans -/
lemma conjugateIsoEquiv_comp_rComp {x y z : C}
    (f : x ≅ y) (g : y ≅ z) (h : x ≅ z)
    (hfg : f ≪≫ g = h := by cat_disch) :
    (Bicategory.conjugateIsoEquiv
      ((P.rEquivalenceOfIso f).symm.adjunction.comp (P.rEquivalenceOfIso g).symm.adjunction)
      (P.rEquivalenceOfIso h).symm.adjunction)
        (P.rComp' g.inv f.inv h.inv) =
        (P.rComp' f.hom g.hom h.hom).symm := by
  ext : 1
  subst h
  dsimp
  have {a b : C} (e : a ≅ b) :
      (P.rEquivalenceOfIso e).symm.adjunction =
      P.rPseudofunctor.mapAdj (LocallyDiscrete.equivalenceOfIso e.op).symm.adjunction := by
    ext
    · dsimp
      generalize_proofs _ h
      rw [P.ε_r_inv, PrelaxFunctor.map₂_eqToHom]
      simp only [LocallyDiscrete.mkPseudofunctor_obj, LocallyDiscrete.mkPseudofunctor_map,
        LocallyDiscrete.id_as, unop_id, LocallyDiscrete.comp_as, Quiver.Hom.toLoc_as, unop_comp,
        Quiver.Hom.unop_op, Iso.cancel_iso_inv_left]
      rw! [e.hom_inv_id]
      simp
    · dsimp
      generalize_proofs h
      rw [P.η_r_inv, PrelaxFunctor.map₂_eqToHom]
      simp only [LocallyDiscrete.mkPseudofunctor_obj, LocallyDiscrete.mkPseudofunctor_map,
        LocallyDiscrete.comp_as, Quiver.Hom.toLoc_as, unop_comp, Quiver.Hom.unop_op,
        LocallyDiscrete.id_as, unop_id]
      rw! [e.inv_hom_id]
      simp
  convert dsimp% Pseudofunctor.conjugateEquiv_mapAdj_comp_mapComp_hom (F := P.rPseudofunctor)
    (adj₁ := (LocallyDiscrete.equivalenceOfIso f.op).symm.adjunction)
    (adj₂ := (LocallyDiscrete.equivalenceOfIso g.op).symm.adjunction)
  · rw [this]
  · rw [this]
  · rw [this]
    congr; ext <;> subsingleton

/- A key equation for proving transitivity of `isoOfIso`. -/
lemma baseChangeEquivalenceOfIso_counit_hom_comp
    {x y z : C} (f : x ≅ y) (g : y ≅ z) (h : x ≅ z)
    (hfg : f ≪≫ g = h := by cat_disch) :
    (P.baseChangeEquivalenceOfIso h).counit.hom =
    _ ◁ (P.lComp' f.hom g.hom h.hom).hom ≫ (P.rComp' f.hom g.hom h.hom).hom ▷ _ ⊗≫
      P.r g.hom ◁ (P.baseChangeEquivalenceOfIso f).counit.hom ▷ P.l g.hom ⊗≫
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
  simp_rw [P.rComp'_id_r, Iso.trans_inv, whiskerLeftIso_inv, Iso.symm_inv,
    whiskerLeft_comp, ← associator_naturality_right_assoc, ← whisker_exchange_assoc,
    whiskerRight_id_assoc, rightUnitor_comp_inv_assoc, cancelIso, Category.comp_id]
  rotate_isos 0 1
  simp only [P.lComp'_id_r, Iso.trans_inv, whiskerRightIso_inv, Iso.symm_inv, comp_whiskerRight,
    leftUnitor_whiskerRight, whiskerLeft_comp, comp_whiskerLeft, Category.assoc,
    Iso.inv_hom_id_assoc]
  simp_rw [← reassoc_of% wl% associator_inv_naturality_left, cancelIso,
    reassoc_of% wl% whisker_exchange, reassoc_of% wl% id_whiskerLeft, cancelIso]
  have := (P.baseChangeEquivalenceOfIso g).adjunction.left_triangle
  dsimp [leftZigzag, bicategoricalComp] at this
  have := (P.baseChangeEquivalenceOfIso g).adjunction.right_triangle
  dsimp [rightZigzag, bicategoricalComp] at this
  simp only [whiskerRight_comp, whiskerLeft_comp, inv%P.baseChange_unit_right g.hom,
    whiskerLeft_rightUnitor_inv, Category.assoc, whiskerLeft_whiskerLeft_inv_hom_assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id, whiskerLeft_hom_inv_assoc]
  simp_rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp]
  congr 1
  simp_rw [cat_nf, leftUnitor_comp_assoc, cancelIso, P.Ψ_inv_eq']
  bicategory

/-- A rather technical computation for an important property: the compositions
isomorphisms for the pseudofunctors P.l and P.r are conjugate to each
others via the base change adjunctions. This is a key property to show
that the ismorphism `P.isoOfIso P.l e.hom ≅ P.r e.inv` is compatible with compositions. -/
lemma conjugateIsoEquiv_baseChange
    {x y z : C} (f : x ≅ y) (g : y ≅ z) (h : x ≅ z)
    (hfg : f ≪≫ g = h := by cat_disch) :
    letI bcAdj_f := (P.baseChangeEquivalenceOfIso f).adjunction
    letI bcAdj_g := (P.baseChangeEquivalenceOfIso g).adjunction
    letI bcAdj_h := (P.baseChangeEquivalenceOfIso h).adjunction
    letI bcAdj_fg := bcAdj_f.comp bcAdj_g
    letI Eₗ : P.l h.hom ≅ P.l f.hom ≫ P.l g.hom := P.lComp' f.hom g.hom h.hom
    letI Eᵣ : P.r h.hom ≅ P.r g.hom ≫ P.r f.hom := P.rComp' f.hom g.hom h.hom
    (Bicategory.conjugateIsoEquiv bcAdj_h bcAdj_fg) Eₗ.symm = Eᵣ := by
  ext
  dsimp
  rw [Bicategory.conjugateEquiv_apply, Bicategory.mateEquiv_apply']
  have := P.baseChangeEquivalenceOfIso_counit_hom_comp f g h
  dsimp [bicategoricalComp] at this ⊢
  rotate_isos ← 0 1 at this
  simp only [this, Category.assoc, whiskerLeft_comp, comp_whiskerRight]
  simp only [whiskerLeft_id, whiskerLeft_rightUnitor_inv, id_whiskerLeft, unitors_equal,
    whiskerLeft_comp, whiskerLeft_rightUnitor, Category.assoc, whiskerRight_comp, id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id, leftUnitor_whiskerRight, comp_whiskerRight,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, Category.comp_id, whiskerRight_id,
    Iso.hom_inv_id, whisker_assoc, Iso.hom_inv_id_assoc, inv_hom_whiskerRight_whiskerRight_assoc,
    inv_hom_whiskerRight_assoc, pentagon_hom_inv_inv_inv_inv_assoc, whiskerLeft_hom_inv_assoc,
    whiskerLeft_inv_hom_assoc]
  /- We first get rid of h -/
  slice_lhs 11 17 => equals 𝟙 _ => bicategory
  simp only [cat_nf, cancelIso]
  simp_rw [← whiskerLeft_comp_assoc,
    ← reassoc_of% wr% wr% associator_inv_naturality_left,
    ← pentagon_hom_inv_inv_inv_inv_assoc, ← associator_inv_naturality_left_assoc,
    whisker_exchange_assoc, cat_nf, cancelIso]
  rotate_isos 1 0
  clear this hfg h
  /- giving shorthands helps here -/
  set Uf := (P.baseChangeEquivalenceOfIso f).adjunction.unit with Uf_def
  set Ug := (P.baseChangeEquivalenceOfIso g).adjunction.unit with Ug_def
  set Cf := (P.baseChangeEquivalenceOfIso f).adjunction.counit with Cf_def
  set Cg := (P.baseChangeEquivalenceOfIso g).adjunction.counit with Cg_def
  dsimp at Uf Ug Cf Cg Uf_def Ug_def Cf_def Cg_def
  rw [← reassoc_of% wl% wl% Uf_def,
    ← reassoc_of% wl% wl% wl% wr% Ug_def,
    ← reassoc_of% wl% wr% wr% wr% Cf_def,
    ← reassoc_of% wr% wr% Cg_def]
  calc _ = 𝟙 _ ⊗≫
            (P.r g.hom ◁ P.r f.hom ◁ Uf) ≫
              (P.r g.hom ◁ P.r f.hom ◁ P.l f.hom ◁ (λ_ (P.r f.hom)).inv) ⊗≫
            (P.r g.hom ◁ P.r f.hom ◁ P.l f.hom ◁ Ug ▷ P.r f.hom) ⊗≫
            (P.r g.hom ◁ Cf ▷ P.l g.hom ▷ P.r g.hom ▷ P.r f.hom) ⊗≫
            (Cg ▷ P.r g.hom ▷ P.r f.hom) ⊗≫ 𝟙 _ := by
          bicategory
      _ = 𝟙 _ ⊗≫
            (P.r g.hom ◁ P.r f.hom ◁ Uf) ≫
              (P.r g.hom ◁ P.r f.hom ◁ P.l f.hom ◁ (λ_ (P.r f.hom)).inv) ⊗≫
            P.r g.hom ◁ (Cf ▷ _ ≫ _ ◁ Ug) ▷ P.r f.hom ⊗≫
            (Cg ▷ P.r g.hom ▷ P.r f.hom) ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]
          bicategory
      _ = 𝟙 _ ⊗≫
            (P.r g.hom ◁ (Bicategory.rightZigzag Uf Cf)) ⊗≫
            (Bicategory.rightZigzag Ug Cg) ▷ P.r f.hom ⊗≫ 𝟙 _ := by
          bicategory
      _ = 𝟙 (P.r g.hom ≫ P.r f.hom) := by
          dsimp [Uf, Ug, Cf, Cg]
          have rtf := (P.baseChangeEquivalenceOfIso f).adjunction.right_triangle
          have rtg := (P.baseChangeEquivalenceOfIso g).adjunction.right_triangle
          dsimp [bicategoricalComp] at rtf rtg
          rw [rtf, rtg]
          bicategory

-- TODO inline properly the letIs for cleaning up
lemma isoOfIso_trans {x y z : C} (f : x ≅ y) (g : y ≅ z) (h : x ≅ z)
    (hfg : f ≪≫ g = h := by cat_disch) :
    (P.isoOfIso h).hom =
    (P.lComp' f.hom g.hom h.hom).hom ≫
    ((P.isoOfIso f).hom ▷ P.l g.hom) ≫
    P.r f.inv ◁ (P.isoOfIso g).hom ≫
    (P.rComp' g.inv f.inv h.inv).inv := by
  -- This one will be hard.
  -- first, we’ll bring up some pasting laws
  -- The idea is that the adjunctions for `h` should be composites of the ones for f and g.
  letI bcAdj_h := (P.baseChangeEquivalenceOfIso h).adjunction
  letI bcAdj_f := (P.baseChangeEquivalenceOfIso f).adjunction
  letI bcAdj_g := (P.baseChangeEquivalenceOfIso g).adjunction
  letI equivOfIsoAdj_h_symm := (P.rEquivalenceOfIso h).symm.adjunction
  letI equivOfIsoAdj_f_symm := (P.rEquivalenceOfIso f).symm.adjunction
  letI equivOfIsoAdj_g_symm := (P.rEquivalenceOfIso g).symm.adjunction
  dsimp at bcAdj_f bcAdj_g bcAdj_h equivOfIsoAdj_h_symm equivOfIsoAdj_f_symm equivOfIsoAdj_g_symm
  letI bcAdj_fg := bcAdj_f.comp bcAdj_g
  letI equivOfIsoAdj_gf_symm := equivOfIsoAdj_f_symm.comp equivOfIsoAdj_g_symm
  letI Eₗ : P.l h.hom ≅ P.l f.hom ≫ P.l g.hom := P.lComp' f.hom g.hom h.hom
  letI Eᵣ : P.r h.hom ≅ P.r g.hom ≫ P.r f.hom := P.rComp' f.hom g.hom h.hom
  letI Eₗ_inv := P.lComp' g.inv f.inv h.inv
  letI Eᵣ_inv := P.rComp' g.inv f.inv h.inv
  dsimp [isoOfIso]
  change (Bicategory.conjugateEquiv equivOfIsoAdj_h_symm bcAdj_h).symm _ = _
  have congrLeft1 := conjugateEquiv_symm_congrIso_left (adj₁ := equivOfIsoAdj_h_symm)
    (adj₁' := equivOfIsoAdj_gf_symm)
    (adj₂ := bcAdj_h) (e₁ := Eᵣ_inv) (e₂ := Eᵣ.symm) (conjugateIsoEquiv_comp_rComp _ _ _ _) (𝟙 _)
  simp only [congrLeft1, Iso.symm_hom, Category.comp_id]
  have congrRight1 := conjugateEquiv_symm_congrIso_right (adj₁ := equivOfIsoAdj_gf_symm)
    (adj₂ := bcAdj_h) (adj₂' := bcAdj_fg) (e₁ := Eₗ.symm) (e₂ := Eᵣ)
      (conjugateIsoEquiv_baseChange ..) Eᵣ.inv
  simp only [congrRight1, Iso.symm_inv, Iso.inv_hom_id, Category.assoc]
  dsimp [equivOfIsoAdj_gf_symm, bcAdj_fg, Eₗ, Eᵣ_inv,
    equivOfIsoAdj_g_symm, equivOfIsoAdj_f_symm, bcAdj_f, bcAdj_g]
  simp only [conjugateEquiv_symm_apply, Category.id_comp, Category.assoc, comp_whiskerRight,
    leftUnitor_inv_whiskerRight, whiskerLeft_comp, whiskerLeft_rightUnitor, Iso.cancel_iso_hom_left,
    Iso.cancel_iso_inv_left]
  have mate_hcomp := Bicategory.mateEquiv_symm_hcomp
    (adj₁ := (P.rEquivalenceOfIso f).symm.adjunction)
    (adj₂ := (P.baseChangeEquivalenceOfIso f).adjunction)
    (adj₃ := (P.rEquivalenceOfIso g).symm.adjunction)
    (adj₄ := (P.baseChangeEquivalenceOfIso g).adjunction)
    (g := 𝟙 _) (h := 𝟙 _) (k := 𝟙 _)
    (α := (ρ_ _).hom ≫ (λ_ _).inv) (β := (ρ_ _).hom ≫ (λ_ _).inv)
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp] at mate_hcomp
  simp only [whiskerLeft_comp, whiskerLeft_rightUnitor, Category.assoc, comp_whiskerRight,
    leftUnitor_inv_whiskerRight, Iso.inv_hom_id, Category.comp_id, triangle_assoc_comp_right_assoc,
    whiskerLeft_inv_hom_assoc, Iso.hom_inv_id_assoc] at mate_hcomp
  simp only [mate_hcomp, Category.assoc, Iso.cancel_iso_inv_left]
  bicategory

/-- A technical compatibility of base change isomorphisms: given two pullback
square

and

as well as an isomorphism (e : c₀ ≅ c₀') compatible with the projections
(which is then unique), the base change isomorphism for teh second
square can be expressed in terms of the first and the one for the square

. -/
lemma baseChange_change_pullback {c₀ c₀' c₁ c₂ c₃ : C}
    (t : c₀ ⟶ c₁) (l : c₀ ⟶ c₂) (r : c₁ ⟶ c₃) (b : c₂ ⟶ c₃)
    (t' : c₀' ⟶ c₁) (l' : c₀' ⟶ c₂)
    (e : c₀' ≅ c₀) (h₁ : IsPullback t l r b) (h₂ : IsPullback t' l' r b)
    (tr₁ : e.hom ≫ t = t') (tr₂ : e.hom ≫ l = l') :
    (P.baseChangeIso t' l' r b h₂).hom =
      (P.baseChangeIso t l r b h₁).hom ⊗≫
      (P.r t ◁ (P.Ψ _).hom ▷ P.l l ≫
      P.r t ◁ (P.baseChangeIso e.hom e.hom (𝟙 _) (𝟙 _) ⊠).hom ▷ P.l l) ⊗≫
      (P.rComp' e.hom t t').inv ▷ P.l e.hom ▷ P.l l ⊗≫
      P.r t' ◁ (P.lComp' e.hom l l').inv ⊗≫ 𝟙 _ := by
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
  simp only [P.baseChange_unit_left, P.baseChange_unit_right,
    P.lComp'_id_r, P.rComp'_id_r, cat_nf, whisker_assoc, cancelIso] at vert
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

-- #exit
end Adjunction

noncomputable section toPseudoFunctor

variable [Limits.HasPullbacks C]

abbrev obj' (x : EffBurnside C) : B := P.obj x.as.of

abbrev map {x y : EffBurnside C} (S : x ⟶ y) : P.obj' x ⟶ P.obj' y := P.r S.of.l ≫ P.l S.of.r

abbrev map₂ {x y : EffBurnside C} {S S' : x ⟶ y}
    (η : S ⟶ S') : P.map S ⟶ P.map S' :=
  letI e_iso : S.of.apex ≅ S'.of.apex := Spans.apexIso η.iso
  (P.rComp' e_iso.hom S'.of.l _).hom ▷ (P.l S.of.r) ≫
  (P.r S'.of.l ≫ P.r e_iso.hom) ◁ (P.lComp' e_iso.hom S'.of.r _).hom ≫
  (α_ _ _ _).hom ≫
  (P.r S'.of.l) ◁ (α_ (P.r e_iso.hom) (P.l e_iso.hom) (P.l S'.of.r)).inv ≫
  (P.r S'.of.l) ◁ (P.baseChangeEquivalenceOfIso e_iso).counit.hom ▷ (P.l S'.of.r) ≫
  (P.r S'.of.l) ◁ (λ_ (P.l S'.of.r)).hom

noncomputable abbrev mapId (x : EffBurnside C) : P.map (𝟙 x) ≅ 𝟙 (P.obj' x) :=
    (P.baseChangeEquivalenceOfIso (Iso.refl _)).counit

/-- A shorthand for a kind of isomorphism that will show up a few time. -/
@[reducible]
def 𝔯 {x y z : EffBurnside C} (f : x ⟶ y) (g : y ⟶ z) :=
    P.rComp' (Spans.πₗ f.of g.of) f.of.l (f.of ≫ g.of).l

@[reducible]
def 𝔩 {x y z : EffBurnside C} (f : x ⟶ y) (g : y ⟶ z) :=
    P.lComp' (Spans.πᵣ f.of g.of) g.of.r (f.of ≫ g.of).r

/-- A shorthand for a morphism that we will be seeing a lot. -/
@[reducible]
def μ {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :
    P.map (S₁ ≫ S₂) ≅
    (P.r S₁.of.l ≫ P.r (Spans.πₗ S₁.of S₂.of)) ≫ P.l (Spans.πᵣ S₁.of S₂.of) ≫ P.l S₂.of.r :=
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

/-- Again a shorthand for a morphism that we will be seeing a lot. -/
abbrev Γ {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :=
  P.baseChangeIso (Spans.πₗ S₁.of S₂.of) (Spans.πᵣ S₁.of S₂.of) S₁.of.r S₂.of.l
    (IsPullback.of_isLimit (Spans.isLimitCompPullbackCone S₁.of S₂.of))

noncomputable abbrev mapComp {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :
    P.map (S₁ ≫ S₂) ≅ P.map S₁ ≫ P.map S₂ :=
  (P.μ S₁ S₂) ≪⊗≫
    (whiskerLeftIso (P.r S₁.of.l) (whiskerRightIso (P.Γ S₁ S₂).symm (P.l S₂.of.r))) ≪⊗≫ .refl _

lemma mapComp_hom {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :
    (P.mapComp S₁ S₂).hom =
    (P.μ S₁ S₂).hom ⊗≫ (P.r S₁.of.l) ◁ (P.Γ S₁ S₂).inv ▷ (P.l S₂.of.r) ⊗≫ 𝟙 _ :=
  rfl

lemma mapComp_inv {x y z : EffBurnside C} (S₁ : x ⟶ y) (S₂ : y ⟶ z) :
    (P.mapComp S₁ S₂).inv =
    𝟙 _ ⊗≫ (P.r S₁.of.l) ◁ (P.Γ S₁ S₂).hom ▷ (P.l S₂.of.r) ⊗≫ (P.μ S₁ S₂).inv := by
  dsimp [bicategoricalIso, mapComp, bicategoricalIsoComp]
  bicategory

lemma map₂_id {a b : EffBurnside C} (f : a ⟶ b) : P.map₂ (𝟙 f) = 𝟙 (P.map f) := by
    dsimp [map₂]
    rw [inv% P.baseChange_id_eq]
    simp only [cat_nf, cancelIso, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
      whiskerRightIso_hom, P.lComp'_id_r, P.rComp'_id_r]
    simp_rw [← reassoc_of% wl% associator_inv_naturality_middle, cancelIso,
      associator_naturality_middle_assoc,
      ← reassoc_of% wl% whisker_exchange, reassoc_of% wl% associator_inv_naturality_left,
      reassoc_of% wl% wr% whiskerRight_id, P.Ψ_inv_eq', cat_nf, cancelIso]
    bicategory

/-- A shorthand for the counit of the base change adjunction deduced by a 2-morphism in
`EffBurnside C`: having it prevents some unfoldings. -/
private def ε {c c' : EffBurnside C} {f g : c ⟶ c'} (η : f ⟶ g) :
    P.r (η.iso.hom.hom) ≫ P.l (η.iso.hom.hom) ≅ 𝟙 (P.obj g.of.apex) :=
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
    (inv% P.rComp'₀₁₃_hom
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
    (P.lComp'₀₁₃_hom
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

end PseudoFunctorCore

end CategoryTheory.EffBurnside
