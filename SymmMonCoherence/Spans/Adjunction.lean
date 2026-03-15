/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.Spans.Inclusions
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # Adjunctions and Spans

In this file, given an arrow `f : c ⟶ c'` in a category `C` with pullbacks,
we show that the 1-cells `(Spans.inr C).map f.toLoc` and
`(Spans.inl C).map f.op.toLoc` are adjoint to each other in the bicategorical
sense, and that the adjunction is pseudofunctorial.
We furthermore show that a pullback square
in `C` induces an adjointable square in the bicategory of spans.
-/

@[expose] public section

namespace CategoryTheory.Spans

open Bicategory
universe w₁ v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]

variable [Limits.HasPullbacks C]
noncomputable section

set_option backward.isDefEq.respectTransparency false in
-- TODO: some API for this one
/-- In bicategories of spans, the 1-morphisms `(Spans.inr C).map f.toLoc` and
`(Spans.inl C).map f.op.toLoc` are adjoint to each other -/
def inrInlAdj {x y : C} (f : x ⟶ y) :
    (Spans.inr C).map f.toLoc ⊣ (Spans.inl C).map f.op.toLoc where
  unit := Spans.compLift (𝟙 _) (𝟙 _)
  counit := Spans.mkHom₂ (Spans.πₗ _ _ ≫ f) (by simp) (by
    have := Spans.comp_comm ((inl C).map f.op.toLoc) ((inr C).map f.toLoc)
    dsimp at this
    simp only [Category.comp_id] at this
    simp [this])
  left_triangle := by
    dsimp [leftZigzag, bicategoricalComp]
    have := Spans.comp_comm (𝟙 _) ((inr C).map f.toLoc)
    dsimp at this
    simp only [Category.comp_id] at this
    ext
    · simp [this]
    · simp [this]
  right_triangle := by
    dsimp [rightZigzag, bicategoricalComp]
    have := Spans.comp_comm ((inl C).map f.op.toLoc) (𝟙 _)
    dsimp at this
    simp only [Category.comp_id] at this
    ext
    · simp
    · have := Spans.comp_comm (Wₗ := ⊤) (Wᵣ := ⊤)
        (Spans.mkHom x f (𝟙 x) (by tauto) (by tauto)) (𝟙 _)
      simp only [Category.comp_id] at this
      simp [this]

-- TODO: move to a different place?
-- TODO: API
/-- The canonical decomposition of a morphism in the bicategory of spans. -/
@[simps!]
def decomposeIso {X Y : Spans C ⊤ ⊤} (S : X ⟶ Y) :
    S ≅ (inl C).map S.l.op.toLoc ≫ (inr C).map S.r.toLoc :=
  Spans.mkIso₂
    ({ hom := compLiftApex (𝟙 _) (𝟙 _) rfl
       inv := Spans.πₗ ((inl C).map S.l.op.toLoc) ((inr C).map S.r.toLoc)
       inv_hom_id := by
         ext
         · simp
         · have := Spans.comp_comm ((inl C).map S.l.op.toLoc) ((inr C).map S.r.toLoc)
           dsimp at this
           simp only [Category.comp_id] at this
           simp [this]
       hom_inv_id := by simp })
    (by simp) (by simp)

section pullbacks

variable {c₀ c₁ c₂ c₃ : C} {t : c₀ ⟶ c₁} {l : c₀ ⟶ c₂} {r : c₁ ⟶ c₃} {b : c₂ ⟶ c₃}
    (S : IsPullback t l r b)

/-- The isomorphism of spans induced by a pullback square in C -/
@[simps! inv_hom]
def isoCompOfIsPullback :
    (Spans.mkHom (C := C) (Wₗ := ⊤) (Wᵣ := ⊤) c₀ l t (by tauto) (by tauto)) ≅
      (inr C).map b.toLoc ≫ (inl C).map r.op.toLoc where
  hom := compLift l t (by simp) (by simp [S.w])
  inv := Spans.mkHom₂
    (S.lift (Spans.πᵣ ..) (Spans.πₗ ..)
      (by simpa using (Spans.comp_comm ((inr C).map b.toLoc) ((inl C).map r.op.toLoc)).symm))
    (by simp)
    (by simp)
  inv_hom_id := by
    ext
    · simp
    · simp
  hom_inv_id := by
    ext
    apply S.hom_ext
    · simp
    · simp

@[reassoc (attr := simp), grind =]
lemma isoCompOfIsPullback_hom_hom_πᵣ :
    (isoCompOfIsPullback S).hom.hom ≫ Spans.πᵣ _ _ = t := by
  simp [isoCompOfIsPullback]

@[reassoc (attr := simp), grind =]
lemma isoCompOfIsPullback_hom_hom_πₗ :
    (isoCompOfIsPullback S).hom.hom ≫ Spans.πₗ _ _ = l := by
  simp [isoCompOfIsPullback]

/-- The "base change" isomorphism that comes from a pullback square in `C`. We do not define
it directly via the calculus of mates, and instead we show that -/
def baseChangeIso :
    (inl C).map l.op.toLoc ≫ (inr C).map t.toLoc ≅
    (inr C).map b.toLoc ≫ (inl C).map r.op.toLoc :=
  (decomposeIso
      (Spans.mkHom (C := C) (Wₗ := ⊤) (Wᵣ := ⊤) c₀ l t (by tauto) (by tauto))).symm ≪≫
    isoCompOfIsPullback S

set_option backward.isDefEq.respectTransparency false in
/-- The "base change" isomorphism we manually defined above is the same as the
base change morphism that comes from the calculus of mates. This
proves that this morphism is indeed invertible. -/
theorem mateEquiv_eq :
    (baseChangeIso S).hom =
    (Bicategory.mateEquiv (adj₁ := inrInlAdj b) (adj₂ := inrInlAdj t)
      (g := (inl C).map l.op.toLoc) (h := (inl C).map r.op.toLoc) |>.symm
        ((inl C).isoMapOfCommSq S.toCommSq.op.toLoc).hom) := by
  rw [Bicategory.mateEquiv_symm_apply']
  dsimp [bicategoricalComp]
  ext
  · simp [baseChangeIso, decomposeIso, isoCompOfIsPullback, inrInlAdj, inr, inl]
  · simp [baseChangeIso, decomposeIso, isoCompOfIsPullback, inrInlAdj, inr, inl,
      Pseudofunctor.isoMapOfCommSq, Pseudofunctor.mapComp', inr, inl,
      reassoc_of% leftUnitor_inv_hom_πᵣ]

end pullbacks

section pseudofunctor

-- TODO: upstream the next two lemmas
lemma _root_.CategoryTheory.Bicategory.Adj.eqToHom_τl
  {B : Type*} [Bicategory B] {x y : Adj B} (f g : x ⟶ y) (h : f = g) :
    (eqToHom h).τl = eqToHom (congr($(h).l)) := by
  subst h
  simp

lemma _root_.CategoryTheory.Bicategory.Adj.eqToHom_τr
  {B : Type*} [Bicategory B] {x y : Adj B} (f g : x ⟶ y) (h : f = g) :
    (eqToHom h).τr = eqToHom (congr($(h.symm).r)) := by
  subst h
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction (inr f) ⊣ (inl f) is pseudofunctorial. -/
def toAdjPseudofunctor : LocallyDiscrete C ⥤ᵖ Adj (Spans C ⊤ ⊤) :=
  pseudofunctorOfIsLocallyDiscrete
    (obj := fun x ↦ Adj.mk <| Spans.mk <| x.as)
    (map := fun {x y} f ↦ Adj.Hom.mk <| inrInlAdj f.as)
    (mapId := fun b ↦ Adj.iso₂Mk
      ((inr C).mapId b)
      ((inl C).mapId (.mk <| .op b.as))
      (by
        ext
        simp [Bicategory.conjugateEquiv_apply', inrInlAdj, Bicategory.Adjunction.id]))
    (mapComp := fun {x y z} f g ↦ Adj.iso₂Mk
      ((inr C).mapComp f g)
      ((inl C).mapComp g.as.op.toLoc f.as.op.toLoc).symm
      (by
        ext
        simp [Bicategory.conjugateEquiv_apply', inrInlAdj]))
    (map₂_associator := by
      intros x y z t f g h
      ext
      simp [Bicategory.Adj.eqToHom_τl, eqToHom_hom])
    (map₂_left_unitor := by
      intros
      ext
      simp [Bicategory.Adj.eqToHom_τl, eqToHom_hom])
    (map₂_right_unitor := by
      intros
      ext
      simp [Bicategory.Adj.eqToHom_τl, eqToHom_hom])

end pseudofunctor

end

end CategoryTheory.Spans
