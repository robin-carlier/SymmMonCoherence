/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.Spans.Basic
public import SymmMonCoherence.Spans.Inclusions

/-! # Spans and terminal objects

In this file, given a category `C` with pullbacks,
we record some equivalences of categories between hom-categories
in bicategories of spans (with respect to all morphisms)
where one of the object is terminal, and
over/under-categories of `C`. More precisely, we constructs equivalences

- `(x : Spans C ⊤ ⊤) ⟶ y ≌ C` when both `x` and `y` are terminal
- `(x : Spans C ⊤ ⊤) ⟶ y ≌ Over x` when `y` is terminal
- `(x : Spans C ⊤ ⊤) ⟶ y ≌ Over y` when `x` is terminal

-/

@[expose] public section

namespace CategoryTheory.Spans

variable (C : Type*) [Category* C] [Limits.HasPullbacks C]

noncomputable def spanOverEquivalenceLeftOfIsTerminal
    (x y : Spans C ⊤ ⊤) (hx : Limits.IsTerminal x.of) :
    (x ⟶ y) ≌ Over y.of where
  functor := Spans.toOverRight _ _
  inverse.obj X :=
    { apex := X.left
      l := hx.from _
      r := X.hom
      wl := by tauto
      wr := by tauto }
  inverse.map f := Spans.mkHom₂ f.left
  unitIso := NatIso.ofComponents (fun S ↦ Spans.mkIso₂ (.refl _) (by apply hx.hom_ext))
  counitIso := NatIso.ofComponents (fun S ↦ .refl _)

noncomputable def spanOverEquivalenceRightOfIsterminal
    (x y : Spans C ⊤ ⊤) (hx : Limits.IsTerminal y.of) :
    (x ⟶ y) ≌ Over x.of where
  functor := Spans.toOverLeft _ _
  inverse.obj X :=
    { apex := X.left
      l := X.hom
      r := hx.from _
      wl := by tauto
      wr := by tauto }
  inverse.map f := Spans.mkHom₂ f.left
  unitIso :=
    NatIso.ofComponents (fun S ↦ Spans.mkIso₂ (.refl _) (by simp) (by apply hx.hom_ext))
  counitIso := NatIso.ofComponents (fun S ↦ .refl _)

noncomputable def spanEndEquivalenceOfIsTerminal
    (x : Spans C ⊤ ⊤) (hx : Limits.IsTerminal x.of) :
    (x ⟶ x) ≌ C where
  functor := Spans.forgetLegs _ _
  inverse.obj X :=
    { apex := X
      l := hx.from _
      r := hx.from _
      wl := by tauto
      wr := by tauto }
  inverse.map f := Spans.mkHom₂ f
  unitIso :=
    NatIso.ofComponents (fun S ↦ Spans.mkIso₂ (.refl _)
      (by apply hx.hom_ext) (by apply hx.hom_ext))
  counitIso := NatIso.ofComponents (fun S ↦ .refl _)

end CategoryTheory.Spans
