/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.Spans.Inclusions
public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import Mathlib.CategoryTheory.Bicategory.Opposites

/-! # Effective Burnside (2,1)-categories

In this file, we define the effective Burnside (2,1)-category of a category with pullbacks
as an abbreviation for the Pith of the bicategory of spans in C .

Spelled explicitly, this is a bicategory where
- objects are (a type alias for) objects of `C`
- 1-morphisms `c → c'` are spans `c ← x → c'` in `C`.
- 2-morphisms are isomorphisms of spans, i.e digrams
  ```
      c
    ↗ ↑
  x → y
    ↘ ↓
      c'
  ```
  where the horizontal morphism is an isomorphism.

## Terminological note

The name "Burnside category" comes from the litterature on equivariant homotopy
theory and more specifically the theory of Mackey functors, where local group-completion of
the pith of the bicategory of spans on finite G-sets is called the "Burnside category of G",
as a categorificaton of the Burnside ring of G
(which itself is the group-completion of the semiring of isomorphisms classes of finite G-sets).
The terminology "effective Burnside ∞-category" was then coined by Barwick and used
without mention of any group (like we do) for the (∞,1)-categorical analogue of the pith of the
category of spans on a category. When interpreting locally groupoidal bicategories as
(∝,1)-categories, we recover Barwick's object.
-/

@[expose] public section

namespace CategoryTheory

/--
The effective Burnside bicategory of a category with pullbacks is the pith of the
bicategory of spans of `C`. Spelled explicitly, this is a bicategory where
- objects are objects of `C`
- 1-morphisms `c → c'` are spans `c ← x → c'` in `C`.
- 2-morphisms are isomorphisms of spans, i.e digrams
  ```
      c
    ↗ ↑
  x → y
    ↘ ↓
      c'
  ```
  where the horizontal morphism is an isomorphism.

By construction, this is a locally groupoidal bicategory.
Please refer to the terminological note in the module docstring
to have an explanation for the name of this object.
-/
abbrev EffBurnside (C : Type*) [Category* C] [Limits.HasPullbacks C] :=
    Bicategory.Pith (Spans C ⊤ ⊤)

namespace EffBurnside

open Bicategory

-- TODO move somewhere else
instance (C : Type*) [Bicategory C] [IsLocallyDiscrete C] :
  IsLocallyGroupoid C := fun x y ↦
    ⟨fun {a b} f ↦ by
      obtain rfl : a = b := IsDiscrete.eq_of_hom f
      obtain rfl : f = 𝟙 _ := by subsingleton
      infer_instance⟩

-- TODO move this elsewhere
@[simp]
lemma _root_.CategoryTheory.Bicategory.Pith.id_iso (C : Type*) [Bicategory C] {x y : Pith C}
    (f : x ⟶ y) :
    (𝟙 f : f ⟶ f).iso = .refl _ :=
  rfl

variable (C : Type*) [Category* C] [Limits.HasPullbacks C]

/-- The right inclusion of `C` in `EffBurnside C`. -/
noncomputable def inr : (LocallyDiscrete C) ⥤ᵖ (EffBurnside C) :=
   Bicategory.Pith.pseudofunctorToPith <| Spans.inr C

/-- The left inclusion of `Cᵒᵖ` in `EffBurnside C`. -/
noncomputable def inl : (LocallyDiscrete Cᵒᵖ) ⥤ᵖ (EffBurnside C) :=
   Bicategory.Pith.pseudofunctorToPith <| Spans.inl C

section

universe w v u

@[local ext]
lemma _root_.CategoryTheory.Bicategory.Opposite.unop2_hom_ext {B : Type u} [Bicategory.{w, v} B]
    {a b : Bᵒᵖ} {f g : a ⟶ b} {φ φ' : f ⟶ g} (h : φ.unop2 = φ'.unop2) :
    φ = φ' := by
  cases φ
  cases φ'
  grind

open Opposite Bicategory.Opposite

/-- The canonical equivalence (in fact, isomorphism) of categories between
`a ⟶ b` and `op b ⟶ op a`,. -/
def _root_.CategoryTheory.Bicategory.Opposite.homCategoryEquivalence
    {B : Type u} [Bicategory.{w, v} B]
    (a b : B) : (op a ⟶ op b) ≌ (b ⟶ a) where
  functor.obj f := f.unop
  functor.map {f g} η := η.unop2
  inverse.obj f := op f
  inverse.map {f g} η := Bicategory.Opposite.op2 η
  unitIso := NatIso.ofComponents (fun _ ↦ .refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ .refl _)

end

-- TODO this should be generalized to more general categories of spans as well
attribute [local ext] _root_.CategoryTheory.Bicategory.Opposite.unop2_hom_ext in
open Opposite Bicategory.Opposite in
/-- The "self-duality" of `EffBurnside C`: it sends a span `x ← c → y` to
`y ← c → x` . -/
@[simps!]
noncomputable def duality : (EffBurnside C) ⥤ᵖ (EffBurnside C)ᵒᵖ where
  obj J := op J
  map {X Y} f := Quiver.Hom.op <|
    .mk
      { apex := f.of.apex
        l := f.of.r
        r := f.of.l
        wl := by tauto
        wr := by tauto  }
  map₂ {X Y} {f g} η :=
    Bicategory.Opposite.op2 <|
      .mk <| Spans.mkIso₂
        { hom := η.iso.hom.hom
          inv := η.iso.inv.hom }
  mapId x := Iso.op2 <| Core.isoMk <| Spans.mkIso₂ (.refl _)
  mapComp {_ _ _} f g := Iso.op2 <| Core.isoMk <| Spans.mkIso₂
    { hom := Spans.compLiftApex (Spans.πᵣ _ _) (Spans.πₗ _ _)
      inv := Spans.compLiftApex (Spans.πᵣ _ _) (Spans.πₗ _ _)
        (by simpa using (Spans.comp_comm _ _).symm)
      hom_inv_id := by dsimp; ext <;> simp
      inv_hom_id := by dsimp; ext <;> simp }
  map₂_whisker_left := by intros; dsimp; ext; dsimp; ext <;> simp
  map₂_whisker_right := by intros; dsimp; ext; dsimp; ext <;> simp
  map₂_associator := by intros; dsimp; ext; dsimp; ext <;> simp
  map₂_left_unitor := by intros; dsimp; ext; simp
  map₂_right_unitor := by intros; dsimp; ext; simp

end EffBurnside

end CategoryTheory
