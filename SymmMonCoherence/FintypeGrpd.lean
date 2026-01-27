/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Data.Fintype.Sum

/-! # The groupoid of finite types and bijections

In this file, we construct by hand a symmetric monoidal
category structure on the groupoid of finite type, i.e
on Core (FintypeCat).

-/

universe u

@[expose] public section

namespace CategoryTheory

abbrev FintypeGrpd := Core FintypeCat.{u}

instance instCoeSort : CoeSort FintypeGrpd Type* :=
  ⟨fun x ↦ x.of.carrier⟩

namespace FintypeGrpd

def tensorObj (x y : FintypeGrpd.{u}) :
    FintypeGrpd.{u} := .mk <| .of <| x.of ⊕ y.of

open FintypeCat

def tensorUnit : FintypeGrpd.{u} := .mk <| .of <| PEmpty.{u + 1}

instance : IsEmpty tensorUnit.{u} := inferInstanceAs (IsEmpty (PEmpty.{u + 1}))

def mkHom {x y : FintypeGrpd.{u}} (f : x ≃ y) : x ⟶ y :=
  .mk <| FintypeCat.equivEquivIso.{u} <| f

def mkIso {x y : FintypeGrpd.{u}} (f : x ≃ y) : x ≅ y :=
  Groupoid.isoEquivHom _ _ |>.symm <| mkHom f

@[simp]
lemma mkHom_iso_hom_apply
    {x y : FintypeGrpd.{u}} (f : x ≃ y) (t : x) :
    (mkHom f).iso.hom t = f t := rfl

@[simp]
lemma mkHom_iso_inv_apply
    {x y : FintypeGrpd.{u}} (f : x ≃ y) (t : y) :
    (mkHom f).iso.inv t = f.symm t := rfl

@[simp]
lemma mkIso_hom_iso_hom_apply
    {x y : FintypeGrpd.{u}} (f : x ≃ y) (t : x) :
    (mkIso f).hom.iso.hom t = f t := rfl

@[simp]
lemma mkIso_hom_iso_inv_apply
    {x y : FintypeGrpd.{u}} (f : x ≃ y) (t : y) :
    (mkIso f).hom.iso.inv t = f.symm t := rfl

@[simp]
lemma mkIso_inv_iso_hom_apply
    {x y : FintypeGrpd.{u}} (f : x ≃ y) (t : y) :
    (mkIso f).inv.iso.hom t = f.symm t := rfl

@[simp]
lemma mkIso_inv_iso_inv_apply
    {x y : FintypeGrpd.{u}} (f : x ≃ y) (t : x) :
    (mkIso f).inv.iso.inv t = f t := rfl

def tensorHom {x x' y y' : FintypeGrpd.{u}} (f : x ⟶ x') (g : y ⟶ y') :
    tensorObj x y ⟶ tensorObj x' y' :=
  mkHom <|
    Equiv.sumCongr (equivEquivIso.symm f.iso) (equivEquivIso.symm g.iso)

def associator (x y z : FintypeGrpd.{u}) :
    tensorObj (tensorObj x y) z ≅ tensorObj x (tensorObj y z) :=
  mkIso <| Equiv.sumAssoc _ _ _

def leftUnitor (x : FintypeGrpd.{u}) : tensorObj tensorUnit x ≅ x :=
  mkIso <| Equiv.emptySum _ _

def rightUnitor (x : FintypeGrpd.{u}) : tensorObj x tensorUnit ≅ x :=
  mkIso <| Equiv.sumEmpty _ _

instance : MonoidalCategoryStruct FintypeGrpd.{u} where
  tensorObj := tensorObj
  tensorHom := tensorHom
  whiskerLeft x {_ _} f := tensorHom (𝟙 x) f
  whiskerRight f x := tensorHom f (𝟙 x)
  tensorUnit := tensorUnit
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  associator := associator

open scoped MonoidalCategory

instance : IsEmpty (𝟙_ (FintypeGrpd.{u})) := inferInstanceAs (IsEmpty (PEmpty.{u + 1}))

/- An equivalence to help type-checking when working with the tensor product in FintypeGrpd -/
def tensorObjEquiv (x y : FintypeGrpd.{u}) : x.of ⊕ y.of ≃ (x ⊗ y).of := Equiv.refl _

/-- The left inclution from x.of to (x ⊗ y).of. Note that this is
a plain function and not a morphism in FintypeGrpd (it is not an equivalence). -/
@[match_pattern]
def inl (x y : FintypeGrpd.{u}) : x.of → (x ⊗ y).of := fun k ↦ tensorObjEquiv x y (Sum.inl k)

/-- The right inclution from y.of to (x ⊗ y).of. Note that this is
a plain function and not a morphism in FintypeGrpd (it is not an equivalence). -/
@[match_pattern]
def inr (x y : FintypeGrpd.{u}) : y.of → (x ⊗ y).of := fun k ↦ tensorObjEquiv x y (Sum.inr k)

@[simp, grind =]
lemma tensorObjEquiv_inl (x y : FintypeGrpd.{u}) (k : x.of) :
    tensorObjEquiv x y (Sum.inl k) = inl x y k := rfl

@[simp, grind =]
lemma tensorObjEquiv_inr (x y : FintypeGrpd.{u}) (k : y.of) :
    tensorObjEquiv x y (Sum.inr k) = inr x y k := rfl

@[simp, grind =]
lemma tensorObjEquiv_symm_inl (x y : FintypeGrpd.{u}) (k : x.of) :
    (tensorObjEquiv x y).symm (inl x y k) = Sum.inl k := rfl

@[simp, grind =]
lemma tensorObjEquiv_symm_inr (x y : FintypeGrpd.{u}) (k : y.of) :
    (tensorObjEquiv x y).symm (inr x y k) = Sum.inr k := rfl

@[cases_eliminator, induction_eliminator]
def tensorObjCases {x y : FintypeGrpd.{u}}
    {motive : (x ⊗ y).of → Sort*}
    (left : ∀ (t : x.of), motive (inl x y t))
    (right : ∀ (t : y.of), motive (inr x y t)) (t : (x ⊗ y).of) :
    motive t := by
  change _ ⊕ _ at t
  cases t with
  | inl val => exact left val
  | inr val => exact right val

@[simp]
lemma tensorObjCases_inl {x y : FintypeGrpd.{u}}
    (motive : (x ⊗ y).of → Sort*)
    (left : ∀ (t : x.of), motive (inl x y t))
    (right : ∀ (t : y.of), motive (inr x y t))
    (t : x.of) :
    tensorObjCases left right (inl _ _ t) = left t :=
  rfl

@[simp]
lemma tensorObjCases_inr {x y : FintypeGrpd.{u}}
    (motive : (x ⊗ y).of → Sort*)
    (left : ∀ (t : x.of), motive (inl x y t))
    (right : ∀ (t : y.of), motive (inr x y t))
    (t : y.of) :
    tensorObjCases left right (inr _ _ t) = right t :=
  rfl

@[simp, grind =]
lemma tensorHom_iso_hom_inl {x x' y y' : FintypeGrpd.{u}} (f : x ⟶ x') (g : y ⟶ y') (u : x.of) :
    (f ⊗ₘ g).iso.hom (inl _ _ u) = inl _ _ (f.iso.hom u) := rfl

@[simp, grind =]
lemma tensorHom_iso_hom_inr {x x' y y' : FintypeGrpd.{u}} (f : x ⟶ x') (g : y ⟶ y') (u : y.of) :
    (f ⊗ₘ g).iso.hom (inr _ _ u) = inr _ _ (g.iso.hom u) := rfl

@[simp, grind =]
lemma whiskerLeft_iso_hom_inl
    (x : FintypeGrpd.{u}) {y y' : FintypeGrpd.{u}} (f : y ⟶ y') (u : x.of) :
    (x ◁ f).iso.hom (inl _ _ u) = inl _ _ u := rfl

@[simp, grind =]
lemma whiskerLeft_iso_hom_inr
    (x : FintypeGrpd.{u}) {y y' : FintypeGrpd.{u}} (f : y ⟶ y') (u : y.of) :
    (x ◁ f).iso.hom (inr _ _ u) = inr _ _ (f.iso.hom u) := rfl

@[simp, grind =]
lemma whiskerRight_iso_hom_inl
    {x x' : FintypeGrpd.{u}} (f : x ⟶ x') (y : FintypeGrpd.{u}) (u : x.of) :
    (f ▷ y).iso.hom (inl _ _ u) = inl _ _ (f.iso.hom u) := rfl

@[simp, grind =]
lemma whiskerRight_iso_hom_inr
    {x x' : FintypeGrpd.{u}} (f : x ⟶ x') (y : FintypeGrpd.{u}) (u : y.of) :
    (f ▷ y).iso.hom (inr _ _ u) = inr _ _ u := rfl

@[simp, grind =]
lemma whiskerLeft_iso_inv_inl
    (x : FintypeGrpd.{u}) {y y' : FintypeGrpd.{u}} (f : y ⟶ y') (u : x.of) :
    (x ◁ f).iso.inv (inl _ _ u) = inl _ _ u := rfl

@[simp, grind =]
lemma whiskerLeft_iso_inv_inr
    (x : FintypeGrpd.{u}) {y y' : FintypeGrpd.{u}} (f : y ⟶ y') (u : y'.of) :
    (x ◁ f).iso.inv (inr _ _ u) = inr _ _ (f.iso.inv u) := rfl

@[simp, grind =]
lemma whiskerRight_iso_inv_inl
    {x x' : FintypeGrpd.{u}} (f : x ⟶ x') (y : FintypeGrpd.{u}) (u : x'.of) :
    (f ▷ y).iso.inv (inl _ _ u) = inl _ _ (f.iso.inv u) := rfl

@[simp, grind =]
lemma whiskerRight_iso_inv_inr
    {x x' : FintypeGrpd.{u}} (f : x ⟶ x') (y : FintypeGrpd.{u}) (u : y.of) :
    (f ▷ y).iso.inv (inr _ _ u) = inr _ _ u := rfl

lemma tensorHom_comp_tensorHom {x x' x'' y y' y'' : FintypeGrpd.{u}}
    (f : x ⟶ x') (f' : x' ⟶ x'') (g : y ⟶ y') (g' : y' ⟶ y'') :
    (f ⊗ₘ g) ≫ (f' ⊗ₘ g') = (f ≫ f') ⊗ₘ (g ≫ g') := by
  ext t
  cases t with simp

@[simp, grind =]
lemma associator_hom_left_left (x y z : FintypeGrpd.{u}) (t : x.of) :
    (α_ x y z).hom.iso.hom (inl _ _ <| inl _ _ t) = inl _ _ t := rfl

@[simp, grind =]
lemma associator_hom_left_right (x y z : FintypeGrpd.{u}) (t : y.of) :
    (α_ x y z).hom.iso.hom (inl _ _ <| inr _ _ t) = inr _ _ (inl _ _ t) := rfl

@[simp, grind =]
lemma associator_hom_right (x y z : FintypeGrpd.{u}) (t : z.of) :
    (α_ x y z).hom.iso.hom (inr _ _ t) = inr _ _ (inr _ _ t) := rfl

@[simp, grind =]
lemma associator_inv_left_left (x y z : FintypeGrpd.{u}) (t : x.of) :
    (α_ x y z).inv.iso.hom (inl _ _ t) = (inl _ _ <| inl _ _ t) := rfl

@[simp, grind =]
lemma associator_inv_left_right (x y z : FintypeGrpd.{u}) (t : y.of) :
    (α_ x y z).inv.iso.hom (inr _ _ (inl _ _ t)) = (inl _ _ <| inr _ _ t) := rfl

@[simp, grind =]
lemma associator_inv_right (x y z : FintypeGrpd.{u}) (t : z.of) :
    (α_ x y z).inv.iso.hom (inr _ _ (inr _ _ t)) = (inr _ _ t) := rfl

@[simp, grind =] lemma leftUnitor_hom_right (x : FintypeGrpd.{u}) (t : x.of) :
      (λ_ x).hom.iso.hom (inr _ _ t) = t := rfl

@[simp, grind =] lemma rightUnitor_hom_right (x : FintypeGrpd.{u}) (t : x.of) :
      (ρ_ x).hom.iso.hom (inl _ _ t) = t := rfl

@[simp, grind =] lemma leftUnitor_hom_inv (x : FintypeGrpd.{u}) (t : x.of) :
      (λ_ x).hom.iso.inv t = inr _ _ t := rfl

@[simp, grind =] lemma rightUnitor_hom_inv (x : FintypeGrpd.{u}) (t : x.of) :
      (ρ_ x).hom.iso.inv t = inl _ _ t := rfl

section dupe

-- TODO/FIXME: lessen duplication via good simp nf
@[simp, grind =]
lemma associator_hom_left_left' (x y z : FintypeGrpd.{u}) (t : x.of) :
    (α_ x y z).inv.iso.inv (inl _ _ <| inl _ _ t) = inl _ _ t := rfl

@[simp, grind =]
lemma associator_hom_left_right' (x y z : FintypeGrpd.{u}) (t : y.of) :
    (α_ x y z).inv.iso.inv (inl _ _ <| inr _ _ t) = inr _ _ (inl _ _ t) := rfl

@[simp, grind =]
lemma associator_hom_right' (x y z : FintypeGrpd.{u}) (t : z.of) :
    (α_ x y z).inv.iso.inv (inr _ _ t) = inr _ _ (inr _ _ t) := rfl

@[simp, grind =]
lemma associator_inv_left_left' (x y z : FintypeGrpd.{u}) (t : x.of) :
    (α_ x y z).hom.iso.inv (inl _ _ t) = (inl _ _ <| inl _ _ t) := rfl

@[simp, grind =]
lemma associator_inv_left_right' (x y z : FintypeGrpd.{u}) (t : y.of) :
    (α_ x y z).hom.iso.inv (inr _ _ (inl _ _ t)) = (inl _ _ <| inr _ _ t) := rfl

@[simp, grind =]
lemma associator_inv_right' (x y z : FintypeGrpd.{u}) (t : z.of) :
    (α_ x y z).hom.iso.inv (inr _ _ (inr _ _ t)) = (inr _ _ t) := rfl

@[simp, grind =] lemma leftUnitor_hom_right' (x : FintypeGrpd.{u}) (t : x.of) :
      (λ_ x).inv.iso.inv (inr _ _ t) = t := rfl

@[simp, grind =] lemma rightUnitor_hom_right' (x : FintypeGrpd.{u}) (t : x.of) :
      (ρ_ x).inv.iso.inv (inl _ _ t) = t := rfl

@[simp, grind =] lemma leftUnitor_hom_inv' (x : FintypeGrpd.{u}) (t : x.of) :
      (λ_ x).inv.iso.hom t = inr _ _ t := rfl

@[simp, grind =] lemma rightUnitor_hom_inv' (x : FintypeGrpd.{u}) (t : x.of) :
      (ρ_ x).inv.iso.hom t = inl _ _ t := rfl

end dupe

instance : MonoidalCategory FintypeGrpd.{u} where
  tensorHom_def f g := by ext i; cases i with simp
  id_tensorHom_id x y := by ext i; cases i with simp
  tensorHom_comp_tensorHom f g f' g' := tensorHom_comp_tensorHom _ _ _ _
  whiskerLeft_id x y := by ext i; cases i with simp
  id_whiskerRight x y := by ext i; cases i with simp
  associator_naturality f g h := by
    ext i
    cases i with
    | left t => cases t with
      | left t => simp
      | right t => simp
    | right t => simp
  leftUnitor_naturality f := by
    ext i
    cases i with
    | left t => exact IsEmpty.elim inferInstance t
    | right t => simp
  rightUnitor_naturality f := by
    ext i
    cases i with
    | left t => simp
    | right t => exact IsEmpty.elim inferInstance t
  pentagon x y z t := by
    ext i
    cases i with
    | left i => cases i with
      | left i => cases i with
        | right i => simp
        | left i => simp
      | right i => simp
    | right i => simp
  triangle x y := by
    ext i
    cases i with
    | left i => cases i with
      | left i => simp
      | right i => exact IsEmpty.elim inferInstance i
    | right i => simp

section Symmetric

def braid (x y : FintypeGrpd.{u}) : x ⊗ y ≅ y ⊗ x :=
  Groupoid.isoEquivHom _ _ |>.symm <|
    .mk <| FintypeCat.equivEquivIso <| Equiv.sumComm _ _

lemma braid_iso_hom_inl (x y : FintypeGrpd.{u}) (t : x.of) :
    (braid x y).hom.iso.hom (inl _ _ t) = inr _ _ t := rfl

lemma braid_iso_hom_inr (x y : FintypeGrpd.{u}) (t : y.of) :
    (braid x y).hom.iso.hom (inr _ _ t) = inl _ _ t := rfl

lemma braid_iso_inv_inr (x y : FintypeGrpd.{u}) (t : x.of) :
    (braid x y).inv.iso.hom (inr _ _ t) = inl _ _ t := rfl

lemma braid_iso_inv_inl (x y : FintypeGrpd.{u}) (t : y.of) :
    (braid x y).inv.iso.hom (inl _ _ t) = inr _ _ t := rfl

attribute [local simp] braid_iso_hom_inr braid_iso_hom_inl braid_iso_inv_inr braid_iso_inv_inl in
instance : SymmetricCategory FintypeGrpd.{u} where
  braiding := braid
  braiding_naturality_left := by intros; ext i; cases i with simp
  braiding_naturality_right := by intros; ext i; cases i with simp
  hexagon_forward := by
    intros
    ext i
    cases i with
    | left t => cases t with
      | left t => simp
      | right t => simp
    | right t => simp
  hexagon_reverse := by
    intros
    ext i
    cases i with
    | left t => simp
    | right t => cases t with simp
  symmetry := by intros; ext i; cases i with simp

@[simp, grind =]
lemma braiding_iso_hom_inl (x y : FintypeGrpd.{u}) (t : x.of) :
    (β_ x y).hom.iso.hom (inl _ _ t) = inr _ _ t := rfl

@[simp, grind =]
lemma braiding_iso_hom_inr (x y : FintypeGrpd.{u}) (t : y.of) :
    (β_ x y).hom.iso.hom (inr _ _ t) = inl _ _ t := rfl

@[simp, grind =]
lemma braiding_iso_inv_inr (x y : FintypeGrpd.{u}) (t : x.of) :
    (β_ x y).inv.iso.hom (inr _ _ t) = inl _ _ t := rfl

@[simp, grind =]
lemma braiding_iso_inv_inl (x y : FintypeGrpd.{u}) (t : y.of) :
    (β_ x y).inv.iso.hom (inl _ _ t) = inr _ _ t := rfl

section dupe

@[simp, grind =]
lemma braiding_iso_hom_inl' (x y : FintypeGrpd.{u}) (t : x.of) :
    (β_ x y).inv.iso.inv (inl _ _ t) = inr _ _ t := rfl

@[simp, grind =]
lemma braiding_iso_hom_inr' (x y : FintypeGrpd.{u}) (t : y.of) :
    (β_ x y).inv.iso.inv (inr _ _ t) = inl _ _ t := rfl

@[simp, grind =]
lemma braiding_iso_inv_inr' (x y : FintypeGrpd.{u}) (t : x.of) :
    (β_ x y).hom.iso.inv (inr _ _ t) = inl _ _ t := rfl

@[simp, grind =]
lemma braiding_iso_inv_inl' (x y : FintypeGrpd.{u}) (t : y.of) :
    (β_ x y).hom.iso.inv (inl _ _ t) = inr _ _ t := rfl

end dupe

end Symmetric

end FintypeGrpd

end CategoryTheory
