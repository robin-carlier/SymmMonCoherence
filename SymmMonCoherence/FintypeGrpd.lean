/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.Data.Fintype.Sum

/-! # The groupoid of finite types and bijections

In this file, we construct by hand a symmetric monoidal
category structure on the groupoid of finite types, i.e.
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
@[no_expose] def tensorObjEquiv (x y : FintypeGrpd.{u}) : x.of ⊕ y.of ≃ (x ⊗ y).of := Equiv.refl _

/-- The left inclusion from x.of to (x ⊗ y).of. Note that this is
a plain function and not a morphism in FintypeGrpd (it is not an equivalence). -/
@[match_pattern]
def inl (x y : FintypeGrpd.{u}) : x.of → (x ⊗ y).of := fun k ↦ tensorObjEquiv x y (Sum.inl k)

/-- The right inclusion from y.of to (x ⊗ y).of. Note that this is
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
    (tensorObjEquiv x y).symm (inl x y k) = Sum.inl k := (rfl)

@[simp, grind =]
lemma tensorObjEquiv_symm_inr (x y : FintypeGrpd.{u}) (k : y.of) :
    (tensorObjEquiv x y).symm (inr x y k) = Sum.inr k := (rfl)

@[cases_eliminator, induction_eliminator]
lemma tensor_obj_cases {x y : FintypeGrpd.{u}}
    {motive : (x ⊗ y).of → Prop}
    (left : ∀ (t : x.of), motive (inl x y t))
    (right : ∀ (t : y.of), motive (inr x y t)) (t : (x ⊗ y).of) :
    motive t := by
  change _ ⊕ _ at t
  cases t with
  | inl val => exact left val
  | inr val => exact right val

@[simp, grind =]
lemma tensorHom_iso_hom_inl {x x' y y' : FintypeGrpd.{u}} (f : x ⟶ x') (g : y ⟶ y') (u : x.of) :
    (f ⊗ₘ g).iso.hom (inl _ _ u) = inl _ _ (f.iso.hom u) := (rfl)

@[simp, grind =]
lemma tensorHom_iso_hom_inr {x x' y y' : FintypeGrpd.{u}} (f : x ⟶ x') (g : y ⟶ y') (u : y.of) :
    (f ⊗ₘ g).iso.hom (inr _ _ u) = inr _ _ (g.iso.hom u) := (rfl)

@[simp, grind =]
lemma whiskerLeft_iso_hom_inl
    (x : FintypeGrpd.{u}) {y y' : FintypeGrpd.{u}} (f : y ⟶ y') (u : x.of) :
    (x ◁ f).iso.hom (inl _ _ u) = inl _ _ u := (rfl)

@[simp, grind =]
lemma whiskerLeft_iso_hom_inr
    (x : FintypeGrpd.{u}) {y y' : FintypeGrpd.{u}} (f : y ⟶ y') (u : y.of) :
    (x ◁ f).iso.hom (inr _ _ u) = inr _ _ (f.iso.hom u) := (rfl)

@[simp, grind =]
lemma whiskerRight_iso_hom_inl
    {x x' : FintypeGrpd.{u}} (f : x ⟶ x') (y : FintypeGrpd.{u}) (u : x.of) :
    (f ▷ y).iso.hom (inl _ _ u) = inl _ _ (f.iso.hom u) := (rfl)

@[simp, grind =]
lemma whiskerRight_iso_hom_inr
    {x x' : FintypeGrpd.{u}} (f : x ⟶ x') (y : FintypeGrpd.{u}) (u : y.of) :
    (f ▷ y).iso.hom (inr _ _ u) = inr _ _ u := (rfl)

@[simp, grind =]
lemma whiskerLeft_iso_inv_inl
    (x : FintypeGrpd.{u}) {y y' : FintypeGrpd.{u}} (f : y ⟶ y') (u : x.of) :
    (x ◁ f).iso.inv (inl _ _ u) = inl _ _ u := (rfl)

@[simp, grind =]
lemma whiskerLeft_iso_inv_inr
    (x : FintypeGrpd.{u}) {y y' : FintypeGrpd.{u}} (f : y ⟶ y') (u : y'.of) :
    (x ◁ f).iso.inv (inr _ _ u) = inr _ _ (f.iso.inv u) := (rfl)

@[simp, grind =]
lemma whiskerRight_iso_inv_inl
    {x x' : FintypeGrpd.{u}} (f : x ⟶ x') (y : FintypeGrpd.{u}) (u : x'.of) :
    (f ▷ y).iso.inv (inl _ _ u) = inl _ _ (f.iso.inv u) := (rfl)

@[simp, grind =]
lemma whiskerRight_iso_inv_inr
    {x x' : FintypeGrpd.{u}} (f : x ⟶ x') (y : FintypeGrpd.{u}) (u : y.of) :
    (f ▷ y).iso.inv (inr _ _ u) = inr _ _ u := (rfl)

lemma tensorHom_comp_tensorHom {x x' x'' y y' y'' : FintypeGrpd.{u}}
    (f : x ⟶ x') (f' : x' ⟶ x'') (g : y ⟶ y') (g' : y' ⟶ y'') :
    (f ⊗ₘ g) ≫ (f' ⊗ₘ g') = (f ≫ f') ⊗ₘ (g ≫ g') := by
  ext t
  cases t with simp

@[simp, grind =]
lemma associator_hom_left_left (x y z : FintypeGrpd.{u}) (t : x.of) :
    (α_ x y z).hom.iso.hom (inl _ _ <| inl _ _ t) = inl _ _ t := (rfl)

@[simp, grind =]
lemma associator_hom_left_right (x y z : FintypeGrpd.{u}) (t : y.of) :
    (α_ x y z).hom.iso.hom (inl _ _ <| inr _ _ t) = inr _ _ (inl _ _ t) := (rfl)

@[simp, grind =]
lemma associator_hom_right (x y z : FintypeGrpd.{u}) (t : z.of) :
    (α_ x y z).hom.iso.hom (inr _ _ t) = inr _ _ (inr _ _ t) := (rfl)

@[simp, grind =]
lemma associator_inv_left_left (x y z : FintypeGrpd.{u}) (t : x.of) :
    (α_ x y z).inv.iso.hom (inl _ _ t) = (inl _ _ <| inl _ _ t) := (rfl)

@[simp, grind =]
lemma associator_inv_left_right (x y z : FintypeGrpd.{u}) (t : y.of) :
    (α_ x y z).inv.iso.hom (inr _ _ (inl _ _ t)) = (inl _ _ <| inr _ _ t) := (rfl)

@[simp, grind =]
lemma associator_inv_right (x y z : FintypeGrpd.{u}) (t : z.of) :
    (α_ x y z).inv.iso.hom (inr _ _ (inr _ _ t)) = (inr _ _ t) := (rfl)

@[simp, grind =] lemma leftUnitor_hom_right (x : FintypeGrpd.{u}) (t : x.of) :
      (λ_ x).hom.iso.hom (inr _ _ t) = t := (rfl)

@[simp, grind =] lemma rightUnitor_hom_right (x : FintypeGrpd.{u}) (t : x.of) :
      (ρ_ x).hom.iso.hom (inl _ _ t) = t := (rfl)

@[simp, grind =] lemma leftUnitor_hom_inv (x : FintypeGrpd.{u}) (t : x.of) :
      (λ_ x).hom.iso.inv t = inr _ _ t := (rfl)

@[simp, grind =] lemma rightUnitor_hom_inv (x : FintypeGrpd.{u}) (t : x.of) :
      (ρ_ x).hom.iso.inv t = inl _ _ t := (rfl)

section dupe

-- TODO/FIXME: lessen duplication via good simp nf
@[simp, grind =]
lemma associator_hom_left_left' (x y z : FintypeGrpd.{u}) (t : x.of) :
    (α_ x y z).inv.iso.inv (inl _ _ <| inl _ _ t) = inl _ _ t := (rfl)

@[simp, grind =]
lemma associator_hom_left_right' (x y z : FintypeGrpd.{u}) (t : y.of) :
    (α_ x y z).inv.iso.inv (inl _ _ <| inr _ _ t) = inr _ _ (inl _ _ t) := (rfl)

@[simp, grind =]
lemma associator_hom_right' (x y z : FintypeGrpd.{u}) (t : z.of) :
    (α_ x y z).inv.iso.inv (inr _ _ t) = inr _ _ (inr _ _ t) := (rfl)

@[simp, grind =]
lemma associator_inv_left_left' (x y z : FintypeGrpd.{u}) (t : x.of) :
    (α_ x y z).hom.iso.inv (inl _ _ t) = (inl _ _ <| inl _ _ t) := (rfl)

@[simp, grind =]
lemma associator_inv_left_right' (x y z : FintypeGrpd.{u}) (t : y.of) :
    (α_ x y z).hom.iso.inv (inr _ _ (inl _ _ t)) = (inl _ _ <| inr _ _ t) := (rfl)

@[simp, grind =]
lemma associator_inv_right' (x y z : FintypeGrpd.{u}) (t : z.of) :
    (α_ x y z).hom.iso.inv (inr _ _ (inr _ _ t)) = (inr _ _ t) := (rfl)

@[simp, grind =] lemma leftUnitor_hom_right' (x : FintypeGrpd.{u}) (t : x.of) :
      (λ_ x).inv.iso.inv (inr _ _ t) = t := (rfl)

@[simp, grind =] lemma rightUnitor_hom_right' (x : FintypeGrpd.{u}) (t : x.of) :
      (ρ_ x).inv.iso.inv (inl _ _ t) = t := (rfl)

@[simp, grind =] lemma leftUnitor_hom_inv' (x : FintypeGrpd.{u}) (t : x.of) :
      (λ_ x).inv.iso.hom t = inr _ _ t := (rfl)

@[simp, grind =] lemma rightUnitor_hom_inv' (x : FintypeGrpd.{u}) (t : x.of) :
      (ρ_ x).inv.iso.hom t = inl _ _ t := (rfl)

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
    (braid x y).hom.iso.hom (inl _ _ t) = inr _ _ t := (rfl)

lemma braid_iso_hom_inr (x y : FintypeGrpd.{u}) (t : y.of) :
    (braid x y).hom.iso.hom (inr _ _ t) = inl _ _ t := (rfl)

lemma braid_iso_inv_inr (x y : FintypeGrpd.{u}) (t : x.of) :
    (braid x y).inv.iso.hom (inr _ _ t) = inl _ _ t := (rfl)

lemma braid_iso_inv_inl (x y : FintypeGrpd.{u}) (t : y.of) :
    (braid x y).inv.iso.hom (inl _ _ t) = inr _ _ t := (rfl)

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
    (β_ x y).hom.iso.hom (inl _ _ t) = inr _ _ t := (rfl)

@[simp, grind =]
lemma braiding_iso_hom_inr (x y : FintypeGrpd.{u}) (t : y.of) :
    (β_ x y).hom.iso.hom (inr _ _ t) = inl _ _ t := (rfl)

@[simp, grind =]
lemma braiding_iso_inv_inr (x y : FintypeGrpd.{u}) (t : x.of) :
    (β_ x y).inv.iso.hom (inr _ _ t) = inl _ _ t := (rfl)

@[simp, grind =]
lemma braiding_iso_inv_inl (x y : FintypeGrpd.{u}) (t : y.of) :
    (β_ x y).inv.iso.hom (inl _ _ t) = inr _ _ t := (rfl)

section dupe

@[simp, grind =]
lemma braiding_iso_hom_inl' (x y : FintypeGrpd.{u}) (t : x.of) :
    (β_ x y).inv.iso.inv (inl _ _ t) = inr _ _ t := (rfl)

@[simp, grind =]
lemma braiding_iso_hom_inr' (x y : FintypeGrpd.{u}) (t : y.of) :
    (β_ x y).inv.iso.inv (inr _ _ t) = inl _ _ t := (rfl)

@[simp, grind =]
lemma braiding_iso_inv_inr' (x y : FintypeGrpd.{u}) (t : x.of) :
    (β_ x y).hom.iso.inv (inr _ _ t) = inl _ _ t := (rfl)

@[simp, grind =]
lemma braiding_iso_inv_inl' (x y : FintypeGrpd.{u}) (t : y.of) :
    (β_ x y).hom.iso.inv (inl _ _ t) = inr _ _ t := (rfl)

end dupe

end Symmetric

end FintypeGrpd

abbrev FintypeGrpdOver (J : Type u) : Type (u + 1) :=
    CostructuredArrow (Core.inclusion FintypeCat.{u} ⋙ FintypeCat.incl) J

namespace FintypeGrpdOver

variable (J : Type u)
abbrev proj : (FintypeGrpdOver J) ⥤ FintypeGrpd.{u} := CostructuredArrow.proj _ _

example : (proj J).Faithful := by infer_instance

open MonoidalCategory
variable {J}

/-- The tensor product of two objects in FintypeGrpdOver J. -/
def tensorObj (x y : FintypeGrpdOver J) :
    FintypeGrpdOver J := .mk (Y := x.left ⊗ y.left) (f :=
      fun i ↦ (Sum.elim x.hom y.hom) ((FintypeGrpd.tensorObjEquiv x.left y.left).symm i))

lemma tensorObj_hom_inl' {x y : FintypeGrpdOver J} (i : x.left) :
    (tensorObj x y).hom (FintypeGrpd.inl _ _ i) = x.hom i := by simp [tensorObj]

lemma tensorObj_hom_inr' {x y : FintypeGrpdOver J} (i : y.left) :
    (tensorObj x y).hom (FintypeGrpd.inr _ _ i) = y.hom i := by simp [tensorObj]

def tensorUnit : FintypeGrpdOver J := .mk (Y := 𝟙_ _) (f := fun j ↦ PEmpty.elim j)

def associator (x y z : FintypeGrpdOver J) :
    tensorObj (tensorObj x y) z ≅ tensorObj x (tensorObj y z) :=
  CostructuredArrow.isoMk (α_ x.left y.left z.left) (by
    ext i
    dsimp [tensorObj] at i
    cases i with
    | left t => cases t with
      | right t => simp [tensorObj]
      | left t => simp [tensorObj]
    | right t => simp [tensorObj])

def leftUnitor (x : FintypeGrpdOver J) : tensorObj tensorUnit x ≅ x :=
  CostructuredArrow.isoMk (λ_ x.left) (by
    ext i
    dsimp [tensorObj] at i
    cases i with
    | left i => exact PEmpty.elim i
    | right i => simp [tensorObj, tensorUnit])

def rightUnitor (x : FintypeGrpdOver J) : tensorObj x tensorUnit ≅ x :=
  CostructuredArrow.isoMk (ρ_ x.left) (by
    ext i
    dsimp [tensorObj] at i
    cases i with
    | right i => exact PEmpty.elim i
    | left i => simp [tensorObj, tensorUnit])

def tensorHom {x x' y y' : FintypeGrpdOver J} (f : x ⟶ x') (g : y ⟶ y') :
    tensorObj x y ⟶ tensorObj x' y' :=
  CostructuredArrow.homMk
    (f.left ⊗ₘ g.left) (by
    ext i
    dsimp [tensorObj] at i
    cases i with
    | right i => simpa [tensorObj] using congr($(g.w) i)
    | left i => simpa [tensorObj] using congr($(f.w) i))

instance : MonoidalCategoryStruct (FintypeGrpdOver J) where
  tensorObj := tensorObj
  tensorHom := tensorHom
  whiskerLeft x {_ _} f := tensorHom (𝟙 x) f
  whiskerRight f x := tensorHom f (𝟙 x)
  tensorUnit := tensorUnit
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  associator := associator

@[simp, grind =]
lemma tensorObj_left {x y : FintypeGrpdOver J} : (x ⊗ y).left = x.left ⊗ y.left := rfl

@[simp, grind =]
lemma tensorObj_hom_inl {x y : FintypeGrpdOver J} (i : x.left) :
    (x ⊗ y).hom (FintypeGrpd.inl _ _ i) = x.hom i := tensorObj_hom_inl' ..

@[simp, grind =]
lemma tensorObj_hom_inr {x y : FintypeGrpdOver J} (i : y.left) :
    (x ⊗ y).hom (FintypeGrpd.inr _ _ i) = y.hom i := tensorObj_hom_inr' ..

@[simp, grind =]
lemma tensorUnit_left :
    (𝟙_ (FintypeGrpdOver J)).left = 𝟙_ (FintypeGrpd.{u}) := rfl

@[simp, grind =]
lemma associator_hom_left (x y z : FintypeGrpdOver J) :
    (α_ x y z).hom.left = (α_ x.left y.left z.left).hom := rfl

@[simp, grind =]
lemma associator_inv_left (x y z : FintypeGrpdOver J) :
    (α_ x y z).inv.left = (α_ x.left y.left z.left).inv := rfl

@[simp, grind =]
lemma tensorHom_left {x x' y y' : FintypeGrpdOver J} (f : x ⟶ x') (g : y ⟶ y') :
    (f ⊗ₘ g).left = f.left ⊗ₘ g.left := rfl

@[simp, grind =]
lemma whiskerRight_left {x x' : FintypeGrpdOver J} (f : x ⟶ x') (y : FintypeGrpdOver J) :
    (f ▷ y).left = f.left ▷ y.left := rfl

@[simp, grind =]
lemma whiskerLeft_left (x : FintypeGrpdOver J) {y y' : FintypeGrpdOver J} (g : y ⟶ y') :
    (x ◁ g).left = x.left ◁ g.left := rfl

@[simp, grind =]
lemma leftUnitor_hom_left (x : FintypeGrpdOver J) :
    (λ_ x).hom.left = (λ_ x.left).hom := rfl

@[simp, grind =]
lemma leftUnitor_inv_left (x : FintypeGrpdOver J) :
    (λ_ x).inv.left = (λ_ x.left).inv := rfl

@[simp, grind =]
lemma rightUnitor_hom_left (x : FintypeGrpdOver J) :
    (ρ_ x).hom.left = (ρ_ x.left).hom := rfl

@[simp, grind =]
lemma rightUnitor_inv_left (x : FintypeGrpdOver J) :
    (ρ_ x).inv.left = (ρ_ x.left).inv := rfl

instance : MonoidalCategory (FintypeGrpdOver J) :=
  letI : Monoidal.InducingFunctorData (proj J) :=
    { μIso X Y := .refl _
      εIso := .refl _ }
  Monoidal.induced (proj J) this

@[simps! μ_iso δ_iso ε_iso η_iso]
instance : (proj J).Monoidal := Monoidal.fromInducedMonoidal _ _

@[simps! braiding_hom_left braiding_hom_right]
instance : BraidedCategory (FintypeGrpdOver J) where
  braiding x y :=
    CostructuredArrow.isoMk (β_ x.left y.left) (by
      ext i
      dsimp [tensorObj] at i
      cases i with
      | right i => simp
      | left i => simp)

instance : IsEmpty (𝟙_ (FintypeGrpdOver J)).left := inferInstanceAs (IsEmpty (PEmpty.{u + 1}))

end FintypeGrpdOver

end CategoryTheory
