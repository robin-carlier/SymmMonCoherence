/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.EquivFintypeGrpd
public import SymmMonCoherence.Spans.Burnside
public import SymmMonCoherence.Spans.Terminal
public import Mathlib.CategoryTheory.Limits.FintypeCat
public import Mathlib.CategoryTheory.Pi.Monoidal
public import Mathlib.Tactic.DepRewrite

/-! # The Burnside (2,1)-category of finite types. -/

universe u

namespace CategoryTheory

/-- The burnside category of the category of finite type. -/
@[expose] public abbrev BurnsideFintype := Burnside FintypeCat.{u}

namespace BurnsideFintype

/-- The unit object -/
@[expose] public abbrev unit : Burnside (FintypeCat.{u}) := .mk <| .mk <| .of PUnit.{u + 1}

/-- The equivalence between endomorphisms of the terminal object and the groupoid
of finite types and permutations. -/
@[expose] public noncomputable def equivalenceFintypeGrpd : (unit ⟶ unit) ≌ FintypeGrpd :=
  Equivalence.core
    (Spans.spanEndEquivalenceOfIsTerminal (FintypeCat.{u}) unit.as
      (Limits.IsTerminal.ofUniqueHom (fun X ↦
        (FintypeCat.homMk <| fun (x : X) ↦ PUnit.unit))
        (fun X Y ↦ by ext)))

-- TODO The API for this equivalence should be better
@[simp]
public lemma equivalenceFintypeGrpd_obj (S : unit.{u} ⟶ unit) :
    (equivalenceFintypeGrpd.functor.obj S) = .mk S.of.apex :=
  rfl

@[simp]
public lemma equivalenceFintypeGrpd_map_iso_hom {S S' : unit.{u} ⟶ unit} (f : S ⟶ S') :
    (equivalenceFintypeGrpd.functor.map f).iso.hom = f.iso.hom.hom :=
  rfl

@[simp]
public lemma equivalenceFintypeGrpd_map_iso_inv {S S' : unit.{u} ⟶ unit} (f : S ⟶ S') :
    (equivalenceFintypeGrpd.functor.map f).iso.inv = f.iso.inv.hom :=
  rfl

section monoidal

/-! In this section, we construct a monoidal structure on homCategories in BurnsideFintype.
These are inherited from the cocartesian monoidal structure on categories of finite types, but we
construct them by hand here.

This monoidal structure allows for a slightly less painful definition of a functor
`(J.of → SList K.of) ⥤ (J ⟶ K)`, as well as a monoidal structure on said functor.
-/

/-- The tensor unit in each hom-groupoid in the Burnside (2,1)-category is the empty type,
with the two unique maps to the legs. -/
def tensorUnit (J K : BurnsideFintype.{u}) : J ⟶ K :=
  .mk <|
    { apex := .of PEmpty.{u + 1}
      l := FintypeCat.homMk PEmpty.elim.{u + 1}
      r := FintypeCat.homMk PEmpty.elim.{u + 1}
      wl := by tauto
      wr := by tauto }

instance (J K : BurnsideFintype.{u}) : IsEmpty (tensorUnit J K).of.apex := by
  dsimp [tensorUnit]
  infer_instance

variable {J K : BurnsideFintype.{u}}

section structureDefinition

/-- The tensor unit in each hom-groupoid in the Burnside (2,1)-category is the empty type,
with the two unique maps to the legs. -/
def tensorObj (X Y : J ⟶ K) : J ⟶ K :=
  .mk <|
    { apex := .of <| X.of.apex ⊕ Y.of.apex
      l := FintypeCat.homMk (Sum.elim X.of.l Y.of.l)
      r := FintypeCat.homMk (Sum.elim X.of.r Y.of.r)
      wl := by tauto
      wr := by tauto }

-- TODO: cleanup this once automation has improved on FintypeCat
/-- The associator isomorphism for the monoidal structure on spans.
Under the hood, this is `Equiv.sumAssoc`. -/
def associator (X Y Z : J ⟶ K) : tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  Core.isoMk <| Spans.mkIso₂ (FintypeCat.equivEquivIso <| Equiv.sumAssoc _ _ _)
    (by
      ext i
      simp only [tensorObj, ConcreteCategory.comp_apply] at i ⊢
      rw [FintypeCat.homMk_apply, FintypeCat.homMk_apply]
      cases i with
      | inl i =>
        rw [FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply]
        cases i with
        | inl i =>
          rw [Sum.elim_inl, FintypeCat.homMk_apply]
          simp
        | inr i =>
          rw [Sum.elim_inl, FintypeCat.homMk_apply, Equiv.sumAssoc_apply_inl_inr,
            Sum.elim_inr,FintypeCat.homMk_apply]
          simp
      | inr i =>
        rw [Sum.elim_inr, FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply,
          Equiv.sumAssoc_apply_inr, Sum.elim_inr, FintypeCat.homMk_apply]
        simp)
    (by
      ext i
      simp only [tensorObj, ConcreteCategory.comp_apply] at i ⊢
      rw [FintypeCat.homMk_apply, FintypeCat.homMk_apply]
      cases i with
      | inl i =>
        rw [FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply]
        cases i with
        | inl i =>
          rw [Sum.elim_inl, FintypeCat.homMk_apply]
          simp
        | inr i =>
          rw [Sum.elim_inl, FintypeCat.homMk_apply, Equiv.sumAssoc_apply_inl_inr, Sum.elim_inr,
            FintypeCat.homMk_apply]
          simp
      | inr i =>
        rw [Sum.elim_inr, FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply,
          Equiv.sumAssoc_apply_inr, Sum.elim_inr]
        rw [FintypeCat.homMk_apply]
        simp)

/-- The left unitor isomorphism for the monoidal structure on spans.
Under the hood, this is `Equiv.emptySum`. -/
def leftUnitor (X : J ⟶ K) : tensorObj (tensorUnit J K) X ≅ X :=
  Core.isoMk <| Spans.mkIso₂ (FintypeCat.equivEquivIso <| Equiv.emptySum _ _)
    (by
      ext i
      simp only [tensorObj, tensorUnit, ConcreteCategory.comp_apply] at i ⊢
      rw [FintypeCat.homMk_apply]
      cases i with
      | inl i => exact i.elim
      | inr i =>
        rw [Sum.elim_inr, FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply]
        simp only [Equiv.emptySum_apply_inr])
    (by
      ext i
      simp only [tensorObj, tensorUnit, ConcreteCategory.comp_apply] at i ⊢
      rw [FintypeCat.homMk_apply]
      cases i with
      | inl i => exact i.elim
      | inr i =>
        rw [Sum.elim_inr, FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply]
        simp)

/-- The right unitor isomorphism for the monoidal structure on spans.
Under the hood, this is `Equiv.sumEmpty`. -/
def rightUnitor (X : J ⟶ K) : tensorObj X (tensorUnit J K) ≅ X :=
  Core.isoMk <| Spans.mkIso₂ (FintypeCat.equivEquivIso <| Equiv.sumEmpty _ _)
    (by
      ext i
      simp only [tensorObj, tensorUnit, ConcreteCategory.comp_apply] at i ⊢
      rw [FintypeCat.homMk_apply]
      cases i with
      | inl i =>
        rw [Sum.elim_inl, FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply]
        simp
      | inr i => exact i.elim)
    (by
      ext i
      simp only [tensorObj, tensorUnit, ConcreteCategory.comp_apply] at i ⊢
      rw [FintypeCat.homMk_apply]
      cases i with
      | inl i =>
        rw [Sum.elim_inl, FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply]
        simp
      | inr i => exact i.elim)

/-- The tensor product of two morphisms for the monoidal structure on spans.
Under the hood, this is `Equiv.sumCongr`. -/
def tensorHom {X X' Y Y' : J ⟶ K} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorObj X Y ⟶ tensorObj X' Y' :=
  .mk <| Spans.mkIso₂ (FintypeCat.equivEquivIso <|
    Equiv.sumCongr
      (FintypeCat.equivEquivIso.symm ((Spans.forgetLegs J.as K.as).mapIso f.iso))
      (FintypeCat.equivEquivIso.symm ((Spans.forgetLegs J.as K.as).mapIso g.iso)))
    (by
      ext i
      simp only [tensorObj, ConcreteCategory.comp_apply] at i ⊢
      rw [FintypeCat.homMk_apply]
      cases i with
      | inl i =>
        rw [FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply]
        simp only [Equiv.sumCongr_apply, Sum.map_inl, FintypeCat.equivEquivIso_symm_apply_apply,
          Functor.mapIso_hom, Spans.forgetLegs_map, Sum.elim_inl]
        rw [FintypeCat.homMk_apply]
        have := congr($f.iso.hom.hom_l i)
        simpa [-Span.Hom.hom_l] using congr($f.iso.hom.hom_l i)
      | inr i =>
        rw [FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply]
        simp only [Equiv.sumCongr_apply, Sum.map_inr, FintypeCat.equivEquivIso_symm_apply_apply,
          Functor.mapIso_hom, Spans.forgetLegs_map, Sum.elim_inr]
        rw [FintypeCat.homMk_apply]
        have := congr($g.iso.hom.hom_l i)
        simpa [-Span.Hom.hom_l] using congr($g.iso.hom.hom_l i))
    (by
      ext i
      simp only [tensorObj, ConcreteCategory.comp_apply] at i ⊢
      rw [FintypeCat.homMk_apply]
      cases i with
      | inl i =>
        rw [FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply]
        simp only [Equiv.sumCongr_apply, Sum.map_inl, FintypeCat.equivEquivIso_symm_apply_apply,
          Functor.mapIso_hom, Spans.forgetLegs_map, Sum.elim_inl]
        rw [FintypeCat.homMk_apply]
        have := congr($f.iso.hom.hom_r i)
        simpa [-Span.Hom.hom_r] using congr($f.iso.hom.hom_r i)
      | inr i =>
        rw [FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply]
        simp only [Equiv.sumCongr_apply, Sum.map_inr, FintypeCat.equivEquivIso_symm_apply_apply,
          Functor.mapIso_hom, Spans.forgetLegs_map, Sum.elim_inr]
        rw [FintypeCat.homMk_apply]
        have := congr($g.iso.hom.hom_l i)
        simpa [-Span.Hom.hom_r] using congr($g.iso.hom.hom_r i))

@[no_expose] public noncomputable instance : MonoidalCategoryStruct (J ⟶ K) where
  tensorObj := tensorObj
  tensorHom := tensorHom
  whiskerLeft x {_ _} f := tensorHom (𝟙 x) f
  whiskerRight f x := tensorHom f (𝟙 x)
  tensorUnit := tensorUnit J K
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  associator := associator

end structureDefinition

open MonoidalCategory

public section structureAPI

instance : IsEmpty (𝟙_ (J ⟶ K)).of.apex := inferInstanceAs (IsEmpty (PEmpty.{u + 1}))

/-- The equivalence that defines the apex of the tensor product of spans. -/
@[no_expose] noncomputable def tensorObjApexEquiv (X Y : J ⟶ K) :
    (X ⊗ Y).of.apex ≃ X.of.apex ⊕ Y.of.apex :=
  .refl _

/-- The left inclution from x.of.apex to (x ⊗ y).of.apex. Note that this is
a plain function and not a morphism in FintypeGrpd (it is not an equivalence). -/
@[match_pattern]
noncomputable abbrev inl (x y : J ⟶ K) : x.of.apex → (x ⊗ y).of.apex :=
  fun x ↦ (tensorObjApexEquiv _ _).symm (Sum.inl x)

/-- The right inclution from y.of.apex to (x ⊗ y).of.apex. Note that this is
a plain function and not a morphism in FintypeGrpd (it is not an equivalence). -/
@[match_pattern]
noncomputable abbrev inr (x y : J ⟶ K) : y.of.apex → (x ⊗ y).of.apex :=
  fun x ↦ (tensorObjApexEquiv _ _).symm (Sum.inr x)

@[simp, grind =]
lemma tensorObj_l_inl (X Y : J ⟶ K) (x : X.of.apex) :
    (X ⊗ Y).of.l (inl _ _ x) = X.of.l x :=
  (rfl)

@[simp, grind =]
lemma tensorObj_r_inl (X Y : J ⟶ K) (x : X.of.apex) :
    (X ⊗ Y).of.r (inl _ _ x) = X.of.r x :=
  (rfl)

@[simp, grind =]
lemma tensorObj_l_inr (X Y : J ⟶ K) (y : Y.of.apex) :
    (X ⊗ Y).of.l (inr _ _ y) = Y.of.l y :=
  (rfl)

@[simp, grind =]
lemma tensorObj_r_inr (X Y : J ⟶ K) (y : Y.of.apex) :
    (X ⊗ Y).of.r (inr _ _ y) = Y.of.r y :=
  (rfl)

@[simp, grind =]
lemma tensorHom_iso_hom_inl {x x' y y' : J ⟶ K} (f : x ⟶ x') (g : y ⟶ y') (u : x.of.apex) :
    (f ⊗ₘ g).iso.hom.hom (inl _ _ u) = inl _ _ (f.iso.hom.hom u) := (rfl)

@[simp, grind =]
lemma tensorHom_iso_hom_inr {x x' y y' : J ⟶ K} (f : x ⟶ x') (g : y ⟶ y') (u : y.of.apex) :
    (f ⊗ₘ g).iso.hom.hom (inr _ _ u) = inr _ _ (g.iso.hom.hom u) := (rfl)

@[simp, grind =]
lemma whiskerLeft_iso_hom_inl
    (x : J ⟶ K) {y y' : J ⟶ K} (f : y ⟶ y') (u : x.of.apex) :
    (x ◁ f).iso.hom.hom (inl _ _ u) = inl _ _ u := (rfl)

@[simp, grind =]
lemma whiskerLeft_iso_hom_inr
    (x : J ⟶ K) {y y' : J ⟶ K} (f : y ⟶ y') (u : y.of.apex) :
    (x ◁ f).iso.hom.hom (inr _ _ u) = inr _ _ (f.iso.hom.hom u) := (rfl)

@[simp, grind =]
lemma whiskerRight_iso_hom_inl
    {x x' : J ⟶ K} (f : x ⟶ x') (y : J ⟶ K) (u : x.of.apex) :
    (f ▷ y).iso.hom.hom (inl _ _ u) = inl _ _ (f.iso.hom.hom u) := (rfl)

@[simp, grind =]
lemma whiskerRight_iso_hom_inr
    {x x' : J ⟶ K} (f : x ⟶ x') (y : J ⟶ K) (u : y.of.apex) :
    (f ▷ y).iso.hom.hom (inr _ _ u) = inr _ _ u := (rfl)

lemma tensorHom_comp_tensorHom {x x' x'' y y' y'' : J ⟶ K}
    (f : x ⟶ x') (f' : x' ⟶ x'') (g : y ⟶ y') (g' : y' ⟶ y'') :
    (f ⊗ₘ g) ≫ (f' ⊗ₘ g') = (f ≫ f') ⊗ₘ (g ≫ g') := by
  ext t
  obtain ⟨t, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective t
  cases t with simp

@[simp, grind =]
lemma associator_hom_left_left (x y z : J ⟶ K) (t : x.of.apex) :
    (α_ x y z).hom.iso.hom.hom (inl _ _ <| inl _ _ t) = inl _ _ t := (rfl)

@[simp, grind =]
lemma associator_hom_left_right (x y z : J ⟶ K) (t : y.of.apex) :
    (α_ x y z).hom.iso.hom.hom (inl _ _ <| inr _ _ t) = inr _ _ (inl _ _ t) := (rfl)

@[simp, grind =]
lemma associator_hom_right (x y z : J ⟶ K) (t : z.of.apex) :
    (α_ x y z).hom.iso.hom.hom (inr _ _ t) = inr _ _ (inr _ _ t) := (rfl)

@[simp, grind =]
lemma associator_inv_left_left (x y z : J ⟶ K) (t : x.of.apex) :
    (α_ x y z).inv.iso.hom.hom (inl _ _ t) = (inl _ _ <| inl _ _ t) := (rfl)

@[simp, grind =]
lemma associator_inv_left_right (x y z : J ⟶ K) (t : y.of.apex) :
    (α_ x y z).inv.iso.hom.hom (inr _ _ (inl _ _ t)) = (inl _ _ <| inr _ _ t) := (rfl)

@[simp, grind =]
lemma associator_inv_right (x y z : J ⟶ K) (t : z.of.apex) :
    (α_ x y z).inv.iso.hom.hom (inr _ _ (inr _ _ t)) = (inr _ _ t) := (rfl)

@[simp, grind =] lemma leftUnitor_hom_right (x : J ⟶ K) (t : x.of.apex) :
    (λ_ x).hom.iso.hom.hom (inr _ _ t) = t := (rfl)

@[simp, grind =] lemma rightUnitor_hom_right (x : J ⟶ K) (t : x.of.apex) :
    (ρ_ x).hom.iso.hom.hom (inl _ _ t) = t := (rfl)

noncomputable instance : MonoidalCategory (J ⟶ K) where
  tensorHom_def f g := by
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with simp
  id_tensorHom_id x y := by
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with simp
  tensorHom_comp_tensorHom f g f' g' := tensorHom_comp_tensorHom _ _ _ _
  whiskerLeft_id x y := by
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with simp
  id_whiskerRight x y := by
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with simp
  associator_naturality f g h := by
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with
    | inl t =>
      obtain ⟨t, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective t
      cases t with
      | inl t => simp
      | inr t => simp
    | inr t => simp
  leftUnitor_naturality f := by
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with
    | inl t => exact IsEmpty.elim inferInstance t
    | inr t => simp
  rightUnitor_naturality f := by
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with
    | inl t => simp
    | inr t => exact IsEmpty.elim inferInstance t
  pentagon x y z t := by
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with
    | inl i =>
      obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
      cases i with
      | inl i =>
        obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
        cases i with
        | inr i => simp
        | inl i => simp
      | inr i => simp
    | inr i => simp
  triangle x y := by
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with
    | inl i =>
      obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
      cases i with
      | inl i => simp
      | inr i => exact IsEmpty.elim inferInstance i
    | inr i => simp

end structureAPI

section Symmetric

/-- The braid isomorphism for the symmetric monoidal structure on homCategories in
`BurnsideFintype`. -/
noncomputable def braid (x y : J ⟶ K) : x ⊗ y ≅ y ⊗ x :=
  Core.isoMk <| Spans.mkIso₂ (FintypeCat.equivEquivIso <| Equiv.sumComm _ _)
    (by
      ext i
      obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
      cases i with rfl)
    (by
      ext i
      obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
      cases i with rfl)

lemma braid_iso_hom_inl (x y : J ⟶ K) (t : x.of.apex) :
    (braid x y).hom.iso.hom.hom (inl _ _ t) = inr _ _ t := rfl

lemma braid_iso_hom_inr (x y : J ⟶ K) (t : y.of.apex) :
    (braid x y).hom.iso.hom.hom (inr _ _ t) = inl _ _ t := rfl

lemma braid_iso_inv_inr (x y : J ⟶ K) (t : x.of.apex) :
    (braid x y).inv.iso.hom.hom (inr _ _ t) = inl _ _ t := rfl

lemma braid_iso_inv_inl (x y : J ⟶ K) (t : y.of.apex) :
    (braid x y).inv.iso.hom.hom (inl _ _ t) = inr _ _ t := rfl

attribute [local simp] braid_iso_hom_inr braid_iso_hom_inl braid_iso_inv_inr braid_iso_inv_inl in
@[no_expose] public noncomputable instance : SymmetricCategory (J ⟶ K) where
  braiding := braid
  braiding_naturality_left := by
    intros
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with simp
  braiding_naturality_right := by
    intros
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with simp
  hexagon_forward := by
    intros
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with
    | inl i =>
      obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
      cases i with
      | inl t => simp
      | inr t => simp
    | inr t => simp
  hexagon_reverse := by
    intros
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with
    | inl i => simp
    | inr i =>
      obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
      cases i with simp
  symmetry := by
    intros
    ext i
    obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
    cases i with simp

@[simp, grind =]
public lemma braiding_iso_hom_inl (x y : J ⟶ K) (t : x.of.apex) :
    (β_ x y).hom.iso.hom.hom (inl _ _ t) = inr _ _ t := (rfl)

@[simp, grind =]
public lemma braiding_iso_hom_inr (x y : J ⟶ K) (t : y.of.apex) :
    (β_ x y).hom.iso.hom.hom (inr _ _ t) = inl _ _ t := (rfl)

@[simp, grind =]
public lemma braiding_iso_inv_inr (x y : J ⟶ K) (t : x.of.apex) :
    (β_ x y).inv.iso.hom.hom (inr _ _ t) = inl _ _ t := (rfl)

@[simp, grind =]
public lemma braiding_iso_inv_inl (x y : J ⟶ K) (t : y.of.apex) :
    (β_ x y).inv.iso.hom.hom (inl _ _ t) = inr _ _ t := (rfl)

end Symmetric

end monoidal

/-- Interpret the constant function ((j : J) ↦ k) as a morphism `J ⟶ K` in the
bursnide category. -/
public noncomputable def const (J : BurnsideFintype.{u}) {K : BurnsideFintype.{u}} (k : K.as.of) :
      J ⟶ K :=
  (Burnside.inl FintypeCat).map (FintypeCat.homMk fun (_ : J.as.of) ↦ k).toLoc

public lemma const_apex (J : BurnsideFintype.{u}) {K : BurnsideFintype.{u}} (k : K.as.of) :
    (const J k).of.apex = J.as.of := (rfl)

/-- The equivalence `(const J k).of.apex ≃ J.as.of`. This needs to be inserted to ease type
checking. -/
public def constApexEquiv (J : BurnsideFintype.{u}) {K : BurnsideFintype.{u}} (k : K.as.of) :
    (const J k).of.apex ≃ J.as.of :=
  .refl _

@[simp]
public lemma const_r_apply (J : BurnsideFintype.{u}) {K : BurnsideFintype.{u}}
    (k : K.as.of) (j : (const J k).of.apex) :
    (const J k).of.r j = k :=
  (rfl)

@[simp]
public lemma const_l_apply (J : BurnsideFintype.{u}) {K : BurnsideFintype.{u}}
    (k : K.as.of) (j : (const J k).of.apex) :
    (const J k).of.l j = (constApexEquiv ..) j :=
  (rfl)

section Additive

variable {J : BurnsideFintype.{u}} (K : BurnsideFintype.{u})

/-! In the following, we show that we can "add" families of spans:
concretely, this means that we exhibit the category `J ⟶ K` as a J-indexed product of the
copies of the category `unit ⟶ K`. The projections functor `J ⟶ K` ⥤ `unit ⟶ K` at the index `j`
for this decomposition takes the fiber of the left morphism at `j`.
In the other direction, a family of spans `J → (unit ⟶ K)` is mapped to a sigma type
that sums all the "fibers".

We then describe the composition of spans through this equivalence. --/

-- TODO make private and only leave the final equivalence as public.

variable {K} in
@[simp]
public lemma iso_inv_hom_id_hom {f g : J ⟶ K} (φ : f ⟶ g) (x : f.of.apex) :
    φ.iso.inv.hom (φ.iso.hom.hom x) = x :=
  congr($(φ.iso.hom_inv_id).hom x)

variable {K} in
@[simp]
public lemma iso_hom_inv_id_hom {f g : J ⟶ K} (φ : f ⟶ g) (x : g.of.apex) :
    φ.iso.hom.hom (φ.iso.inv.hom x) = x :=
  congr($(φ.iso.inv_hom_id).hom x)

open scoped Classical in
/-- Given a span `J ⟶ K`, and `j : J`, this is the span obtained by restricting to the left morphism
to its fiber over `j`. -/
noncomputable def leftFiber (j : J.as.of) (K : BurnsideFintype.{u}) :
    (J ⟶ K) ⥤ (unit ⟶ K) where
  obj f :=
    .mk <|
      { apex := .of <| { x : f.of.apex // f.of.l x = j}
        l := FintypeCat.homMk fun _ ↦ PUnit.unit
        r := FintypeCat.homMk (fun x ↦ f.of.r x.val)
        wl := by tauto
        wr := by tauto }
  map φ :=
    .mk <| Spans.mkIso₂ (FintypeCat.equivEquivIso <|
      { toFun x := ⟨φ.iso.hom.hom x.val, by
          have p := x.property
          have hl := congr($(φ.iso.hom.hom_l) x.val)
          simp only [← p, ← hl, Span.Hom.hom_l]
          rfl ⟩
        invFun x := ⟨φ.iso.inv.hom x.val, by
          have p := x.property
          have hl := congr($(φ.iso.inv.hom_l) x.val)
          simp only [← p, ← hl, Span.Hom.hom_l]
          rfl⟩
        left_inv x := by
          change @Eq (Subtype _) _ _
          ext
          simp
        right_inv x := by
          change @Eq (Subtype _) _ _
          ext
          simp })
      (by ext)
      (by
        ext i
        exact congr($(φ.iso.hom.hom_r) i.val))

variable {K}

/-- An equivalence `((leftFiber j K).obj f).of.apex ≃ { x : f.of.apex // f.of.l x = j}`
to help type checking. -/
noncomputable def leftFiberObjApexEquiv (j : J.as.of) (f : J ⟶ K) :
    ((leftFiber j K).obj f).of.apex ≃ { x : f.of.apex // f.of.l x = j } :=
  .refl _

@[simp]
lemma of_l_leftFiberObjApexEmbedding (j : J.as.of) (f : J ⟶ K)
    (x : ((leftFiber j K).obj f).of.apex) :
    f.of.l ((leftFiberObjApexEquiv j f) x) = j :=
  x.property

@[simp]
lemma leftFiberObj_of_r_apply (j : J.as.of) (f : J ⟶ K)
    (x : ((leftFiber j K).obj f).of.apex) :
    ((leftFiber j K).obj f).of.r x = f.of.r ((leftFiberObjApexEquiv j f) x) :=
  (rfl)

@[simp]
lemma leftFiber_map_iso_hom_hom_val (j : J.as.of) {f g : J ⟶ K} (φ : f ⟶ g)
    (x : ((leftFiber j K).obj f).of.apex) :
    (leftFiberObjApexEquiv ..) (((leftFiber j K).map φ).iso.hom.hom x) =
    φ.iso.hom.hom ((leftFiberObjApexEquiv ..) x) :=
  (rfl)

@[simp]
lemma leftFiber_map_iso_inv_hom_val (j : J.as.of) {f g : J ⟶ K} (φ : f ⟶ g)
    (y : ((leftFiber j K).obj g).of.apex) :
    (leftFiberObjApexEquiv ..) (((leftFiber j K).map φ).iso.inv.hom y) =
    φ.iso.inv.hom ((leftFiberObjApexEquiv ..) y) :=
  (rfl)

variable (J K) in
/-- Sum a `J`-indexed family of spans `unit ⟶ K` to a span `J ⟶ K`. -/
def leftSum : (J.as.of → (unit ⟶ K)) ⥤ (J ⟶ K) where
  obj F :=
    .mk <|
      { apex := .of <| Σ j : J.as.of, (F j).of.apex
        l := FintypeCat.homMk (fun u ↦ u.1)
        r := FintypeCat.homMk (fun u ↦ (F u.fst).of.r u.2)
        wl := by tauto
        wr := by tauto }
  map φ :=
    .mk <| Spans.mkIso₂ (FintypeCat.equivEquivIso <|
      { toFun x := ⟨x.1, (φ x.1).iso.hom.hom x.2⟩
        invFun x := ⟨x.1, (φ x.1).iso.inv.hom x.2⟩
        left_inv x := by
          change @Eq (Sigma _) _ _
          ext
          · rfl
          · simp
        right_inv x := by
          change @Eq (Sigma _) _ _
          ext
          · rfl
          · simp })
      (by
        ext i
        rfl)
      (by
        ext i
        exact congr($((φ i.fst).iso.hom.hom_r) i.snd))

/-- The equivalence that defines leftSum on objects. -/
noncomputable def leftSumObjApexEquiv (F : J.as.of → (unit ⟶ K)) :
    ((leftSum J K).obj F).of.apex ≃ (Σ j : J.as.of, (F j).of.apex) := .refl _

lemma leftSumObj_of_l_apply (F : J.as.of → (unit ⟶ K))
    (x : ((leftSum J K).obj F).of.apex) :
    ((leftSum J K).obj F).of.l x = ((leftSumObjApexEquiv ..) x).fst :=
  rfl

lemma leftSumObj_of_r_apply (F : J.as.of → (unit ⟶ K))
    (x : ((leftSum J K).obj F).of.apex) :
    ((leftSum J K).obj F).of.r x =
    (F ((leftSumObjApexEquiv ..) x).fst).of.r ((leftSumObjApexEquiv ..) x).snd :=
  rfl

@[simp]
lemma leftSum_map_hom_app {F G : J.as.of → (unit ⟶ K)} (φ : F ⟶ G)
    (x : ((leftSum J K).obj F).of.apex) :
    (leftSumObjApexEquiv ..) (((leftSum J K).map φ).iso.hom.hom x) =
    ⟨((leftSumObjApexEquiv ..) x).fst, (φ ((leftSumObjApexEquiv ..) x).fst).iso.hom.hom
      ((leftSumObjApexEquiv ..) x).snd⟩ :=
  (rfl)

@[simp]
lemma leftSum_map_inv_app {F G : J.as.of → (unit ⟶ K)} (φ : F ⟶ G)
    (x : ((leftSum J K).obj G).of.apex) :
    (leftSumObjApexEquiv ..) (((leftSum J K).map φ).iso.inv.hom x) =
    ⟨((leftSumObjApexEquiv ..) x).fst, (φ ((leftSumObjApexEquiv ..) x).fst).iso.inv.hom
      ((leftSumObjApexEquiv ..) x).snd⟩ :=
  (rfl)

variable (J K) in
/-- The equivalence that decomposes a span into a family of spans by taking fibers
of the left map of the original span. -/
public noncomputable def leftSumEquiv : (J ⟶ K) ≌ (J.as.of → (unit ⟶ K)) where
  functor := Functor.pi' (fun x ↦ leftFiber x K)
  inverse := leftSum J K
  unitIso :=
    NatIso.ofComponents (fun F ↦
      Core.isoMk <| Spans.mkIso₂ (FintypeCat.equivEquivIso <|
        (Equiv.sigmaFiberEquiv F.of.l).symm.trans <|
            (Equiv.sigmaCongrRight (fun j ↦ leftFiberObjApexEquiv j F)).symm.trans
            (leftSumObjApexEquiv _).symm))
    (fun {F G} φ ↦ by
      ext (i : F.of.apex)
      apply (leftSumObjApexEquiv ..).injective
      ext
      · exact congr($(φ.iso.hom.hom_l) i)
      · rfl)
  counitIso :=
    NatIso.ofComponents (fun F ↦ Pi.isoMk (fun j ↦
      Core.isoMk <| Spans.mkIso₂ (FintypeCat.equivEquivIso <|
        (leftFiberObjApexEquiv ..).trans <| (Equiv.subtypeEquiv (leftSumObjApexEquiv F)
          (p := fun x ↦ ((J.leftSum K).obj F).of.l x = j) (q := fun x ↦ x.1 = j)
          (h := fun t ↦ by exact Iff.rfl)).trans (Equiv.sigmaSubtype j))
        (by ext)
        (by
          ext i;
          obtain ⟨⟨i, hi⟩, rfl⟩ := (leftFiberObjApexEquiv ..).symm.surjective i
          obtain ⟨⟨i, k⟩, rfl⟩ := (leftSumObjApexEquiv ..).symm.surjective i
          generalize_proofs
          obtain rfl : i = j := by grind
          rfl)))
      (fun {F G} η ↦ by
        ext j k
        dsimp [Functor.pi'] at j k ⊢
        obtain ⟨⟨k, hk⟩, rfl⟩ := (leftFiberObjApexEquiv ..).symm.surjective k
        obtain ⟨⟨j', k⟩, rfl⟩ := (leftSumObjApexEquiv ..).symm.surjective k
        generalize_proofs
        obtain rfl : j' = j := by grind
        rfl)
  functor_unitIso_comp X := by
    ext j k
    dsimp [Functor.pi', Equiv.Perm.sigmaCongrRight] at j k ⊢
    obtain ⟨⟨k, hk⟩, rfl⟩ := (leftFiberObjApexEquiv ..).symm.surjective k
    obtain ⟨⟨j', ⟨k, hk'⟩⟩, rfl⟩ := (Equiv.sigmaFiberEquiv X.of.l).surjective k
    simp only [Equiv.sigmaFiberEquiv_apply] at hk
    obtain rfl : j = j' := by grind
    subst hk
    rfl

public section leftSumEquivAPI

/-- The equivalence that determines the underlying type of
`((leftSumEquiv.functor.obj X) j).of.apex` -/
noncomputable def leftSumEquivFunctorObjEvalOfApexEquiv (X : J ⟶ K) (j : J.as.of) :
    (((leftSumEquiv J K).functor.obj X) j).of.apex ≃ { x : X.of.apex // X.of.l x = j } :=
  .refl _

@[simp, grind =]
lemma leftSumEquiv_functor_obj_eval_r (X : J ⟶ K) (j : J.as.of)
    (x : (((leftSumEquiv J K).functor.obj X) j).of.apex) :
    (((leftSumEquiv J K).functor.obj X) j).of.r x =
    X.of.r ((leftSumEquivFunctorObjEvalOfApexEquiv ..) x) :=
  (rfl)

@[simp, grind =]
lemma of_l_leftSumEquivFunctorObjEvalOfApexEquiv (X : J ⟶ K) (j : J.as.of)
    (x : (((leftSumEquiv J K).functor.obj X) j).of.apex) :
    X.of.l ↑((leftSumEquivFunctorObjEvalOfApexEquiv X j) x) = j :=
  ((leftSumEquivFunctorObjEvalOfApexEquiv X j) x).property

@[simp, grind =]
lemma leftSumEquiv_functor_map_iso_hom_apply {X Y : J ⟶ K}
    (φ : X ⟶ Y) (j : J.as.of) (x : (((leftSumEquiv J K).functor.obj X) j).of.apex) :
    (leftSumEquivFunctorObjEvalOfApexEquiv ..)
      ((((leftSumEquiv J K).functor.map φ) j).iso.hom.hom x) =
    φ.iso.hom.hom ((leftSumEquivFunctorObjEvalOfApexEquiv ..) x) :=
  (rfl)

@[simp, grind =]
lemma leftSumEquiv_functor_map_iso_inv_apply {X Y : J ⟶ K}
    (φ : X ⟶ Y) (j : J.as.of) (y : (((leftSumEquiv J K).functor.obj Y) j).of.apex) :
    (leftSumEquivFunctorObjEvalOfApexEquiv ..)
      ((((leftSumEquiv J K).functor.map φ) j).iso.inv.hom y) =
    φ.iso.inv.hom ((leftSumEquivFunctorObjEvalOfApexEquiv ..) y) :=
  (rfl)

/-- The equivalence that determines the underlying type of
`((leftSumEquiv J K).inverse.obj F).of.apex` -/
noncomputable def leftSumEquivInverseObjOfApexEquiv (F : J.as.of → (unit ⟶ K)) :
    ((leftSumEquiv J K).inverse.obj F).of.apex ≃ (Σ j : J.as.of, (F j).of.apex) :=
  .refl _

@[simp, grind =]
lemma leftSumEquiv_inverse_of_l_apply (F : J.as.of → (unit ⟶ K))
    (x : ((leftSumEquiv J K).inverse.obj F).of.apex) :
    ((leftSumEquiv J K).inverse.obj F).of.l x = ((leftSumEquivInverseObjOfApexEquiv ..) x).fst :=
  (rfl)

@[simp, grind =]
lemma leftSumEquiv_inverse_of_r_apply (F : J.as.of → (unit ⟶ K))
    (x : ((leftSumEquiv J K).inverse.obj F).of.apex) :
    ((leftSumEquiv J K).inverse.obj F).of.r x =
      (F ((leftSumEquivInverseObjOfApexEquiv ..) x).fst).of.r
        ((leftSumEquivInverseObjOfApexEquiv ..) x).snd :=
  (rfl)

lemma leftSumEquiv_unitIso_hom_app_iso_hom_app (X : J ⟶ K) (x : X.of.apex) :
    ((leftSumEquiv J K).unitIso.hom.app X).iso.hom.hom x =
    ((leftSumEquivInverseObjOfApexEquiv .. ).symm
      ⟨X.of.l x, (leftSumEquivFunctorObjEvalOfApexEquiv ..).symm ⟨x, rfl⟩⟩) :=
  (rfl)

/- Lemmas for co/units are not marked simp: it’s better to just know that they are part of an
equivalence, and one should rarely try to poke into its innards. -/

lemma leftSumEquiv_unitIso_hom_app_iso_inv_app (X : J ⟶ K)
      (x : ((J.leftSumEquiv K).inverse.obj ((J.leftSumEquiv K).functor.obj X)).of.apex.carrier) :
    ((leftSumEquiv J K).unitIso.hom.app X).iso.inv.hom x =
    (Equiv.sigmaFiberEquiv X.of.l)
      ⟨((leftSumEquivInverseObjOfApexEquiv ..) x).fst,
        ⟨ ((leftSumEquivFunctorObjEvalOfApexEquiv ..)
            ((leftSumEquivInverseObjOfApexEquiv ..) x).snd).val,
          ((leftSumEquivFunctorObjEvalOfApexEquiv ..)
            ((leftSumEquivInverseObjOfApexEquiv ..) x).snd).property⟩⟩ :=
  (rfl)

lemma leftSumEquiv_unitIso_inv_app_iso_hom_app (X : J ⟶ K)
      (x : ((J.leftSumEquiv K).inverse.obj ((J.leftSumEquiv K).functor.obj X)).of.apex.carrier) :
    ((leftSumEquiv J K).unitIso.inv.app X).iso.hom.hom x =
    (Equiv.sigmaFiberEquiv X.of.l)
      ⟨((leftSumEquivInverseObjOfApexEquiv ..) x).fst,
        ⟨ ((leftSumEquivFunctorObjEvalOfApexEquiv ..)
            ((leftSumEquivInverseObjOfApexEquiv ..) x).snd).val,
          ((leftSumEquivFunctorObjEvalOfApexEquiv ..)
            ((leftSumEquivInverseObjOfApexEquiv ..) x).snd).property⟩⟩ :=
  (rfl)

lemma leftSumEquiv_unitIso_inv_app_iso_inv_app (X : J ⟶ K) (x : X.of.apex) :
    ((leftSumEquiv J K).unitIso.inv.app X).iso.inv.hom x =
    ((leftSumEquivInverseObjOfApexEquiv .. ).symm
      ⟨X.of.l x, (leftSumEquivFunctorObjEvalOfApexEquiv ..).symm ⟨x, rfl⟩⟩) :=
  (rfl)

-- unfortunately, this one needs casts...
lemma leftSumEquiv_counitIso_hom_app_iso_hom_app (F : J.as.of → (unit ⟶ K))
      (j : J.as.of)
      (x : ((J.leftSumEquiv K).functor.obj ((J.leftSumEquiv K).inverse.obj F) j).of.apex.carrier) :
    (((leftSumEquiv J K).counitIso.hom.app F) j).iso.hom.hom x =
    ( letI x' := (leftSumEquivFunctorObjEvalOfApexEquiv ..) x
      letI x'' := (leftSumEquivInverseObjOfApexEquiv ..) x'.val
      x'.property ▸ leftSumEquiv_inverse_of_l_apply F x' ▸ x''.snd) :=
  (rfl)

lemma leftSumEquiv_counitIso_hom_app_iso_inv_app (F : J.as.of → (unit ⟶ K))
      (j : J.as.of)
      (x : (F j).of.apex) :
    (((leftSumEquiv J K).counitIso.hom.app F) j).iso.inv.hom x =
    ((leftSumEquivFunctorObjEvalOfApexEquiv ..).symm
      ⟨(leftSumEquivInverseObjOfApexEquiv ..).symm ⟨j, x⟩,
        by rw [leftSumEquiv_inverse_of_l_apply, Equiv.apply_symm_apply]⟩) :=
  (rfl)

lemma leftSumEquiv_counitIso_inv_app_iso_hom_app (F : J.as.of → (unit ⟶ K))
      (j : J.as.of)
      (x : (F j).of.apex) :
    (((leftSumEquiv J K).counitIso.inv.app F) j).iso.hom.hom x =
    ((leftSumEquivFunctorObjEvalOfApexEquiv ..).symm
      ⟨(leftSumEquivInverseObjOfApexEquiv ..).symm ⟨j, x⟩,
        by rw [leftSumEquiv_inverse_of_l_apply, Equiv.apply_symm_apply]⟩) :=
  (rfl)

lemma leftSumEquiv_counitIso_inv_app_iso_inv_app (F : J.as.of → (unit ⟶ K))
      (j : J.as.of)
      (x : ((J.leftSumEquiv K).functor.obj ((J.leftSumEquiv K).inverse.obj F) j).of.apex.carrier) :
    (((leftSumEquiv J K).counitIso.inv.app F) j).iso.inv.hom x =
    ( letI x' := (leftSumEquivFunctorObjEvalOfApexEquiv ..) x
      letI x'' := (leftSumEquivInverseObjOfApexEquiv ..) x'.val
      x'.property ▸ leftSumEquiv_inverse_of_l_apply F x' ▸ x''.snd) :=
  (rfl)

end leftSumEquivAPI

section leftSumMonoidal

/-! In this section, we construct a symmetric monoidal structure on the equivalence sumEquiv. -/

open MonoidalCategory

-- not inlined for performance reasons.
/-- Auxiliary definition to show that leftSumEquiv.functor is monoidal. -/
noncomputable def leftSumEquiv.μIso (X Y : J ⟶ K) :
    (J.leftSumEquiv K).functor.obj X ⊗ (J.leftSumEquiv K).functor.obj Y ≅
    (J.leftSumEquiv K).functor.obj (X ⊗ Y) :=
  letI e₁ (j : J.as.of) (X Y : J ⟶ K) :
      { x // X.of.l x = j } ⊕ { x // Y.of.l x = j } ≃ { y // (X ⊗ Y).of.l y = j } :=
    (Equiv.sumCongr
      (Equiv.subtypeEquivRight (by simp))
      (Equiv.subtypeEquivRight (by simp))).trans <|
      Equiv.subtypeSum.symm.trans <| Equiv.subtypeEquivOfSubtype (tensorObjApexEquiv _ _).symm
  Pi.isoMk (fun j ↦
    Core.isoMk <| Spans.mkIso₂ (FintypeCat.equivEquivIso <|
      ((tensorObjApexEquiv _ _).trans <|
        Equiv.sumCongr
          (leftSumEquivFunctorObjEvalOfApexEquiv ..)
          (leftSumEquivFunctorObjEvalOfApexEquiv ..) |>.trans <|
        (e₁ j X Y).trans
        (leftSumEquivFunctorObjEvalOfApexEquiv ..).symm))
    (by ext)
    (by
      ext i
      obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
      cases i with rfl))

-- not inlined for performance reasons.
/-- Auxiliary definition to show that leftSumEquiv.functor is monoidal. -/
noncomputable def leftSumEquiv.εIso :
    𝟙_ (J.as.of → (unit ⟶ K)) ≅ (J.leftSumEquiv K).functor.obj (𝟙_ (J ⟶ K)) :=
  Pi.isoMk (fun j ↦
      Core.isoMk <| Spans.mkIso₂ (FintypeCat.equivEquivIso <|
        (({ toFun p := IsEmpty.elim (inferInstanceAs <| IsEmpty <| (𝟙_ (unit ⟶ K)).of.apex) p
            invFun p := IsEmpty.elim inferInstance p
            left_inv p := IsEmpty.elim (inferInstanceAs <| IsEmpty <| (𝟙_ (unit ⟶ K)).of.apex) p
            right_inv p := IsEmpty.elim inferInstance p } : _ ≃ _).trans <|
          (leftSumEquivFunctorObjEvalOfApexEquiv ..).symm))
      (by ext)
      (by
        ext i
        dsimp at i
        exact IsEmpty.elim inferInstance i))

/- Many rfl's in the proof below, but they are actually "good"!
I've observed a considerable speedup (about 10x!) with this proof compared to
the one that would be "principled" (using casts, then relying on the simplifier) -/

@[no_expose]
public noncomputable instance : (leftSumEquiv J K).functor.Monoidal :=
  letI : (leftSumEquiv J K).functor.CoreMonoidal :=
    { εIso := leftSumEquiv.εIso
      μIso X Y := leftSumEquiv.μIso X Y
      μIso_hom_natural_left {X Y} f Z := by
        ext j i
        cases i with rfl
      μIso_hom_natural_right := by
        intros
        ext j i
        cases i with rfl
      associativity X Y Z := by
        ext j i
        obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
        cases i with
        | inl i =>
          cases i with
          | left i => rfl
          | right i => rfl
        | inr i => rfl
      left_unitality X := by
        ext j i
        obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
        cases i with
        | inl i =>
          dsimp at i
          exact IsEmpty.elim inferInstance i
        | inr i => rfl
      right_unitality X := by
        ext j i
        obtain ⟨i, rfl⟩ := (tensorObjApexEquiv _ _).symm.surjective i
        cases i with
        | inl i => rfl
        | inr i =>
          dsimp at i
          exact IsEmpty.elim inferInstance i }
  this.toMonoidal

@[no_expose]
public noncomputable instance leftSumEquivInverseMonoidal : (leftSumEquiv J K).inverse.Monoidal :=
  (leftSumEquiv J K).inverseMonoidal

public section leftSumEquivMonoidalAPI

/- SimpNF complains about the lemmas below because simp unfolds the tensor product in the
monoidal structure on Pi categories.
They seem to be incompatible with Pi.monoidalCategoryStruct_tensorObj. -/

@[grind =]
lemma leftSumEquiv_μ_iso_hom_app_inl (X Y : J ⟶ K) (j : J.as.of)
    (t : ((J.leftSumEquiv K).functor.obj X j).of.apex.carrier) :
    (Functor.LaxMonoidal.μ (leftSumEquiv J K).functor X Y j).iso.hom.hom (inl _ _ t) =
    (leftSumEquivFunctorObjEvalOfApexEquiv ..).symm
      ⟨inl X Y ((leftSumEquivFunctorObjEvalOfApexEquiv ..) t), by simp⟩ :=
  (rfl)

@[grind =]
lemma leftSumEquiv_μ_iso_hom_app_inr (X Y : J ⟶ K) (j : J.as.of)
    (t : ((J.leftSumEquiv K).functor.obj Y j).of.apex.carrier) :
    (Functor.LaxMonoidal.μ (leftSumEquiv J K).functor X Y j).iso.hom.hom (inr _ _ t) =
    (leftSumEquivFunctorObjEvalOfApexEquiv ..).symm
      ⟨inr X Y ((leftSumEquivFunctorObjEvalOfApexEquiv ..) t), by simp⟩ :=
  (rfl)

@[grind =]
lemma leftSumEquiv_μ_iso_inv_app_inl (X Y : J ⟶ K) (j : J.as.of)
    (t : ((J.leftSumEquiv K).functor.obj X j).of.apex.carrier) :
    (Functor.LaxMonoidal.μ (leftSumEquiv J K).functor X Y j).iso.inv.hom
      ((leftSumEquivFunctorObjEvalOfApexEquiv ..).symm
      ⟨inl X Y ((leftSumEquivFunctorObjEvalOfApexEquiv ..) t), by simp⟩) =
    inl _ _ t :=
  (rfl)

@[grind =]
lemma leftSumEquiv_μ_iso_inv_app_inr (X Y : J ⟶ K) (j : J.as.of)
    (t : ((J.leftSumEquiv K).functor.obj Y j).of.apex.carrier) :
    (Functor.LaxMonoidal.μ (leftSumEquiv J K).functor X Y j).iso.inv.hom
      ((leftSumEquivFunctorObjEvalOfApexEquiv ..).symm
        ⟨inr X Y ((leftSumEquivFunctorObjEvalOfApexEquiv ..) t), by simp⟩) =
    inr _ _ t :=
  (rfl)

@[grind =]
lemma leftSumEquiv_δ_iso_hom_app_inl (X Y : J ⟶ K) (j : J.as.of)
    (t : ((J.leftSumEquiv K).functor.obj X j).of.apex.carrier) :
    (Functor.OplaxMonoidal.δ (leftSumEquiv J K).functor X Y j).iso.hom.hom
      ((leftSumEquivFunctorObjEvalOfApexEquiv ..).symm
      ⟨inl X Y ((leftSumEquivFunctorObjEvalOfApexEquiv ..) t), by simp⟩) =
    inl _ _ t :=
  (rfl)

@[grind =]
lemma leftSumEquiv_δ_iso_hom_app_inr (X Y : J ⟶ K) (j : J.as.of)
    (t : ((J.leftSumEquiv K).functor.obj Y j).of.apex.carrier) :
    (Functor.OplaxMonoidal.δ (leftSumEquiv J K).functor X Y j).iso.hom.hom
      ((leftSumEquivFunctorObjEvalOfApexEquiv ..).symm
        ⟨inr X Y ((leftSumEquivFunctorObjEvalOfApexEquiv ..) t), by simp⟩) =
    inr _ _ t :=
  (rfl)

@[grind =]
lemma leftSumEquiv_δ_iso_inv_app_inl (X Y : J ⟶ K) (j : J.as.of)
    (t : ((J.leftSumEquiv K).functor.obj X j).of.apex.carrier) :
    (Functor.OplaxMonoidal.δ (leftSumEquiv J K).functor X Y j).iso.inv.hom (inl _ _ t) =
    (leftSumEquivFunctorObjEvalOfApexEquiv ..).symm
      ⟨inl X Y ((leftSumEquivFunctorObjEvalOfApexEquiv ..) t), by simp⟩ :=
  (rfl)

@[grind =]
lemma leftSumEquiv_δ_iso_inv_app_inr (X Y : J ⟶ K) (j : J.as.of)
    (t : ((J.leftSumEquiv K).functor.obj Y j).of.apex.carrier) :
    (Functor.OplaxMonoidal.δ (leftSumEquiv J K).functor X Y j).iso.inv.hom (inr _ _ t) =
    (leftSumEquivFunctorObjEvalOfApexEquiv ..).symm
      ⟨inr X Y ((leftSumEquivFunctorObjEvalOfApexEquiv ..) t), by simp⟩ :=
  (rfl)

noncomputable instance : (leftSumEquiv J K).functor.Braided where
  braided X Y := by
    ext j i
    cases i with rfl

noncomputable instance : (leftSumEquiv J K).IsMonoidal := inferInstance

noncomputable instance : (leftSumEquiv J K).inverse.Braided := inferInstance

end leftSumEquivMonoidalAPI

end leftSumMonoidal

public section Duality

variable {J K : BurnsideFintype.{u}}

open Bicategory Opposite
/-- The global "sefl-duality" of the burnside (2,1)-category of spans
of finite types. -/
@[expose] noncomputable abbrev duality : BurnsideFintype ⥤ᵖ BurnsideFintypeᵒᵖ :=
  Burnside.duality _

variable (J K) in
@[simps!, expose]
noncomputable def dualityFunctor : (J ⟶ K) ⥤ (K ⟶ J) :=
  PrelaxFunctor.mapFunctor duality.toPrelaxFunctor J K ⋙
    (Bicategory.Opposite.homCategoryEquivalence _ _).functor

@[no_expose]
noncomputable instance : (dualityFunctor J K).Monoidal :=
  letI : (dualityFunctor J K).CoreMonoidal :=
    { εIso := .refl _
      μIso X Y := Core.isoMk <| Spans.mkIso₂ (.refl _)
      associativity X Y Z := by
        ext i
        cases i with
        | left t => cases t with
          | left t => rfl
          | right t => rfl
        | right t => rfl }
  this.toMonoidal

@[no_expose]
noncomputable instance : (dualityFunctor J K).Braided where
  braided X Y := by
    ext i
    cases i with rfl

end Duality

end Additive

end BurnsideFintype

end CategoryTheory
