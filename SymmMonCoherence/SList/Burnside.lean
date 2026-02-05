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

end BurnsideFintype

end CategoryTheory
