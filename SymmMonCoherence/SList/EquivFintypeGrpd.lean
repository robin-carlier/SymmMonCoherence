/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.FintypeGrpd
public import SymmMonCoherence.SList.Equivalence
public import Mathlib.CategoryTheory.Elementwise

/-! # Symmetric lists and FintypeGrpd

Symetric lists on the unit type are equivalent to the groupoid of finite types and bijections,
and the equivalence is symmetric monoidal. -/

@[expose] public section

universe v u

namespace CategoryTheory.SList

-- TODO Generalize from Unit to PUnit

/-- The functor from symmetric lists on a unit type to the groupoid
of finite types and bijections. The API for this definition is minimal,
please prefer its equivalence version below (unitEquivalence). -/
@[pp_with_univ]
def toFintypeGrpdFunctor : SList PUnit.{v + 1} ⥤ FintypeGrpd.{u} where
  obj x := .mk <| .of <| ULift <| Fin x.length
  map f := FintypeGrpd.mkHom <| Equiv.symm <|
    Equiv.ulift.trans <| (toEquiv f).trans <| Equiv.ulift.symm

/-- An equivalence `toFintypeGrpdFunctor.obj x ≃ Fin x.length`. Under the hood,
this is an identity, but it is important to insert it in order to help automation. -/
@[pp_with_univ]
irreducible_def toFintypeGrpdFunctor.ι (x : SList PUnit.{v + 1}) :
    Fin x.length ≃ toFintypeGrpdFunctor.{v, u}.obj x :=
  Equiv.ulift.symm

@[simp]
lemma toFintypeGrpdFunctor_card (x : SList PUnit.{v + 1}) :
    Fintype.card (toFintypeGrpdFunctor.{v, u}.obj x) = x.length := by
  simp [← Fintype.card_eq.mpr ⟨toFintypeGrpdFunctor.ι.{v, u} _⟩]

open toFintypeGrpdFunctor

@[simp]
lemma toFintypeGrpdFunctor_map_ι_symm {x y : SList PUnit.{v + 1}} (f : x ⟶ y) (i : Fin y.length) :
    (toFintypeGrpdFunctor.{v, u}.map f).iso.inv (ι.{v, u} y i) = (ι.{v, u} x) (toEquiv f i) := by
  simp_rw [toFintypeGrpdFunctor.ι_def]
  rfl

@[simp]
lemma toFintypeGrpdFunctor_map_ι {x y : SList PUnit.{v + 1}} (f : x ⟶ y) (i : Fin x.length) :
    (toFintypeGrpdFunctor.{v, u}.map f).iso.hom (ι.{v, u} x i) =
      (ι.{v, u} y) ((toEquiv f).symm i) := by
  simp_rw [toFintypeGrpdFunctor.ι_def]
  rfl

-- instance : toFintypeGrpdFunctor.EssSurj where
--   mem_essImage x :=
--     letI u := listEquiv.symm <| List.replicate (Fintype.card x) ()
--     haveI : u.length = (Fintype.card x) := by
--       simp [u, length]
--     ⟨u, Nonempty.intro <| Groupoid.isoEquivHom _ _ |>.symm <|
--       FintypeGrpd.mkHom <| Equiv.symm <| Fintype.equivFinOfCardEq this.symm⟩
--
-- instance : toFintypeGrpdFunctor.Full where
--   map_surjective f := by
--     use SList.liftEquiv (FintypeCat.equivEquivIso.symm f.iso).symm fun _ ↦ rfl
--     ext i
--     simp only [toFintypeGrpdFunctor, toEquiv_liftEquiv, Equiv.symm_symm]
--     rfl
--
-- instance : toFintypeGrpdFunctor.Faithful where
--   map_injective {x y} f g hfg := by
--     rw [SList.hom_eq_iff_toEquiv_eq]
--     ext i : 1
--     have := congr(ι x <| (($hfg).iso.inv ((ι _) i)))
--     simpa using this
--
-- public instance : toFintypeGrpdFunctor.IsEquivalence where
--
-- public noncomputable def unitEquivalence : SList PUnit.{v + 1} ≌ FintypeGrpd :=
--   Functor.asEquivalence toFintypeGrpdFunctor
--
-- @[simps!]
-- noncomputable def unitEquivalenceFunctorIso : unitEquivalence.functor ≅ toFintypeGrpdFunctor :=
--   .refl _

section
open MonoidalCategory

public instance : IsEmpty (toFintypeGrpdFunctor.{v, u}.obj (𝟙_ (SList PUnit.{v + 1}))) := by
  simp only [toFintypeGrpdFunctor, tensorUnit_length]
  infer_instance

public instance : toFintypeGrpdFunctor.{v, u}.Monoidal :=
  letI : toFintypeGrpdFunctor.{v, u}.CoreMonoidal :=
    { εIso := FintypeGrpd.mkIso
        (⟨fun i ↦ IsEmpty.elim inferInstance i,
          fun i ↦ IsEmpty.elim inferInstance i,
          fun i ↦ IsEmpty.elim inferInstance i,
          fun i ↦ IsEmpty.elim inferInstance i⟩)
      μIso X Y := FintypeGrpd.mkIso <|
        FintypeGrpd.tensorObjEquiv _ _ |>.symm.trans <|
          Equiv.sumCongr (ι.{v, u} X).symm (ι.{v, u} Y).symm |>.trans <|
            finSumTensEquiv .. |>.trans <|
              ι.{v, u} (X ⊗ Y)
      μIso_hom_natural_left {X Y} f Z := by
        ext i
        cases i using FintypeGrpd.tensorObjCases with
          obtain ⟨t, rfl⟩ := (ι.{v, u} _).surjective t
        | left t => simp [toEquiv_symm]
        | right t => simp [toEquiv_symm]
      μIso_hom_natural_right X {Y Z} f := by
        ext i
        cases i using FintypeGrpd.tensorObjCases with
          obtain ⟨t, rfl⟩ := (ι.{v, u} _).surjective t
        | left t => simp [toEquiv_symm]
        | right t => simp [toEquiv_symm]
      associativity X Y Z := by
        ext i
        cases i using FintypeGrpd.tensorObjCases with
        | left i =>
          cases i using FintypeGrpd.tensorObjCases with
            obtain ⟨t, rfl⟩ := (ι.{v, u} _).surjective t
          | left t => simp [toEquiv_symm]
          | right t => simp [toEquiv_symm]
        | right i =>
          obtain ⟨i, rfl⟩ := (ι.{v, u} _).surjective i
          simp [toEquiv_symm]
      left_unitality X := by
        ext i
        cases i using FintypeGrpd.tensorObjCases with
        | left t => exact IsEmpty.elim inferInstance t
        | right t =>
          obtain ⟨i, rfl⟩ := (ι.{v, u} _).surjective t
          simp [toEquiv_symm]
      right_unitality X := by
        ext i
        cases i using FintypeGrpd.tensorObjCases with
        | left t =>
          obtain ⟨i, rfl⟩ := (ι.{v, u} _).surjective t
          simp [toEquiv_symm]
        | right t => exact IsEmpty.elim inferInstance t }
  this.toMonoidal

lemma toFintypeGrpdFunctor_μIso_def (X Y : SList PUnit.{v + 1}) :
    Functor.Monoidal.μIso toFintypeGrpdFunctor.{v, u} X Y =
    (FintypeGrpd.mkIso <|
      FintypeGrpd.tensorObjEquiv _ _ |>.symm.trans <|
        Equiv.sumCongr (ι.{v, u} X).symm (ι.{v, u} Y).symm |>.trans <|
          finSumTensEquiv .. |>.trans <|
            ι.{v, u} (X ⊗ Y)) := rfl

-- instance : unitEquivalence.functor.Monoidal := inferInstanceAs toFintypeGrpdFunctor.Monoidal

section
variable {X Y : SList PUnit.{v + 1}}
    (l : (toFintypeGrpdFunctor.{v, u}.obj X))
    (r : (toFintypeGrpdFunctor.{v, u}.obj Y))

@[simp]
lemma toFintypeGrpdFunctor_μ_iso_hom_left :
    (Functor.LaxMonoidal.μ toFintypeGrpdFunctor.{v, u} X Y).iso.hom (FintypeGrpd.inl _ _ l) =
    (ι.{v, u} _) (Ψ _ _ ((ι.{v, u} _ |>.symm l).castAdd _)) :=
  rfl

@[simp]
lemma toFintypeGrpdFunctor_μ_iso_hom_right :
    (Functor.LaxMonoidal.μ toFintypeGrpdFunctor.{v, u} X Y).iso.hom (FintypeGrpd.inr _ _ r) =
    (ι.{v, u} _) (Ψ _ _ ((ι.{v, u} _ |>.symm r).natAdd _)) :=
  rfl

@[simp]
lemma toFintypeGrpdFunctor_μ_iso_inv_left :
    (Functor.LaxMonoidal.μ toFintypeGrpdFunctor.{v, u} X Y).iso.inv
      (ι _ (Ψ _ _ ((ι _ |>.symm l).castAdd _))) =
    (FintypeGrpd.inl _ _ l) := by
  rw [← Functor.Monoidal.μIso_hom, toFintypeGrpdFunctor_μIso_def]
  simp

@[simp]
lemma toFintypeGrpdFunctor_μ_iso_inv_right :
    (Functor.LaxMonoidal.μ toFintypeGrpdFunctor.{v, u} X Y).iso.inv
      (ι _ (Ψ _ _ ((ι _ |>.symm r).natAdd _))) =
    (FintypeGrpd.inr _ _ r) := by
  rw [← Functor.Monoidal.μIso_hom, toFintypeGrpdFunctor_μIso_def]
  simp

@[simp]
lemma toFintypeGrpdFunctor_δ_iso_hom_left :
    (Functor.OplaxMonoidal.δ toFintypeGrpdFunctor.{v, u} X Y).iso.hom
      (ι _ (Ψ _ _ ((ι _ |>.symm l).castAdd _))) =
    (FintypeGrpd.inl _ _ l) := by
  rw [← Functor.Monoidal.μIso_inv, toFintypeGrpdFunctor_μIso_def]
  simp

@[simp]
lemma toFintypeGrpdFunctor_δ_iso_hom_right :
    (Functor.OplaxMonoidal.δ toFintypeGrpdFunctor.{v, u} X Y).iso.hom
      (ι _ (Ψ _ _ ((ι _ |>.symm r).natAdd _))) =
    (FintypeGrpd.inr _ _ r) := by
  rw [← Functor.Monoidal.μIso_inv, toFintypeGrpdFunctor_μIso_def]
  simp

@[simp]
lemma toFintypeGrpdFunctor_δ_iso_inv_left :
    (Functor.OplaxMonoidal.δ toFintypeGrpdFunctor.{v, u} X Y).iso.inv (FintypeGrpd.inl _ _ l) =
    (ι _ (Ψ _ _ ((ι _ |>.symm l).castAdd _))) :=
  rfl

@[simp]
lemma toFintypeGrpdFunctor_δ_iso_inv_right :
    (Functor.OplaxMonoidal.δ toFintypeGrpdFunctor.{v, u} X Y).iso.inv (FintypeGrpd.inr _ _ r) =
    (ι _ (Ψ _ _ ((ι _ |>.symm r).natAdd _))) :=
  rfl

end

-- noncomputable instance : unitEquivalence.inverse.Monoidal := unitEquivalence.inverseMonoidal

instance : toFintypeGrpdFunctor.{v, u}.Braided where
  braided X Y := by
    ext i
    cases i using FintypeGrpd.tensorObjCases with
    | left t =>
      obtain ⟨t, rfl⟩ := (ι _).surjective t
      simp only [Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, coreCategory_comp_iso,
        Iso.trans_hom, ConcreteCategory.comp_apply, toFintypeGrpdFunctor_μ_iso_hom_left,
        Equiv.symm_apply_apply, FintypeGrpd.braiding_iso_hom_inl,
        toFintypeGrpdFunctor_μ_iso_hom_right]
      simp [toEquiv_symm, ← SymmetricCategory.braiding_swap_eq_inv_braiding]
    | right t =>
      obtain ⟨i, rfl⟩ := (ι _).surjective t
      simp only [Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, coreCategory_comp_iso,
        Iso.trans_hom, ConcreteCategory.comp_apply, toFintypeGrpdFunctor_μ_iso_hom_right,
        Equiv.symm_apply_apply, FintypeGrpd.braiding_iso_hom_inr,
        toFintypeGrpdFunctor_μ_iso_hom_left]
      simp [toEquiv_symm, ← SymmetricCategory.braiding_swap_eq_inv_braiding]

-- instance : toFintypeGrpdFunctor.Braided := inferInstanceAs <| unitEquivalence.functor.Braided

section

-- TODO: move this somewhere better
instance
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D]
    (e : C ≌ D) [e.functor.Braided] [e.inverse.Monoidal] [e.IsMonoidal] : e.inverse.Braided where
  braided X Y := by
    apply e.functor.map_injective
    simp only [Functor.map_comp, Equivalence.fun_inv_map, Functor.comp_obj, Functor.id_obj,
      Equivalence.functor_map_μ_inverse_comp_counitIso_hom_app_tensor_assoc,
      BraidedCategory.braiding_naturality_assoc, Functor.map_braiding, Category.assoc, cancel_epi]
    rw [← IsIso.inv_eq_inv]
    simp [Equivalence.functor_map_μ_inverse_comp_counitIso_hom_app_tensor_assoc]

end

section ofFintypeGrpd

@[pp_with_univ]
def ofFintype (X : Type u) [Fintype X] : SList PUnit.{v + 1} :=
  listEquiv.symm <| List.replicate (Fintype.card X) .unit

lemma ofFintype_length (X : Type*) [Fintype X] :
  (ofFintype X).length = Fintype.card X := by simp [ofFintype]

/- The equivalence between Fin (ofFintype X).length X induced by the
equality of their cardinal. -/
@[pp_with_univ]
noncomputable irreducible_def ofFintype.ι.{s, t} (X : Type t) [Fintype X] :
    X ≃ Fin (ofFintype.{s, t} X).length :=
  Fintype.equivFinOfCardEq (ofFintype_length _).symm

noncomputable def ofFintypeHomOfEquiv {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) :
    ofFintype X ⟶ ofFintype Y :=
  liftEquiv
    ((ofFintype.ι _).symm.trans e.symm |>.trans (ofFintype.ι _))
    (fun _ ↦ rfl)

section
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

@[simp, grind =]
lemma toEquiv_ofFintypeHomOfEquiv_ι (e : X ≃ Y) (y : Y) :
    toEquiv (ofFintypeHomOfEquiv e) (ofFintype.ι _ y) = ofFintype.ι _ (e.symm y) := by
  simp [ofFintypeHomOfEquiv]

@[simp, grind =]
lemma toEquiv_ofFintypeHomOfEquiv_symm_ι (e : X ≃ Y) (x : X) :
    (toEquiv (ofFintypeHomOfEquiv e)).symm (ofFintype.ι _ x) = ofFintype.ι _ (e x) := by
  simp [ofFintypeHomOfEquiv]

variable (X) in
@[simp, grind =]
lemma ofFintypeHomOfEquiv_refl : ofFintypeHomOfEquiv (.refl X) = 𝟙 _ := by
  rw [hom_eq_iff_toEquiv_eq]
  ext i
  obtain ⟨i, rfl⟩ := (ofFintype.ι X).surjective i
  simp

@[simp, grind =]
lemma ofFintypeHomOfEquiv_trans (e₁ : X ≃ Y) (e₂ : Y ≃ Z) :
    ofFintypeHomOfEquiv (e₁.trans e₂) = ofFintypeHomOfEquiv e₁ ≫ ofFintypeHomOfEquiv e₂ := by
  rw [hom_eq_iff_toEquiv_eq]
  ext i
  obtain ⟨i, rfl⟩ := (ofFintype.ι Z).surjective i
  simp

@[simp, push]
lemma ofFintypeHomOfEquiv_symm (e : X ≃ Y) :
    inv (ofFintypeHomOfEquiv e) = ofFintypeHomOfEquiv e.symm := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  rw [hom_eq_iff_toEquiv_eq]
  ext i : 1
  obtain ⟨i, rfl⟩ := (ofFintype.ι Y).surjective i
  simp

end

section

@[simp]
lemma _root_.CategoryTheory.Core.id_iso {C : Type*} [Category* C] (X : Core C) :
    (𝟙 X:).iso = .refl X.of := rfl

@[simp]
lemma _root_.CategoryTheory.Core.comp_iso {C : Type*} [Category* C] {X Y Z : Core C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).iso = f.iso.trans g.iso := rfl

@[simp, grind =]
lemma _root_.FintypeCat.equivEquivIso_refl (X : FintypeCat) :
    FintypeCat.equivEquivIso (Equiv.refl X) = .refl X := rfl

@[simp, grind =]
lemma _root_.FintypeCat.equivEquivIso_trans {X Y Z : FintypeCat} (e : X ≃ Y) (e' : Y ≃ Z) :
    FintypeCat.equivEquivIso (e.trans e') =
    (FintypeCat.equivEquivIso e).trans (FintypeCat.equivEquivIso e') := rfl

@[simp, grind =]
lemma _root_.FintypeCat.equivEquivIso_apply_symm {X Y : FintypeCat} (e : X ≃ Y) :
    FintypeCat.equivEquivIso (e.symm) =
    (FintypeCat.equivEquivIso e).symm := rfl

@[simp, grind =]
lemma _root_.FintypeCat.equivEquivIso_symm_refl (X : FintypeCat) :
    (FintypeCat.equivEquivIso.symm (Iso.refl X)) =
    Equiv.refl _ := rfl

@[simp, grind =]
lemma _root_.FintypeCat.equivEquivIso_symm_trans {X Y Z : FintypeCat} (e : X ≅ Y) (e' : Y ≅ Z) :
    FintypeCat.equivEquivIso.symm (e.trans e') =
    (FintypeCat.equivEquivIso.symm e).trans (FintypeCat.equivEquivIso.symm e') := rfl

@[simp, grind =]
lemma _root_.FintypeCat.equivEquivIso_symm_apply_symm {X Y : FintypeCat} (e : X ≅ Y) :
    FintypeCat.equivEquivIso.symm e.symm =
    (FintypeCat.equivEquivIso.symm e).symm := rfl

end

-- This is an abbrev so that things check out at reducible transparency.
@[pp_with_univ, simps]
noncomputable abbrev ofFintypeGrpdFunctor : FintypeGrpd.{u} ⥤ SList PUnit.{v + 1} where
  obj X := ofFintype X
  map f := ofFintypeHomOfEquiv (FintypeCat.equivEquivIso.symm f.iso)

instance (X : FintypeGrpd) [IsEmpty X] : IsEmpty (Fin (ofFintypeGrpdFunctor.{u}.obj X).length) := by
  rw [← Equiv.isEmpty_congr (ofFintype.ι _)]
  infer_instance

public noncomputable instance : ofFintypeGrpdFunctor.{v, u}.Monoidal :=
  letI : ofFintypeGrpdFunctor.{v, u}.CoreMonoidal :=
    { εIso :=
        SList.liftEquivIso ((Equiv.equivEmpty _).trans (Equiv.equivEmpty _).symm)
          (fun _ ↦ rfl)
      μIso X Y :=
        SList.liftEquivIso
          (ofFintype.ι _ |>.symm.trans <|
            (FintypeGrpd.tensorObjEquiv X Y).symm.trans <|
            (Equiv.sumCongr (ofFintype.ι _) (ofFintype.ι _)).trans <|
            (finSumTensEquiv (ofFintype X) (ofFintype Y)))
          (fun _ ↦ rfl)
      μIso_hom_natural_left {X Y} f Z := by
        rw [hom_eq_iff_toEquiv_eq]
        ext i : 1
        obtain ⟨i, rfl⟩ := (ofFintype.ι _).surjective i
        obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
        cases i with simp
      μIso_hom_natural_right X {Y Z} f := by
        rw [hom_eq_iff_toEquiv_eq]
        ext i : 1
        obtain ⟨i, rfl⟩ := (ofFintype.ι _).surjective i
        obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
        cases i with simp
      associativity X Y Z := by
        rw [hom_eq_iff_toEquiv_eq]
        ext i : 1
        obtain ⟨i, rfl⟩ := (ofFintype.ι _).surjective i
        obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
        cases i with
        | inl i => simp
        | inr i =>
          obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
          cases i with simp
      left_unitality X := by
        rw [hom_eq_iff_toEquiv_eq]
        ext i : 1
        obtain ⟨i, rfl⟩ := (ofFintype.ι _).surjective i
        simp
      right_unitality X := by
        rw [hom_eq_iff_toEquiv_eq]
        ext i : 1
        obtain ⟨i, rfl⟩ := (ofFintype.ι _).surjective i
        simp }
  this.toMonoidal

lemma ofFintypeGrpdFunctor_μIso_hom_def (X Y : FintypeGrpd.{u}) :
    (Functor.Monoidal.μIso ofFintypeGrpdFunctor X Y).hom =
    SList.liftEquiv
      (ofFintype.ι _ |>.symm.trans <|
        (FintypeGrpd.tensorObjEquiv X Y).symm.trans <|
        (Equiv.sumCongr (ofFintype.ι _) (ofFintype.ι _)).trans <|
        (finSumTensEquiv (ofFintype X) (ofFintype Y)))
      (fun _ ↦ rfl) := rfl

lemma ofFintypeGrpdFunctor_μIso_inv_def (X Y : FintypeGrpd.{u}) :
    (Functor.Monoidal.μIso ofFintypeGrpdFunctor X Y).inv =
    SList.liftEquiv
      (finSumTensEquiv (ofFintype X) (ofFintype Y)|>.symm.trans <|
        (Equiv.sumCongr (ofFintype.ι _).symm (ofFintype.ι _).symm).trans <|
        (FintypeGrpd.tensorObjEquiv X Y).trans <| ofFintype.ι _ )
      (fun _ ↦ rfl) := rfl

section

@[simp, grind =]
lemma toEquiv_ofFintypeGrpdFunctor_μ_left (X Y : FintypeGrpd.{u}) (x : X) :
    toEquiv (Functor.LaxMonoidal.μ ofFintypeGrpdFunctor.{v, u} X Y)
      (ofFintype.ι _ (FintypeGrpd.inl _ _ x)) =
    Ψ _ _ ((ofFintype.ι _ x).castAdd _) := by
  simp [← Functor.Monoidal.μIso_hom, ofFintypeGrpdFunctor_μIso_hom_def]

@[simp, grind =]
lemma toEquiv_ofFintypeGrpdFunctor_μ_right (X Y : FintypeGrpd.{u}) (y : Y) :
    toEquiv (Functor.LaxMonoidal.μ ofFintypeGrpdFunctor.{v, u} X Y)
      (ofFintype.ι _ (FintypeGrpd.inr _ _ y)) =
    Ψ _ _ ((ofFintype.ι _ y).natAdd _) := by
  simp [← Functor.Monoidal.μIso_hom, ofFintypeGrpdFunctor_μIso_hom_def]

@[simp, grind =]
lemma toEquiv_ofFintypeGrpdFunctor_δ_left (X Y : FintypeGrpd.{u}) (x : X) :
    toEquiv (Functor.OplaxMonoidal.δ ofFintypeGrpdFunctor.{v, u} X Y)
      (Ψ _ _ ((ofFintype.ι _ x).castAdd _)) = ofFintype.ι _ (FintypeGrpd.inl _ _ x) := by
  simp [← Functor.Monoidal.μIso_inv, ofFintypeGrpdFunctor_μIso_inv_def]

@[simp, grind =]
lemma toEquiv_ofFintypeGrpdFunctor_δ_right (X Y : FintypeGrpd.{u}) (y : Y) :
    toEquiv (Functor.OplaxMonoidal.δ ofFintypeGrpdFunctor.{v, u} X Y)
      (Ψ _ _ ((ofFintype.ι _ y).natAdd _)) = ofFintype.ι _ (FintypeGrpd.inr _ _ y) := by
  simp [← Functor.Monoidal.μIso_inv, ofFintypeGrpdFunctor_μIso_inv_def]

end

noncomputable instance : ofFintypeGrpdFunctor.{v, u}.Braided where
  braided X Y := by
    rw [hom_eq_iff_toEquiv_eq]
    ext i : 1
    obtain ⟨i, rfl⟩ := (ofFintype.ι _).surjective i
    obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
    cases i with
    | inl i =>
      simp [← Functor.Monoidal.μIso_hom, ofFintypeGrpdFunctor_μIso_hom_def]
    | inr i =>
      simp [← Functor.Monoidal.μIso_hom, ofFintypeGrpdFunctor_μIso_hom_def]

noncomputable def unitEquivalence.counitIso :
    ofFintypeGrpdFunctor.{v, u} ⋙ toFintypeGrpdFunctor.{v, u} ≅ 𝟭 FintypeGrpd.{u} :=
  NatIso.ofComponents
    (fun _ ↦ FintypeGrpd.mkIso <| (toFintypeGrpdFunctor.ι.{v, u} _).symm.trans
      (ofFintype.ι.{v, u} _).symm)
    (fun {x y} f ↦ by
      ext i
      dsimp at i ⊢
      obtain ⟨i, rfl⟩ := (toFintypeGrpdFunctor.ι _).surjective i
      obtain ⟨i, rfl⟩ := (ofFintype.ι _).surjective i
      simp)

attribute [-simp] Adjunction.rightAdjointLaxMonoidal_μ in -- this declaration causes timeouts here
instance : unitEquivalence.counitIso.{v, u}.hom.IsMonoidal where
  tensor X Y := by
    ext i
    dsimp at i ⊢
    obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
    cases i with
    | inl i =>
      obtain ⟨i, rfl⟩ := (toFintypeGrpdFunctor.ι _).surjective i
      obtain ⟨i, rfl⟩ := (ofFintype.ι _).surjective i
      simp [← Functor.Monoidal.μIso_hom, ofFintypeGrpdFunctor_μIso_hom_def,
        toFintypeGrpdFunctor_μIso_def, unitEquivalence.counitIso]
    | inr i =>
      obtain ⟨i, rfl⟩ := (toFintypeGrpdFunctor.ι _).surjective i
      obtain ⟨i, rfl⟩ := (ofFintype.ι _).surjective i
      simp [← Functor.Monoidal.μIso_hom, ofFintypeGrpdFunctor_μIso_hom_def,
        toFintypeGrpdFunctor_μIso_def, unitEquivalence.counitIso]
  unit := by -- cat_disch works but is a bit slow
    ext i
    grind [IsEmpty.false i]

/- The composition `toFintypeGrpdFunctor ⋙ ofFintypeGrpdFunctor`  is naturally
isomorphic to the identity since both functors are symmetric monoidal.
Note that such an isomorphism, if it exists, must be unique. -/
noncomputable def unitEquivalence.unitIso :
      𝟭 (SList PUnit.{v + 1}) ≅ toFintypeGrpdFunctor.{v, u} ⋙ ofFintypeGrpdFunctor.{v, u} :=
  monoidalLiftNatIso <| fun x ↦
    SList.liftEquivIso
      (Fintype.equivOfCardEq (by simp [ofFintype_length]))
      (fun _ ↦ rfl)

instance : NatTrans.IsMonoidal unitEquivalence.unitIso.hom := by
  dsimp [unitEquivalence.unitIso]
  infer_instance

noncomputable abbrev unitEquivalence :  SList PUnit.{v + 1} ≌ FintypeGrpd.{u} where
  functor := toFintypeGrpdFunctor.{v, u}
  inverse := ofFintypeGrpdFunctor.{v, u}
  counitIso := unitEquivalence.counitIso.{v, u}
  unitIso := unitEquivalence.unitIso.{v, u}
  functor_unitIso_comp X := by
    /- We restate it as an equality of natural transormations, so that
    we can use the universal property -/
    suffices H : (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (unitEquivalence.unitIso.hom) toFintypeGrpdFunctor ≫
        (Functor.associator ..).hom ≫
        Functor.whiskerLeft toFintypeGrpdFunctor (unitEquivalence.counitIso.hom) ≫
        (Functor.rightUnitor _).hom = 𝟙 _ by
      simpa using congr($(H).app X)
    apply monoidalNatTrans_ext_app_singleton
    intro c
    simp only [NatTrans.comp_app, Functor.comp_obj, Functor.id_obj, Functor.leftUnitor_inv_app,
      ofFintypeGrpdFunctor_obj, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.comp_id, Category.id_comp,
      NatTrans.id_app]
    ext i
    haveI : Subsingleton <| toFintypeGrpdFunctor.{v, u}.obj [c]~ := by
      simp [← Fintype.card_le_one_iff_subsingleton]
    subsingleton

instance : toFintypeGrpdFunctor.{v,u}.IsEquivalence :=
  unitEquivalence.isEquivalence_functor

instance : ofFintypeGrpdFunctor.{v,u}.IsEquivalence :=
  unitEquivalence.isEquivalence_inverse

end ofFintypeGrpd

end

end CategoryTheory.SList
