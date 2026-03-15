/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.FreeSMC
public import SymmMonCoherence.SList.Linear
public import Mathlib.Tactic.CategoryTheory.Coherence
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Equivalence between `SList C` and `FreeSymmetricMonoidalCategory C`

This file constructs the equivalence of symmetric monoidal categories between the category of
symmetric lists `SList C` and the free symmetric monoidal category
`FreeSymmetricMonoidalCategory C`. The idea of encoding part of the coherence
theorem in this way is due to Stefano Piceghello, and we mostly follow his
work here.

## Main definitions

* `normalization`: The monoidal functor `FreeSMC C ⥤ SList C` that flattens a tree into a list.
* `inclusion`: The monoidal functor `SList C ⥤ FreeSMC C`
  that maps a list to a right-associated tree.
* `equivalence`: The equivalence of categories `SList C ≌ FreeSMC C`.

-/


open CategoryTheory MonoidalCategory FreeSymmetricMonoidalCategory

namespace CategoryTheory.SList

variable (C : Type*)

noncomputable section Normalization

/-- The normalization functor maps an object in `FreeSMC C` (a "tree") to its underlying (symmetric)
list of "leaves" in `SList C`.
It is defined using the universal property of the free symmetric monoidal category. -/
@[expose] public def normalization : FreeSymmetricMonoidalCategory C ⥤ SList C :=
  FreeSymmetricMonoidalCategory.project (fun c => [c]~)

public lemma normalization_of (c : C) : (normalization C).obj (of c) = [c]~ := rfl

@[no_expose] public def normalizationOfIso (c : C) : (normalization C).obj (of c) ≅ [c]~ :=
  eqToIso (normalization_of _ _)

public instance : (normalization C).Monoidal :=
    inferInstanceAs (FreeSymmetricMonoidalCategory.project _).Monoidal
public instance : (normalization C).Braided :=
    inferInstanceAs (FreeSymmetricMonoidalCategory.project _).Braided

end Normalization

section Inclusion

open FreeSListQuiv

/-- The recursive data defining the inclusion functor `SList C ⥤ FreeSMC C`. -/
def inclusionRecData : RecursiveFunctorData C (FreeSymmetricMonoidalCategory C) where
  nilObj := 𝟙_ _
  consF c := tensorLeft (of c)
  swapIso x y := NatIso.ofComponents
    (fun Z => (α_ _ _ _).symm ≪≫ (whiskerRightIso (β_ _ _) Z) ≪≫ (α_ _ _ _))
    (fun f => by
      dsimp
      simp only [Category.assoc]
      simp_rw [ tensor_whiskerLeft_symm, Iso.hom_inv_id_assoc, ← whisker_exchange_assoc]
      simp)
  swap_inv c c' l := by simp [← comp_whiskerRight_assoc]
  hexagon c c' c'' l := by
    dsimp
    monoidal_simps
    simp_rw [pentagon_hom_inv_inv_inv_inv_assoc, pentagon_hom_hom_inv_hom_hom_assoc,
      whisker_assoc_symm_assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc]
    have :=
      ((α_ _ _ _).hom ≫= BraidedCategory.yang_baxter (of c) (of c') (of c'')) =≫ (α_ _ _ _).inv
    simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id] at this
    simp [this]

/-- The inclusion functor `J : SList C ⥤ FreeSMC C` mapping lists to right-associated trees. -/
public def J : SList C ⥤ FreeSymmetricMonoidalCategory C :=
  (inclusionRecData C).functor

section
-- Computation rules for J

variable {C}

public lemma J_obj_unit : (J C).obj ([]~) = 𝟙_ _ :=
  RecursiveFunctorData.functor_obj_nil _

public lemma J_obj_cons (c : C) (l : SList C) : (J C).obj (c ::~ l) = (of c) ⊗ (J C).obj l :=
  RecursiveFunctorData.functor_obj_cons _ _ _

@[expose] public def JObjNilIso : (J C).obj []~ ≅ 𝟙_ _ := eqToIso J_obj_unit

@[expose] public def JObjConsIso (c : C) (l : SList C) :
    (J C).obj (c ::~ l) ≅ (of c) ⊗ (J C).obj l :=
  eqToIso <| J_obj_cons c l

lemma J_map_cons_map (c : C) {l l' : SList C} (f : l ⟶ l') :
    (J C).map ((cons c).map f) =
      (JObjConsIso _ _).hom ≫
      ((of c) ◁ (J C).map f) ≫
      (JObjConsIso _ _).inv :=
  RecursiveFunctorData.functor_map_cons_map _ _ _

lemma J_map_swap (c c' : C) (l : SList C) :
    (J C).map (β~ c c' l) =
    (JObjConsIso _ _).hom ≫
      ((of c) ◁ (JObjConsIso _ _).hom) ≫
      ((α_ _ _ _).symm ≪≫ (whiskerRightIso (β_ _ _) _) ≪≫ (α_ _ _ _)).hom ≫
      ((of c') ◁ (JObjConsIso _ _).inv) ≫
      (JObjConsIso _ _).inv :=
  RecursiveFunctorData.functor_map_swap _ _ _ _

end

end Inclusion

section MonoidalStructure

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism of bifunctors J(-) ⊗ J(-) ⟶ J(- ⊗ -)
that defines the monoidal structure on J. -/
public def μIso :
    (Functor.whiskeringLeft₂ _|>.obj (J C) |>.obj (J C) |>.obj
      (curriedTensor (FreeSymmetricMonoidalCategory C))) ≅
    (Functor.postcompose₂.obj (J C)).obj (curriedTensor (SList C)) :=
  recNatIso
    (NatIso.ofComponents
      (fun x ↦ whiskerRightIso JObjNilIso _ ≪≫ (λ_ _) ≪≫ (J C).mapIso ((λ_ _).symm ≪≫
        whiskerRightIso unitIsoNil x))
      fun {x y} f ↦ by
        dsimp
        monoidal_simps
        simp only [Functor.map_comp, whisker_exchange_assoc, id_whiskerLeft, Category.assoc,
          Iso.inv_hom_id_assoc]
        congr 2
        simp_rw [← Functor.map_comp]
        congr 1
        rw [hom_eq_iff_toEquiv_eq]
        ext i : 1
        obtain ⟨i, rfl⟩ := (Ψ _ _).surjective i
        cases i with
        | inl i => simp only [length_nil] at i; exact Fin.elim0 i
        | inr i => simp )
    (fun c l μ ↦
      NatIso.ofComponents
        (fun x ↦
          whiskerRightIso (JObjConsIso _ _) _ ≪≫ (α_ _ _ _) ≪≫ whiskerLeftIso (of c) (μ.app _) ≪≫
            (JObjConsIso _ _).symm ≪≫ (J C).mapIso (tensorObjConsIso c l x).symm)
        fun {x y} f ↦ by
          dsimp
          simp only [whisker_exchange_assoc, tensor_whiskerLeft, Category.assoc,
            Iso.inv_hom_id_assoc]
          congr 2
          have := NatIso.naturality_2 μ f
          dsimp at this
          simp_rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← this]
          simp [J_map_cons_map, whiskerLeft_cons])
    (fun u v l μ ↦ by
      ext x
      dsimp
      simp only [J_map_swap, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Category.assoc,
        comp_whiskerRight, whisker_assoc, whiskerLeft_comp, inv_hom_whiskerRight_assoc,
        Iso.inv_hom_id_assoc]
      congr 3
      simp_rw [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id]
      simp only [comp_whiskerRight, id_whiskerRight, Category.id_comp, whiskerLeft_comp,
        Category.assoc, pentagon_assoc]
      simp_rw [tensor_whiskerLeft_symm, Category.assoc, Iso.hom_inv_id_assoc,
        whiskerRight_tensor_symm_assoc, Iso.inv_hom_id_assoc, ← whisker_exchange_assoc]
      simp only [tensor_whiskerLeft, Category.assoc, pentagon_inv_hom_hom_hom_hom_assoc,
        Iso.inv_hom_id_assoc]
      congr 2
      simp only [whiskerRight_swap, Functor.map_comp, J_map_cons_map, J_map_swap, Iso.trans_hom,
        Iso.symm_hom, whiskerRightIso_hom, Category.assoc, Iso.inv_hom_id_assoc,
        Iso.map_inv_hom_id_assoc]
      simp_rw [← whiskerLeft_comp_assoc, Iso.map_inv_hom_id_assoc, Iso.inv_hom_id, whiskerLeft_id,
        Category.id_comp])
    (fun c l l' f μ μ' h ↦ by
      ext x
      replace h := congr_app h x
      dsimp at μ μ' h ⊢
      simp only [J_map_cons_map, comp_whiskerRight, whisker_assoc, Category.assoc,
        inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc, whiskerRight_cons_map, Functor.map_comp,
        Iso.map_inv_hom_id_assoc]
      simp_rw [← whiskerLeft_comp_assoc, h])

@[local simp]
lemma μIso_hom_app_nil_app (t : SList C) :
    ((μIso C).hom.app []~).app t =
      JObjNilIso.hom ▷ _ ≫ (λ_ _).hom ≫ (J C).map ((λ_ _).inv ≫
        unitIsoNil.hom ▷ t) := by
  simp [μIso]

@[local simp]
lemma μIso_hom_app_cons_app (c : C) (l t : SList C) :
    ((μIso C).hom.app (c ::~ l)).app t =
    (JObjConsIso _ _).hom ▷ _ ≫ (α_ _ _ _).hom ≫ (of c) ◁ ((μIso C).hom.app l).app t ≫
      (JObjConsIso _ _).inv ≫ (J C).map (tensorObjConsIso c l _).inv := by
  simp [μIso]

@[reassoc (attr := local simp)]
lemma μIso_natural_left {x y : SList C}
    (f : x ⟶ y) (z : SList C) :
    (J C).map f ▷ (J C).obj z ≫ ((μIso C).hom.app y).app z =
    ((μIso C).hom.app x).app z ≫ (J C).map (f ▷ z) := by
  simpa [-NatTrans.naturality] using congr_app ((μIso C).hom.naturality f) z

@[reassoc (attr := local simp)]
lemma μIso_natural_right
    (z : SList C)
    {x y : SList C} (f : x ⟶ y) :
    (J C).obj z ◁ (J C).map f ≫ ((μIso C).hom.app z).app y =
    ((μIso C).hom.app z).app x ≫ (J C).map (z ◁ f) := by
  simpa [-NatTrans.naturality] using ((μIso C).hom.app z).naturality f

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition to define the monoidal structure on J C. -/
@[expose] public def JCoreMonoidal : (J C).CoreMonoidal where
  εIso := JObjNilIso.symm ≪≫ (J C).mapIso unitIsoNil.symm
  μIso x y := ((μIso C).app x).app y
  μIso_hom_natural_left {x y} f z := by simp
  μIso_hom_natural_right x {y z} f := by simp
  associativity x y z := by
    induction x using SList.cons_induction with
    | nil =>
      dsimp
      simp only [μIso_hom_app_nil_app, Functor.map_comp, comp_whiskerRight,
        leftUnitor_whiskerRight, Category.assoc, μIso_natural_left_assoc,
        Functor.postcompose₂_obj_obj_obj_obj, curriedTensor_obj_obj, leftUnitor_inv_whiskerRight,
        whiskerRight_tensor]
      simp_rw [whisker_exchange_assoc, ← Functor.map_comp_assoc]
      simp
    | cons c x hr =>
      simp only [Iso.app_hom, μIso_hom_app_cons_app, Functor.postcompose₂_obj_obj_obj_obj,
        curriedTensor_obj_obj, comp_whiskerRight, whisker_assoc, Category.assoc,
        μIso_natural_left_assoc, inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc] at hr ⊢
      simp_rw [whiskerRight_tensor_symm_assoc, whisker_exchange_assoc]
      congr 2
      simp only [pentagon_inv_hom_hom_hom_inv_assoc, tensor_whiskerLeft, Category.assoc,
        Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
      have := congr(of c ◁ $hr) =≫ of c ◁ (J C).map (α_ x y z).inv
      simp_rw [← whiskerLeft_comp, Category.assoc, Iso.map_hom_inv_id] at this
      simp_rw [Category.comp_id, whiskerLeft_comp] at this
      simp_rw [reassoc_of% this, whiskerLeft_inv_hom_assoc]
      congr 2
      -- Now all remaining morphisms are eqToHoms under the hood, so we don’t have to try
      -- to be too smart.
      -- An alternative proof that does not use strictness is to show that JObjConsIso is
      -- natural in the second var.
      rw [show (α_ x y z) = SList.associator x y z by rfl,
        show α_ (c ::~ x) y z = SList.associator _ _ _ by rfl]
      simp [SList.associator, tensorObjConsIso, JObjConsIso, eqToHom_map]
  left_unitality x := by simp
  right_unitality x := by
    induction x using SList.cons_induction with
    | nil => simp [whisker_exchange_assoc, unitors_equal, unitors_inv_equal]
    | cons c x hr =>
      simp only [Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
        whiskerLeft_comp, Iso.app_hom, Category.assoc, μIso_natural_right_assoc,
        Functor.postcompose₂_obj_obj_obj_obj, curriedTensor_obj_obj,
        μIso_hom_app_cons_app] at hr ⊢
      -- here, we basically want to change the ((μIso C).hom.app x).app (𝟙_ (SList C)) term
      -- to a ((μIso C).hom.app x).app ([]~) that appears in hr, to simplify things.
      have := μIso_natural_right C x unitIsoNil.hom =≫ (J C).map (x ◁ unitIsoNil.inv)
      simp only [Functor.postcompose₂_obj_obj_obj_obj, curriedTensor_obj_obj, Category.assoc,
        Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, ← Functor.map_comp, whiskerLeft_hom_inv,
        Functor.map_id, Category.comp_id] at this
      simp_rw [← this, whiskerLeft_comp_assoc]
      have := (J C).obj x ◁ JObjNilIso.hom ≫= hr =≫
        (inv <| (J C).map (x ◁ unitIsoNil.inv) ≫ (J C).map (ρ_ x).hom)
      simp only [IsIso.inv_comp, Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id,
        Category.comp_id, whiskerLeft_hom_inv_assoc] at this
      simp only [← this, whiskerLeft_comp, whiskerLeft_rightUnitor, Category.assoc,
        whiskerLeft_inv_hom'_assoc]
      simp_rw [tensor_whiskerLeft_symm_assoc, Iso.hom_inv_id_assoc, whisker_exchange_assoc,
        ← whiskerLeft_comp_assoc, Iso.map_inv_hom_id_assoc]
      simp only [whiskerRight_id, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp, Category.assoc,
        Iso.inv_hom_id_assoc, ← cancel_epi (ρ_ ((J C).obj (c ::~ x))).inv]
      -- Now everything is strict.
      simp [show (ρ_ _) = SList.rightUnitor _ by rfl,
        SList.rightUnitor, tensorObjConsIso, JObjConsIso, eqToHom_map]

@[expose] public instance : (J C).Monoidal := JCoreMonoidal C|>.toMonoidal

variable {C}

@[local simp]
lemma J_μ_app_nil_app (t : SList C) :
    Functor.LaxMonoidal.μ (J C) []~ t =
      JObjNilIso.hom ▷ _ ≫ (λ_ _).hom ≫ (J C).map ((λ_ _).inv ≫
        unitIsoNil.hom ▷ t) :=
  μIso_hom_app_nil_app C _

@[local simp]
lemma J_μ_app_cons_app (c : C) (l t : SList C) :
    Functor.LaxMonoidal.μ (J C) (c ::~ l) t =
    (JObjConsIso _ _).hom ▷ _ ≫ (α_ _ _ _).hom ≫ (of c) ◁ Functor.LaxMonoidal.μ (J C) l t ≫
      (JObjConsIso _ _).inv ≫ (J C).map (tensorObjConsIso c l _).inv :=
  μIso_hom_app_cons_app C _ _ _

lemma J_ε :
    Functor.LaxMonoidal.ε (J C) = JObjNilIso.inv ≫ (J C).map unitIsoNil.inv :=
  rfl

lemma J_η :
    Functor.OplaxMonoidal.η (J C) = (J C).map unitIsoNil.hom ≫ JObjNilIso.hom :=
  rfl

/-- A version of `braiding_inv_tensorUnit_right` seen through JObjNilIso. -/
lemma braiding_inv_J_obj_nil_right (x : FreeSymmetricMonoidalCategory C) :
    (β_ x ((J C).obj []~)).inv =
    JObjNilIso.hom ▷ x ≫ (λ_ x).hom ≫ (ρ_ x).inv ≫ x ◁ JObjNilIso.inv := by
  have := BraidedCategory.braiding_naturality_right x JObjNilIso.hom =≫ JObjNilIso.inv ▷ x
  simp at this
  rw [← IsIso.inv_eq_inv]
  simp [← this]

/-- A version of `braiding_inv_tensorUnit_right` seen through JObjNilIso. -/
lemma braiding_hom_J_obj_nil_right (x : FreeSymmetricMonoidalCategory C) :
    (β_ x ((J C).obj []~)).hom =
     x ◁ JObjNilIso.hom ≫ (ρ_ x).hom ≫ (λ_ x).inv ≫ JObjNilIso.inv ▷ x := by
  have := BraidedCategory.braiding_naturality_right x JObjNilIso.hom =≫ JObjNilIso.inv ▷ x
  simp at this
  rw [← IsIso.inv_eq_inv]
  simp [← this]

lemma J_braided_nil_nil :
    Functor.LaxMonoidal.μ (J C) []~ []~ ≫ (J C).map (β_ []~ []~).hom =
    (β_ ((J C).obj []~) ((J C).obj []~)).hom ≫ Functor.LaxMonoidal.μ (J C) []~ []~ := by
  simp only [J_μ_app_nil_app,
    Functor.LaxMonoidal.left_unitality, Functor.map_comp, Category.assoc,
    Iso.map_hom_inv_id_assoc, braiding_hom_app_nil]
  simp_rw [← Functor.LaxMonoidal.μ_natural_left, ← Functor.LaxMonoidal.μ_natural_left_assoc,
    J_μ_app_nil_app, J_ε, Category.assoc, Functor.map_comp,
    ← BraidedCategory.braiding_naturality_right_assoc, braiding_tensorUnit_right]
  simp_rw [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.map_inv_hom_id_assoc,
    ← whisker_exchange_assoc]
  simp [-Functor.LaxMonoidal.left_unitality, -Functor.LaxMonoidal.right_unitality,
    ← unitors_equal, ← cancel_epi ((J C).obj []~ ◁ JObjNilIso.inv), whisker_exchange_assoc,
    ← unitors_inv_equal]

lemma J_braided_nil_left (x : SList C) :
    Functor.LaxMonoidal.μ (J C) x []~ ≫ (J C).map (β_ x []~).hom =
    (β_ ((J C).obj x) ((J C).obj []~)).hom ≫ Functor.LaxMonoidal.μ (J C) []~ x := by
  induction x using SList.cons_induction with
  | nil => exact J_braided_nil_nil
  | cons c x hr =>
    simp only [J_μ_app_cons_app]
    have := hr =≫ (J C).map (β_ x []~).inv
    simp only [Category.assoc, Iso.map_hom_inv_id, Category.comp_id] at this
    rw [this]
    simp only [Category.assoc, J_μ_app_nil_app]
    rw [← cancel_epi ((JObjConsIso c x).inv ▷ (J C).obj []~)]
    simp only [inv_hom_whiskerRight_assoc, BraidedCategory.braiding_naturality_left_assoc,
      whisker_exchange_assoc, whiskerRight_tensor_assoc, leftUnitor_naturality_assoc]
    rw [← cancel_epi (α_ (of c) ((J C).obj x) ((J C).obj []~)).inv]
    simp only [Iso.inv_hom_id_assoc, BraidedCategory.hexagon_reverse_assoc,
      SList.braiding_hom_app_nil, whiskerLeft_comp, Category.assoc,
      SList.braiding_inv_app_nil,
      SList.whiskerLeft_cons, Category.assoc, cancel_epi]
    -- At this point all of the braiding have been rewritten,
    -- and what remains is "pure" monoidal category stuff
    simp only [Functor.map_comp, whiskerLeft_comp, Iso.map_inv_hom_id_assoc, Category.assoc]
    simp only [← Category.assoc, cancel_mono]
    simp only [Category.assoc, braiding_hom_J_obj_nil_right]
    simp only [comp_whiskerRight, whisker_assoc, leftUnitor_inv_whiskerRight, Category.assoc,
      triangle_assoc_comp_right_assoc, Iso.inv_hom_id_assoc, cancel_epi]
    simp_rw [← whiskerLeft_comp_assoc, ← Functor.map_comp_assoc, hom_inv_whiskerRight_assoc,
      Iso.inv_hom_id_assoc, ← comp_whiskerRight_assoc]
    simp only [← Functor.map_comp, Category.assoc, inv_hom_whiskerRight, id_whiskerRight,
      Category.id_comp, Iso.inv_hom_id_assoc, ]
    simp only [Functor.map_comp, J_map_cons_map, Category.assoc, Iso.inv_hom_id_assoc,
      ← whiskerLeft_comp_assoc]
    have := (JObjConsIso c x).inv ≫= J_map_cons_map c ((ρ_ x).inv)
    simp only [Iso.inv_hom_id_assoc] at this
    simp only [← Functor.map_comp, whiskerLeft_hom_inv, Category.comp_id,
      ← reassoc_of% this, ← cancel_epi (JObjConsIso c x).hom, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      ← Functor.map_id]
    congr 1
    -- and now everything lives in SList and are morphisms known to be eqToHoms.
    simp [show (ρ_ _) = SList.rightUnitor _ by rfl,
      SList.rightUnitor, tensorObjConsIso, eqToHom_map]

lemma J_braided_nil_right (x : SList C) :
    Functor.LaxMonoidal.μ (J C) []~ x ≫ (J C).map (β_ []~ x).hom =
    (β_ ((J C).obj []~) ((J C).obj x)).hom ≫ Functor.LaxMonoidal.μ (J C) x []~ := by
  simp_rw [SymmetricCategory.braiding_swap_eq_inv_braiding]
  have := J_braided_nil_left x =≫  (J C).map (β_ x []~).inv
  simp only [Category.assoc, Iso.map_hom_inv_id, Category.comp_id] at this
  rw [this]
  simp

@[reassoc]
private lemma whiskerLeft_map_hom_inv
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory D]
    (x : D) {y z : C} (F : C ⥤ D) (e : y ≅ z) :
    x ◁ F.map e.hom ≫ x ◁ F.map e.inv = 𝟙 _ := by
  simp [← whiskerLeft_comp]

@[reassoc]
private lemma whiskerLeft_map_inv_hom
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory D]
    (x : D) {y z : C} (F : C ⥤ D) (e : y ≅ z) :
    x ◁ F.map e.inv ≫ x ◁ F.map e.hom = 𝟙 _ := by
  simp [← whiskerLeft_comp]

@[reassoc]
private lemma whiskerLeft_whiskerLeft_inv_hom
    {D : Type*} [Category* D] [MonoidalCategory D]
    (x y : D) {z t : D} (e : z ≅ t) :
    x ◁ y ◁ e.inv ≫ x ◁ y ◁ e.hom = 𝟙 _ := by
  simp [← whiskerLeft_comp]

@[reassoc]
private lemma whiskerLeft_whiskerLeft_hom_inv
    {D : Type*} [Category* D] [MonoidalCategory D]
    (x y : D) {z t : D} (e : z ≅ t) :
    x ◁ y ◁ e.hom ≫ x ◁ y ◁ e.inv = 𝟙 _ := by
  simp [← whiskerLeft_comp]

@[reassoc]
private lemma whiskerLeft_hom_inv_whiskerRight
    {D : Type*} [Category* D] [MonoidalCategory D]
    (x : D) {y z : D} (e : y ≅ z) (t : D) :
  x ◁ e.hom ▷ t ≫ x ◁ e.inv ▷ t = 𝟙 _ := by
  simp [← whiskerLeft_comp]

@[reassoc]
private lemma whiskerLeft_inv_hom_whiskerRight
    {D : Type*} [Category* D] [MonoidalCategory D]
    (x : D) {y z : D} (e : y ≅ z) (t : D) :
  x ◁ e.inv ▷ t ≫ x ◁ e.hom ▷ t = 𝟙 _ := by
  simp [← whiskerLeft_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The functor `J C` is braided (and hence symmetric). Note that by the universal
property of the free symmetric monoidal category, this statement "defines"
the counit of the equivalence `SList C ≌ FreeSymmetricMonoidalCategory C`, as thanks to
it both `𝟭 _` and `K C ⋙ J C` are symmetric monoidal functors with
isomorphic values on the generators. -/
public instance : (J C).Braided where
  braided x y := by
    induction y using SList.cons_induction generalizing x with
    | nil => exact J_braided_nil_left _
    | cons c l ih =>
      induction x using SList.cons_induction generalizing c l with
      | nil => exact J_braided_nil_right _
      | cons c' l' hr =>
        /- Clearly the hardest computation here. This one is a massive pain.
        First the idea is to get rid of the terms of form
        Functor.LaxMonoidal.μ (J C) (c ::~ l) (c' ::~ l') and use existing commutations
        to partially swap out some terms. -/
        simp only [J_μ_app_cons_app]
        have := hr c l ih =≫ (J C).map (β_ l' (c ::~ l)).inv
        simp only [Category.assoc, Iso.map_hom_inv_id, Category.comp_id] at this
        simp only [this, J_μ_app_cons_app]
        have := (β_ ((J C).obj (c' ::~ l')) ((J C).obj l)).inv ≫= ih (c' ::~ l')
        simp only [Iso.inv_hom_id_assoc] at this
        simp only [← this, J_μ_app_cons_app, Category.assoc,
          ← SymmetricCategory.braiding_swap_eq_inv_braiding]
        /- Then we want to get rid of the `(J C).obj (c ::~ l)` in arguments of the
        braiding, turning them into `of c ⊗ (J C).obj l`. -/
        simp_rw [← cancel_epi ((JObjConsIso c' l').inv ▷ (J C).obj (c ::~ l)),
          inv_hom_whiskerRight_assoc, BraidedCategory.braiding_naturality_left_assoc,
          SymmetricCategory.braiding_swap_eq_inv_braiding (((J C).obj (c' ::~ l'))),
          SymmetricCategory.braiding_swap_eq_inv_braiding (((J C).obj (c ::~ l))),
          ← BraidedCategory.braiding_inv_naturality_right_assoc, whisker_exchange_assoc]
        simp_rw [← BraidedCategory.braiding_inv_naturality_right_assoc]
        /- Then, we bring up the computation rules for the braiding in SList, which describes
        `β_ (c ::~ l) _` -/
        simp_rw [SList.braiding_hom_cons_right, SList.braiding_hom_cons_left]
        /- then a short round of "cleaning up" -/
        simp only [whiskerLeft_comp, Category.assoc, Functor.map_comp,
          J_map_cons_map, Iso.inv_hom_id_assoc, whiskerLeft_map_inv_hom_assoc,
          whiskerLeft_inv_hom_assoc]
        /- cancel redundant terms on the right -/
        simp only [← Category.assoc, cancel_mono]
        simp only [Category.assoc]
        simp only [associator_naturality_right_assoc, ← Iso.eq_inv_comp,
          ← associator_inv_naturality_right_assoc, whiskerLeft_whiskerLeft_inv_hom_assoc,
          cancel_epi]
        /- Now we want to get rid of the tensors in arguments of braidings. -/
        simp only [BraidedCategory.braiding_tensor_left_inv, Category.assoc,
          BraidedCategory.braiding_tensor_right_inv]
        /- A second cleanup round is able to clear some noise now. -/
        monoidal_simps
        simp only [Functor.comp_obj,
          Functor.flip_obj_obj, curriedTensor_obj_obj, whiskerLeft_inv_hom_assoc,
          pentagon_hom_hom_inv_hom_hom_assoc, inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc,
          pentagon_inv_assoc, cancel_epi]
        /- Now we rewrite Functor.LaxMonoidal.μ (J C) l' l in terms of
        Functor.LaxMonoidal.μ (J C) l l' -/
        have := ih l' =≫ (J C).map (β_ l' l).inv
        simp only [Category.assoc, Iso.map_hom_inv_id, Category.comp_id] at this
        simp only [this, whiskerLeft_comp, whiskerLeft_whiskerLeft_inv_hom_assoc,
          ← SymmetricCategory.braiding_swap_eq_inv_braiding (of c'),
          whiskerLeft_inv_hom_whiskerRight_assoc]
        /- Now we have to perform more clean up, using the computation rules for the braiding in
        SList. -/
        simp only [Q_inv_app_cons, Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj,
          Functor.map_comp, J_map_cons_map, J_map_swap, Iso.trans_hom, Iso.symm_hom,
          whiskerRightIso_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc,
          pentagon_assoc] -- generated by simp? [Q_inv_app_cons, J_map_cons_map, J_map_swap]
        simp only [← whiskerLeft_comp_assoc, ← Functor.map_comp_assoc,
          Iso.hom_inv_id_app_assoc, Iso.inv_hom_id]
        simp only [whiskerLeft_comp, Functor.map_id, Category.id_comp, Iso.inv_hom_id,
          Category.comp_id, Iso.map_inv_hom_id, whiskerLeft_inv_hom, Category.assoc]
        simp only [← SymmetricCategory.braiding_swap_eq_inv_braiding (of c)]
        simp only [tensor_whiskerLeft_symm_assoc, Iso.hom_inv_id_assoc, cancel_epi,
          whisker_exchange_assoc, whiskerRight_tensor_symm_assoc, Iso.inv_hom_id_assoc]
        simp [SymmetricCategory.braiding_swap_eq_inv_braiding]

end MonoidalStructure

noncomputable section Equivalence

attribute [-simp] Functor.LaxMonoidal.left_unitality

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `η : 𝟭 ≅ J ⋙ K` on `SList C`. -/
public def unitIso : 𝟭 (SList C) ≅ J C ⋙ normalization C :=
  recNatIso
    (SList.unitIsoNil.symm ≪≫ (Functor.Monoidal.εIso _) ≪≫
      (normalization C).mapIso JObjNilIso.symm) -- nil
    (fun x p e₀ ↦
      (x>~).mapIso ((λ_ p).symm ≪≫
        whiskerRightIso SList.unitIsoNil p) ≪≫
        (SList.tensorObjConsIso x []~ p).symm ≪≫
        whiskerLeftIso _ e₀ ≪≫
        (Functor.Monoidal.μIso (normalization C) (of x) ((J C).obj p)) ≪≫
        (normalization C).mapIso (JObjConsIso x p).symm) --cons
    (fun x y l' p ↦ by
      -- simp? [J_map_swap]
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.mapIso_trans,
        Functor.mapIso_symm, Iso.trans_assoc, whiskerLeftIso_trans, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_inv, Functor.mapIso_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
        Functor.Monoidal.μIso_hom, Functor.comp_map,
        J_map_swap, Category.assoc, Functor.map_comp, Iso.map_inv_hom_id_assoc]
      have e₁ := Functor.LaxMonoidal.μ_natural_right (normalization C) (of x) (JObjConsIso y l').inv
      have e₂ := Functor.LaxMonoidal.μ_natural_right (normalization C) (of y) (JObjConsIso x l').inv
      dsimp [normalization_of] at e₁ e₂
      simp only [reassoc_of% e₁, ← Functor.map_comp, whiskerLeft_inv_hom_assoc, reassoc_of% e₂]
      simp only [Functor.map_comp, ← Category.assoc, cancel_mono]; simp only [Category.assoc]
      simp_rw [Functor.Monoidal.map_whiskerRight_assoc (F := normalization C), Functor.map_braiding,
        Functor.Monoidal.map_associator_inv]
      -- simp?
      simp only [normalization_of, comp_whiskerRight, Category.assoc,
        Functor.LaxMonoidal.associativity, Functor.Monoidal.μ_δ_assoc,
        Functor.Monoidal.whiskerRight_μ_δ_assoc, Functor.Monoidal.whiskerLeft_μ_δ_assoc]
      --cancel equal terms on the right, we definitely need a simproc for this
      simp only [← Category.assoc, cancel_mono]; simp only [Category.assoc]
      simp_rw [tensor_whiskerLeft_symm_assoc, Iso.hom_inv_id_assoc, whisker_exchange_assoc]
      simp only [tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      simp only [← Category.assoc, cancel_mono]; simp only [Category.assoc]
      -- at this point everything remaining is "noise" in SList around β~ x y l' or β_ [x]~ [y]~ l'.
      -- So we can just check that the remaining morphisms give the same permutations
      rw [hom_eq_iff_toEquiv_eq]
      ext i
      obtain ⟨i, rfl⟩ := Ψ _ _ |>.surjective i
      cases i with
      | inl i =>
        obtain ⟨i, rfl⟩ := Φ _ _ |>.surjective i
        cases i with
        | inr i => simp only [length_nil] at i; exact Fin.elim0 i
        | inl i =>
          obtain rfl : i = () := rfl
          simp [toEquiv_tensorObjConsIso_inv_Φ_inr, toEquiv_tensorObjConsIso_inv_Φ_inl,
            toEquiv_cons_map_Φ_inl, toEquiv_cons_map_Φ_inr, toEquiv_swap_Φ_inl]
      | inr i =>
        obtain ⟨i, rfl⟩ := Ψ _ _ |>.surjective i
        cases i with
        | inl i =>
          obtain ⟨i, rfl⟩ := Φ _ _ |>.surjective i
          cases i with
          | inr i => simp only [length_nil] at i; exact Fin.elim0 i
          | inl i =>
            obtain rfl : i = () := rfl
            simp [toEquiv_tensorObjConsIso_inv_Φ_inr, toEquiv_tensorObjConsIso_inv_Φ_inl,
              toEquiv_cons_map_Φ_inl, toEquiv_cons_map_Φ_inr, toEquiv_swap_Φ_inr_Φ_inl]
        | inr i =>
          simp [toEquiv_tensorObjConsIso_inv_Φ_inr, toEquiv_cons_map_Φ_inr,
            toEquiv_swap_Φ_inr_Φ_inr])
    (fun x l l' f pl pl' h ↦ by
      dsimp at h ⊢
      have := congr(x::~ₘ $h)
      simp only [Functor.map_comp] at this
      simp only [Functor.map_comp, whiskerLeft_cons, Category.assoc, Iso.inv_hom_id_assoc,
        J_map_cons_map, Iso.map_inv_hom_id_assoc]
      simp_rw [← Functor.map_comp_assoc, ← Functor.map_comp, ← whisker_exchange,
        leftUnitor_inv_naturality_assoc, ← whiskerLeft_comp_assoc, h]
      simp only [whiskerLeft_comp, id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
        Functor.map_comp, cancel_epi]
      simp only [← Category.assoc, cancel_mono]; simp only [Category.assoc]
      simp_rw [Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.μ_δ_assoc]
      simp only [Functor.OplaxMonoidal.left_unitality, Functor.map_comp, Category.assoc,
        normalization_of, whiskerLeft_cons, Iso.inv_hom_id_assoc]
      simp only [← Category.assoc, cancel_mono]; simp only [Category.assoc]
      simp only [← Functor.map_comp, ← Functor.map_comp_assoc]; congr 1
      simp [← whisker_exchange, -Functor.map_comp, ← Functor.map_comp_assoc ])

@[simp, reassoc]
lemma unitIso_hom_app_nil :
    (unitIso C).hom.app []~ =
    unitIsoNil.inv ≫
      Functor.LaxMonoidal.ε (normalization C) ≫
      (normalization C).map JObjNilIso.inv := by
  simp [unitIso]

@[simp, reassoc]
lemma unitIso_hom_app_cons (c : C) (l : SList C) :
    (unitIso C).hom.app (c ::~ l) =
    (c ::~ₘ (λ_ l).inv) ≫
    (c ::~ₘ unitIsoNil.hom ▷ l) ≫
      (tensorObjConsIso c []~ l).inv ≫
      [c]~ ◁ (unitIso C).hom.app l ≫
      Functor.LaxMonoidal.μ (normalization C) (of c) ((J C).obj l) ≫
      (normalization C).map (JObjConsIso c l).inv := by
  simp [unitIso]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
lemma unitIso_inv_app_nil :
    (unitIso C).inv.app []~ =
      (normalization C).map JObjNilIso.hom ≫
       Functor.OplaxMonoidal.η (normalization C) ≫ unitIsoNil.hom := by
  rw [← IsIso.inv_eq_inv]
  simp [unitIso]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
lemma unitIso_inv_app_cons (c : C) (l : SList C) :
    (unitIso C).inv.app (c ::~ l) =
    (normalization C).map (JObjConsIso c l).hom ≫
      Functor.OplaxMonoidal.δ (normalization C) (of c) ((J C).obj l) ≫
      [c]~ ◁ (unitIso C).inv.app l ≫
      (tensorObjConsIso c []~ l).hom ≫
      (c ::~ₘ unitIsoNil.inv ▷ l) ≫
      (c ::~ₘ (λ_ l).hom) := by
  rw [← IsIso.inv_eq_inv]
  simp only [← Functor.map_inv, IsIso.Iso.inv_hom, IsIso.inv_comp]
  simp [unitIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma unitIso_inv_app_singleton (c : C) :
    (unitIso C).inv.app ([c]~) =
    (normalization C).map ((JObjConsIso c []~).hom ≫ of c ◁ JObjNilIso.hom ≫ (ρ_ (of c)).hom) := by
  simp only [Functor.comp_obj, Functor.id_obj, unitIso_inv_app_cons, normalization_of,
    unitIso_inv_app_nil, whiskerLeft_comp,
    Category.assoc, Functor.map_comp, Functor.Monoidal.map_whiskerLeft,
    Functor.Monoidal.map_rightUnitor,
    Functor.Monoidal.μ_δ_assoc]
  simp only [whiskerLeft_cons, whiskerLeft_nil, Functor.OplaxMonoidal.left_unitality,
    unitors_inv_equal, Category.assoc, ← Functor.map_comp_assoc, whiskerRight_id,
    Iso.inv_hom_id_assoc, ← Functor.map_comp, hom_inv_whiskerRight_assoc, Iso.inv_hom_id,
    Category.comp_id, Iso.hom_inv_id_assoc,
    Functor.OplaxMonoidal.left_unitality_hom_assoc]
  congr 3
  simp only [← unitors_inv_equal]
  simp [rightUnitor_cons]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma unitIso_hom_app_singleton (c : C) :
    (unitIso C).hom.app ([c]~) =
    (normalization C).map ((ρ_ (of c)).inv ≫ of c ◁ JObjNilIso.inv ≫ (JObjConsIso c []~).inv) := by
  rw [← IsIso.inv_eq_inv, ← NatIso.isIso_inv_app, IsIso.Iso.inv_hom, unitIso_inv_app_singleton]
  simp [← Functor.map_inv]

set_option backward.isDefEq.respectTransparency false in
public instance : (unitIso C).hom.IsMonoidal where
  unit := by
    have := (unitIso C).hom.naturality unitIsoNil.inv
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, unitIso_hom_app_nil,
      Functor.comp_map, Category.assoc, Iso.cancel_iso_inv_left] at this
    simp [this, J_ε]
  tensor x y := by
    induction x using SList.cons_induction with
    | nil =>
      let e₁ : []~ ⊗ y ≅ y := whiskerRightIso unitIsoNil.symm y ≪≫ λ_ _
      have nat₁ := (unitIso C).hom.naturality e₁.inv
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at nat₁
      simp only [Functor.id_obj, Functor.comp_obj, Functor.LaxMonoidal.id_μ, Category.id_comp,
        unitIso_hom_app_nil, Functor.LaxMonoidal.comp_μ]
      rw [← cancel_epi e₁.inv, nat₁]
      -- simp? [tensorHom_def, e₁, ← whisker_exchange_assoc, cancel_epi, J_μ_app_nil_app] says
      simp only [Functor.comp_obj, Iso.trans_inv, whiskerRightIso_inv, Iso.symm_inv,
        Functor.map_comp, tensorHom_def, comp_whiskerRight, Category.assoc,
        ← whisker_exchange_assoc, Functor.LaxMonoidal.μ_natural_left_assoc, id_whiskerLeft,
        Functor.OplaxMonoidal.left_unitality,
        Functor.Monoidal.whiskerRight_η_ε_assoc, Functor.Monoidal.δ_μ_assoc,
        hom_inv_whiskerRight_assoc, Iso.inv_hom_id_assoc, cancel_epi, e₁]
      simp [← Functor.map_comp, J_μ_app_nil_app]
    | cons c x hr =>
      simp only [Functor.id_obj, Functor.comp_obj, Functor.LaxMonoidal.id_μ, Category.id_comp,
        Functor.LaxMonoidal.comp_μ, unitIso_hom_app_cons] at hr ⊢
      have nat₁ := (unitIso C).hom.naturality (tensorObjConsIso c x y).inv
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, unitIso_hom_app_cons,
        whiskerRight_tensor, Functor.map_comp, Category.assoc, Functor.comp_map] at nat₁
      rw [← cancel_epi (tensorObjConsIso c x y).inv, nat₁, hr]
      simp only [Functor.comp_obj, tensorHom_def, Category.assoc, whiskerLeft_comp,
        comp_whiskerRight, whisker_assoc, J_μ_app_cons_app, Functor.map_comp]
      simp_rw [Functor.Monoidal.map_whiskerLeft_assoc, Functor.Monoidal.map_whiskerRight_assoc,
        Functor.Monoidal.μ_δ_assoc, whisker_exchange_assoc, ← comp_whiskerRight_assoc,
        Iso.map_inv_hom_id, Category.comp_id, ← whisker_exchange_assoc,
        Functor.LaxMonoidal.μ_whiskerRight_comp_μ_assoc, Iso.map_inv_hom_id_assoc,
        Functor.Monoidal.μ_δ_assoc, normalization_of, associator_naturality_right_assoc,
        Iso.inv_hom_id_assoc]
      simp only [← Category.assoc, cancel_mono]; simp only [Category.assoc]
      -- and now it’s all strict morphisms so we can just rip it apart.
      simp [show (λ_ _) = SList.leftUnitor _ by rfl,
        show (α_ _ _ _) = SList.associator _ _ _ by rfl,
        SList.leftUnitor, tensorObjConsIso, appendNilIso, unitIsoNil, SList.associator, eqToHom_map]

instance : (unitIso C).inv.IsMonoidal := by infer_instance

/-- The natural isomorphism `ε : K ⋙ J ≅ 𝟭` on `FreeSMC C`:
it is defined via the universal property of the free symmetric monoidal category,
as both sides are monoidal. -/
public def counitIso : normalization C ⋙ J C ≅ 𝟭 (FreeSymmetricMonoidalCategory C) :=
  FreeSymmetricMonoidalCategory.liftNatIso fun c ↦
    JObjConsIso c _ ≪≫ whiskerLeftIso (of c) JObjNilIso ≪≫ ρ_ _

@[simp, reassoc]
lemma counitIso_hom_app_unit :
    (counitIso C).hom.app (𝟙_ (FreeSymmetricMonoidalCategory C)) =
      (J C).map (Functor.OplaxMonoidal.η (normalization C)) ≫ Functor.OplaxMonoidal.η (J C) := by
  simp [counitIso]

@[simp, reassoc]
lemma counitIso_inv_app_unit :
    (counitIso C).inv.app (𝟙_ (FreeSymmetricMonoidalCategory C)) =
      Functor.LaxMonoidal.ε (J C) ≫ (J C).map (Functor.LaxMonoidal.ε (normalization C)) := by
  simp [counitIso]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma counitIso_hom_app_of (c : C) :
    (counitIso C).hom.app (of c) =
    (JObjConsIso c _).hom ≫ (of c) ◁ JObjNilIso.hom ≫ (ρ_ _).hom := by
  simp [counitIso]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma counitIso_inv_app_of (c : C) :
    (counitIso C).inv.app (of c) =
    (ρ_ _).inv ≫ (of c) ◁ JObjNilIso.inv ≫ (JObjConsIso c _).inv := by
  simp [counitIso]

@[simp, reassoc]
lemma counitIso_hom_app_tensor (x y : FreeSymmetricMonoidalCategory C) :
    (counitIso C).hom.app (x ⊗ y) =
    (J C).map (Functor.OplaxMonoidal.δ (normalization C) x y) ≫
    Functor.OplaxMonoidal.δ (J C) ((normalization C).obj x) ((normalization C).obj y) ≫
      (((counitIso C).hom.app x) ⊗ₘ ((counitIso C).hom.app y)) := by
    simp [counitIso]

@[simp, reassoc]
lemma counitIso_inv_app_tensor (x y : FreeSymmetricMonoidalCategory C) :
    (counitIso C).inv.app (x ⊗ y) =
    (((counitIso C).inv.app x) ⊗ₘ ((counitIso C).inv.app y)) ≫
      Functor.LaxMonoidal.μ (J C) ((normalization C).obj x) ((normalization C).obj y) ≫
        (J C).map (Functor.LaxMonoidal.μ (normalization C) x y) := by
  simp [counitIso]

instance : (counitIso C).hom.IsMonoidal where
instance : (counitIso C).inv.IsMonoidal where

section

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
variable {F : C ⥤ D} {G : D ⥤ C} [Functor.LaxMonoidal F] [Functor.LaxMonoidal G]
  (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) [η.hom.IsMonoidal] [ε.hom.IsMonoidal]

instance : (Equivalence.adjointifyη η ε).hom.IsMonoidal := by
  dsimp [Equivalence.adjointifyη]
  infer_instance

end

set_option backward.isDefEq.respectTransparency false in
/-- The coherence theorem: `SList C` is equivalent to `FreeSymmetricMonoidalCategory C`
as a symmetric monoidal category. -/
@[simps, expose]
public def equivalence : SList C ≌ FreeSymmetricMonoidalCategory C where
  functor := J C
  inverse := normalization C
  unitIso := unitIso C
  counitIso := counitIso C
  functor_unitIso_comp x := by
    /- Instead of computing, we’ll use a trick here:
    adjointifying the not-yet-half-adjoint equivalence will give an half-adjoint equivalence with
    the correct unit, but potentially not the correct counit. But the adjointification process
    preserves monoidal natural transformations, so in that adjointified equivalence,
    the counit will be monoidal.
    But then the counit is uniquely determined by its components on elements from `C`,
    and by fully faithfulness of `normalization C` (which we can know without knowing adjointness)
    these elements have no automorphisms in the free symmetric monoidal category, so
    this adjointified counit is the same as ours. -/
    let E₀ := Equivalence.mk (normalization C) (J C) (counitIso C).symm (unitIso C).symm
    letI : (E₀.symm.inverse ⋙ E₀.symm.functor).LaxMonoidal := by
      dsimp [E₀, Equivalence.mk]; infer_instance
    have E₀_unit : E₀.symm.unitIso = unitIso C := rfl
    haveI : (unitIso C).symm.hom.IsMonoidal := by dsimp; infer_instance
    haveI : (counitIso C).symm.hom.IsMonoidal := by dsimp; infer_instance
    have : E₀.symm.counitIso.hom.IsMonoidal :=
      inferInstanceAs (Equivalence.adjointifyη _ _).inv.IsMonoidal
    suffices H : E₀.symm.counitIso = counitIso C by
      rw [← H]
      exact E₀.symm.functor_unitIso_comp x
    ext : 1
    dsimp [E₀, Equivalence.mk]
    apply FreeSymmetricMonoidalCategory.ext_of_monoidal
    intro x
    dsimp
    suffices H' : ∀ (y : FreeSymmetricMonoidalCategory C), Subsingleton (y ⟶ .of x) by
      subsingleton
    suffices H₀ : Linear ((normalization C).obj (.of x)) by
      intro y
      let : (normalization C).FullyFaithful := E₀.symm.fullyFaithfulInverse
      rw [Equiv.subsingleton_congr this.homEquiv]
      infer_instance
    rw [normalization_of]
    infer_instance

public instance : (equivalence C).functor.Monoidal := inferInstanceAs (J C).Monoidal
public instance : (equivalence C).functor.Braided := inferInstanceAs (J C).Braided
public instance : (equivalence C).inverse.Monoidal := inferInstanceAs (normalization C).Monoidal
public instance : (equivalence C).inverse.Braided := inferInstanceAs (normalization C).Braided

set_option backward.isDefEq.respectTransparency false in
/-- TODO: this should be generalized -/
public instance : (equivalence C).IsMonoidal where
  leftAdjoint_ε := by
    dsimp [equivalence]
    have := NatTrans.IsMonoidal.unit (τ := (unitIso C).hom)
    simp at this
    simp [this]
  leftAdjoint_μ x y := by
    dsimp [equivalence]
    have u₁ := NatTrans.IsMonoidal.tensor (τ := (unitIso C).hom) ((normalization C).obj x)
      (normalization C |>.obj y)
    have u₂ := NatTrans.IsMonoidal.tensor (τ := (counitIso C).hom) x y
    simp only [Functor.id_obj, Functor.comp_obj, Functor.LaxMonoidal.id_μ, Category.id_comp,
      Functor.LaxMonoidal.comp_μ] at u₁
    dsimp at u₂
    simp only [Category.assoc, Category.comp_id] at u₂
    simp only [← u₂, Functor.Monoidal.δ_μ_assoc, u₁, Category.assoc]
    have := (equivalence C).unit_app_inverse
    dsimp [equivalence] at this
    simp_rw [this, Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp]
    simp

public instance : (equivalence C).unit.IsMonoidal := inferInstance
public instance : (equivalence C).unitInv.IsMonoidal := inferInstance
public instance : (equivalence C).counit.IsMonoidal := inferInstance
public instance : (equivalence C).counitInv.IsMonoidal := inferInstance

end Equivalence

section UniversalProperty

/-! ## (Symmetric monoidal) universal property of symmetric lists
In this section, we transfer the universal property of FreeSymmetricMonoidalCategory to
symmetric lists. -/

variable {C} {D : Type*} [Category* D] [MonoidalCategory D] [SymmetricCategory D]

/-- The (symmetric monoidal) functor `SList C ⥤ D` induced by a function C → D when
`D` is a symmetric monoidal category. -/
@[expose] public def monoidalLift (p : C → D) : SList C ⥤ D :=
  (equivalence C).functor ⋙ FreeSymmetricMonoidalCategory.project p

public instance (p : C → D) : (monoidalLift p).Monoidal :=
    inferInstanceAs ((equivalence C).functor ⋙ FreeSymmetricMonoidalCategory.project p).Monoidal

public instance (p : C → D) : (monoidalLift p).Braided :=
    inferInstanceAs ((equivalence C).functor ⋙ FreeSymmetricMonoidalCategory.project p).Braided

@[expose] public def monoidalLiftConsNilIso (p : C → D) (c : C) :
    (monoidalLift p).obj [c]~ ≅ p c :=
  (project p).mapIso (JObjConsIso c []~) ≪≫
  (Functor.Monoidal.μIso (project p) _ _).symm ≪≫
    whiskerLeftIso _ ((project p).mapIso JObjNilIso) ≪≫
    whiskerLeftIso _ (Functor.Monoidal.εIso _).symm ≪≫ ρ_ _

/-- Given two symmetric monoidal functors `F G : SList C ⥤ D`, a family of morphisms
`F.obj [c]~ → G.obj [c]~` determines a monoidal natural transformation from `F` to `G`. -/
@[expose] public def monoidalLiftNatTrans
    {F G : SList C ⥤ D} [F.Braided] [G.LaxBraided]
    (φ : ∀ (c : C), F.obj [c]~ ⟶ G.obj [c]~) :
    F ⟶ G :=
  letI F' : FreeSymmetricMonoidalCategory C ⥤ D := (equivalence C).inverse ⋙ F
  letI G' : FreeSymmetricMonoidalCategory C ⥤ D := (equivalence C).inverse ⋙ G
  letI φ' : ∀ (c : C), F'.obj (of c) ⟶ G'.obj (of c) := φ
  letI α₀ : F' ⟶ G' := FreeSymmetricMonoidalCategory.liftNatTrans φ'
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (equivalence C).unit _ ≫
    (Functor.associator ..).hom ≫
    Functor.whiskerLeft (equivalence C).functor α₀ ≫
    (Functor.associator ..).inv ≫
    Functor.whiskerRight (equivalence C).unitInv _ ≫
    (Functor.leftUnitor _).hom

public section

-- TODO: upstream this in mathlib
variable {C : Type*} [Category* C] [MonoidalCategory C]
  {D : Type*} [Category* D] [MonoidalCategory D]
  {E : Type*} [Category* E] [MonoidalCategory E]
  {E' : Type*} [Category* E'] [MonoidalCategory E']

variable {F₁ F₂ F₃ : C ⥤ D} (τ : F₁ ⟶ F₂) [F₁.LaxMonoidal] [F₂.LaxMonoidal] [F₃.LaxMonoidal]

open NatTrans
instance {G₁ : D ⥤ E} [G₁.LaxMonoidal] [IsMonoidal τ] :
    IsMonoidal (Functor.whiskerRight τ G₁) := by
  rw [← Functor.hcomp_id]
  infer_instance

instance {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal]
    (τ' : G₁ ⟶ G₂) [IsMonoidal τ'] :
    IsMonoidal (Functor.whiskerLeft F₁ τ') := by
  rw [← Functor.id_hcomp]
  infer_instance

end

set_option backward.isDefEq.respectTransparency false in
public instance {F G : SList C ⥤ D} [F.Braided] [G.LaxBraided]
    (φ : ∀ (c : C), F.obj [c]~ ⟶ G.obj [c]~) : (monoidalLiftNatTrans φ).IsMonoidal := by
  dsimp [monoidalLiftNatTrans]
  -- The composition is a bit too big, so we have to provide an intermediate instance
  letI F' : FreeSymmetricMonoidalCategory C ⥤ D := (equivalence C).inverse ⋙ F
  letI G' : FreeSymmetricMonoidalCategory C ⥤ D := (equivalence C).inverse ⋙ G
  letI φ' : ∀ (c : C), F'.obj (of c) ⟶ G'.obj (of c) := φ
  letI α₀ : F' ⟶ G' := FreeSymmetricMonoidalCategory.liftNatTrans φ'
  haveI : NatTrans.IsMonoidal
    ((J C).whiskerLeft (FreeSymmetricMonoidalCategory.liftNatTrans φ') ≫
          ((J C).associator (normalization C) G).inv ≫
            Functor.whiskerRight (equivalence C).unitInv G ≫ G.leftUnitor.hom) :=
    inferInstance
  infer_instance

public section

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma monoidalLiftNatTrans_app_singleton
    {F G : SList C ⥤ D} [F.Braided] [G.LaxBraided] (φ : ∀ (c : C), F.obj [c]~ ⟶ G.obj [c]~)
    (c : C) :
    (monoidalLiftNatTrans φ).app [c]~ = φ c := by
  letI F' : FreeSymmetricMonoidalCategory C ⥤ D := (equivalence C).inverse ⋙ F
  letI G' : FreeSymmetricMonoidalCategory C ⥤ D := (equivalence C).inverse ⋙ G
  letI φ' : ∀ (c : C), F'.obj (of c) ⟶ G'.obj (of c) := φ
  letI α₀ : F' ⟶ G' := FreeSymmetricMonoidalCategory.liftNatTrans φ'
  simp only [monoidalLiftNatTrans, equivalence_functor, equivalence_inverse, NatTrans.comp_app,
    Functor.comp_obj, Functor.id_obj, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp]
  change F.map ((equivalence C).unit.app [c]~) ≫
    α₀.app ((J C).obj [c]~) ≫ G.map ((equivalence C).unitInv.app [c]~) = φ c
  let nat₁ := α₀.naturality (JObjConsIso c []~ ≪≫ whiskerLeftIso (of c) JObjNilIso ≪≫ ρ_ _).hom
  simp [-NatTrans.naturality, G', F'] at nat₁
  have := (equivalence C).unitInv_app_inverse ((of c))
  dsimp [normalization_of] at this
  rw [this]
  dsimp [equivalence]
  rw [unitIso_hom_app_singleton]
  simp only [Functor.map_comp, normalization_of, equivalence_inverse, counitIso_hom_app_of, ← nat₁,
    liftNatTrans_app_of, Category.assoc, F', α₀, φ']
  simp [← Functor.map_comp, ← Functor.map_comp_assoc, normalization_of]

lemma monoidalNatTrans_ext_app_singleton
    {F G : SList C ⥤ D} [F.Braided] [G.LaxBraided]
    {α β : F ⟶ G} [α.IsMonoidal] [β.IsMonoidal]
    (h : ∀ c : C, α.app [c]~ = β.app [c]~) : α = β := by
  apply (Functor.whiskeringLeft .. |>.obj ((equivalence C).inverse)).map_injective
  dsimp
  apply FreeSymmetricMonoidalCategory.ext_of_monoidal
  exact h

lemma monoidalLiftNatTrans_comp {F G H : SList C ⥤ D} [F.Braided] [G.Braided] [H.LaxBraided]
    (φ : ∀ (c : C), F.obj [c]~ ⟶ G.obj [c]~)
    (ψ : ∀ c : C, G.obj [c]~ ⟶ H.obj [c]~) :
    monoidalLiftNatTrans φ ≫ monoidalLiftNatTrans ψ =
    monoidalLiftNatTrans (fun c ↦ φ c ≫ ψ c) := by
  apply monoidalNatTrans_ext_app_singleton
  intro c
  simp

@[expose, simps] public def monoidalLiftNatIso
    {F G : SList C ⥤ D} [F.Braided] [G.Braided]
    (φ : ∀ (c : C), F.obj [c]~ ≅ G.obj [c]~) :
    F ≅ G where
  hom := monoidalLiftNatTrans fun c ↦ (φ c).hom
  inv := monoidalLiftNatTrans fun c ↦ (φ c).inv
  hom_inv_id := by
    apply monoidalNatTrans_ext_app_singleton
    simp
  inv_hom_id := by
    apply monoidalNatTrans_ext_app_singleton
    simp

public instance {F G : SList C ⥤ D} [F.Braided] [G.Braided]
    (φ : ∀ (c : C), F.obj [c]~ ≅ G.obj [c]~) : (monoidalLiftNatIso φ).hom.IsMonoidal :=
  inferInstanceAs <| NatTrans.IsMonoidal <| monoidalLiftNatTrans ..

end

end UniversalProperty

end CategoryTheory.SList
