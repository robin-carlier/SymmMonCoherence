/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.Duality
public import SymmMonCoherence.SList.Kleisli
public import SymmMonCoherence.Spans.PseudoFromBurnside.Pseudofunctor
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Spans of finite types and the Kleisli bicateory of
symmetric lists.

In this file, we use the results from the file
`SymmMonCoherence.Spans.PseudoFromBurnside.Pseudofunctor` to construct a pseudofunctor
from `Bursnide (FintypeCat)` to the bicategory `SList.Kleisli`.-/
universe u

@[expose] public section

namespace CategoryTheory.SList.EffBurnside

/-- An auxiliary construction for computing the monoidal pushforwards.
given `f : J → K`, this is the family `K → SList J` that sends `k` to a
symmetric list corresponding to the fibers `f ''⁻¹ {k}`. -/
noncomputable def pushforwardAux {J K : Type u} [Finite J] (f : J → K) :
    K → SList J :=
  (SList.duality.{u} _ _).obj ([f ·]~)

/- The values of pushforwards are only composed of linear symmetric lists.
In particular, there is at most one isomorphism between two of these. -/
instance {J K : Type u} [Finite J] (f : J → K) (k : K) : Linear (pushforwardAux f k) := by
  dsimp [pushforwardAux]
  classical
  letI : Fintype J := .ofFinite _
  rw [SList.linear_iff', duality_obj_multiset]
  simp only [multiset, cons_toList, nil_toList, Multiset.coe_singleton,
    Multiset.count_singleton]
  rw [Multiset.nodup_iff_count_le_one]
  intro j
  simp only [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  grind

open MonoidalCategory in
lemma monoidalLift_multiset {J K : Type*} (f : J → SList K) (L : SList J) :
    ((monoidalLift f).obj L).multiset =
    ((L.multiset.map f).map (·.multiset)).sum := by
  induction L using SList.cons_induction with
  | nil =>
    simp only [Multiset.map_map, Function.comp_apply]
    let e : (monoidalLift f).obj []~ ≅ 𝟙_ _ :=
      (monoidalLift f).mapIso unitIsoNil.symm ≪≫ (Functor.Monoidal.εIso _).symm
    rw [multiset_eq_of_hom e.hom]
    simp [multiset]
  | cons x L ih =>
    simp only [Multiset.map_map, Function.comp_apply]
    let e : (monoidalLift f).obj (x ::~ L) ≅ f x ⊗ (monoidalLift f).obj L :=
      (monoidalLift f).mapIso (consTensSingletonIso _ _) ≪≫
        (Functor.Monoidal.μIso _ _ _).symm ≪≫ whiskerRightIso (monoidalLiftConsNilIso ..) _
    rw [multiset_eq_of_hom e.hom]
    simp only [multiset_tensor, ih, Multiset.map_map, Function.comp_apply]
    simp [multiset]

lemma linearOfIsPullback {X Y Z T : FintypeCat} {u : X ⟶ Y} {v : X ⟶ Z} {f : Y ⟶ T} {g : Z ⟶ T}
    (S : IsPullback u v f g) (z : Z) :
    ((monoidalLift (pushforwardAux f)).obj
      (RelativePseudomonad.ι T.carrier (g z))).Linear := by
  classical
  rw [SList.linear_iff', Multiset.nodup_iff_count_eq_one]
  intro y hy
  simp only [pushforwardAux, monoidalLift_multiset, multiset_singleton, Multiset.map_singleton,
    duality_obj_multiset, Multiset.count_singleton,
    Multiset.sum_singleton, Multiset.mem_sum, Finset.mem_univ, true_and] at hy ⊢
  simp only [Multiset.mem_replicate, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    Decidable.not_not, exists_eq_right'] at hy
  obtain ⟨h₁, h₂, h₃⟩ := Limits.Types.isPullback_iff _ _ _ _|>.mp (S.map FintypeCat.incl)
  obtain ⟨x, hx₁, hx₂⟩ := h₃ _ _ hy.symm
  simp only [FintypeCat.incl_obj, FintypeCat.incl_map, FintypeCat.hom_apply] at hx₁ hx₂
  simp only [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
  grind

noncomputable def pseudoFunctorCore : EffBurnside.PseudoFunctorCore FintypeCat.{0} Kleisli.{0} where
  obj J := .mk J
  u {X Y} f := .mk <| pushforwardAux f
  v {X Y} f := .mk <| RelativePseudomonad.ι _ ∘ f
  uId' {X} f h := Kleisli.mkIso₂ <| Pi.isoMk <| fun x ↦ isoOfMultisetEq _ _ <| by
    classical
    ext t
    simp only [pushforwardAux, h, ConcreteCategory.id_apply, duality_obj_multiset,
      multiset_singleton, Multiset.count_singleton, Multiset.count_sum',
      Multiset.count_replicate, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Kleisli.id_of]
    grind
  vId' {Y} f h := Kleisli.mkIso₂ <| Pi.isoMk <| fun x ↦ eqToIso (by simp [h])
  uComp' {X Y Z} f g fg hfg := Kleisli.mkIso₂ <| Pi.isoMk <| fun x ↦ isoOfMultisetEq _ _ <| by
    classical
    ext t
    simp only [pushforwardAux, ← hfg, ConcreteCategory.comp_apply, duality_obj_multiset,
      multiset_singleton, Multiset.count_singleton, Multiset.count_sum',
      Multiset.count_replicate, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Kleisli.comp_of,
      Pi.precompFunctor'_obj, monoidalLift_multiset, Multiset.map_map, Function.comp_apply,
      Multiset.count_sum]
    rw [Multiset.sum_map_eq_nsmul_single (f t) (fun i' hi' hi'' ↦ by grind)]
    simp [Multiset.count_sum', Multiset.count_replicate]
  vComp' {X Y Z} f g fg hfg := Kleisli.mkIso₂ <| Pi.isoMk <| fun x ↦ isoOfMultisetEq _ _ <| by
    simp [monoidalLift_multiset, ← hfg]
  baseChangeIso {X Y Z T} u v f g S :=
    Kleisli.mkIso₂ <| Pi.isoMk <| fun z ↦ isoOfMultisetEq _ _ <| by
      dsimp
      classical
      ext t
      simp only [pushforwardAux, Function.comp_apply,
        monoidalLift_multiset, multiset_singleton, Multiset.map_singleton, duality_obj_multiset,
        Multiset.count_singleton, Multiset.sum_singleton,
        Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, Multiset.map_map, Multiset.count_sum]
      split_ifs with h
      · obtain ⟨h₁, h₂, h₃⟩ := Limits.Types.isPullback_iff _ _ _ _|>.mp (S.map FintypeCat.incl)
        simp only [FintypeCat.incl_obj, FintypeCat.incl_map, FintypeCat.hom_apply,
          and_imp] at h₁ h₂ h₃
        obtain ⟨ao, ha⟩ := h₃ _ _ h.symm
        letI ao₁ : t = u ao := by grind
        letI ao₂ : v ao = z := by grind
        rw [Multiset.sum_map_eq_nsmul_single (ao) (fun i' hi' hi'' ↦ by
          simp only [Multiset.mem_sum, Finset.mem_univ, true_and, ite_eq_right_iff, one_ne_zero,
            imp_false] at hi'' ⊢
          obtain ⟨j, hj⟩ := hi'' -- doable
          simp only [Multiset.mem_replicate, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
            Decidable.not_not] at hj
          obtain ⟨rfl, rfl⟩ := hj
          rintro rfl
          grind)]
        simp [ao₁, Multiset.count_sum', Multiset.count_replicate, ao₂]
      · symm
        rw [Multiset.sum_eq_zero_iff]
        intros p n
        simp only [Multiset.mem_map, Multiset.mem_sum, Finset.mem_univ, true_and] at n
        obtain ⟨a, ⟨i, hi⟩, ha'⟩ := n
        rw [Multiset.mem_replicate] at hi
        obtain ⟨hi, rfl⟩ := hi
        simp only [← ha', ite_eq_right_iff, one_ne_zero, imp_false]
        rintro rfl
        have := congr($(S.w) a)
        simp at this
        grind
  baseChange_unit_left {X Y} f := by
    ext i
    dsimp
    have : IsPullback f (𝟙 _) (𝟙 _) f := .of_vert_isIso (by simp)
    haveI := linearOfIsPullback this
    subsingleton
  baseChange_unit_right {X Y} f := by
    ext i
    dsimp
    have : IsPullback (𝟙 _) f f (𝟙 _) := .of_horiz_isIso (by simp)
    haveI :
      ((monoidalLift (pushforwardAux f)).obj
        (RelativePseudomonad.ι Y.carrier i)).Linear := linearOfIsPullback this i
    dsimp at this
    subsingleton
  baseChange_comp_horiz {x y z t m n} {f g h k u v w} S₁ S₂ := by
    ext i
    dsimp
    have := S₁.paste_horiz S₂
    haveI :
        ((monoidalLift (pushforwardAux u)).obj
        (RelativePseudomonad.ι n.carrier (w (v i)))).Linear :=
      linearOfIsPullback this i
    subsingleton
  baseChange_comp_vert {x y z t m n} {f g h k u v w} S₁ S₂ := by
    ext i
    dsimp
    have := S₁.paste_vert S₂
    haveI :
        ((monoidalLift (pushforwardAux (h ≫ w))).obj
        (RelativePseudomonad.ι n.carrier (u i))).Linear :=
      linearOfIsPullback this i
    subsingleton

open Bicategory
universe v' u' in
/-- The main result: a symmetric monoidal category can be interpreted as a pseudofunctor from
EffBurnsideFintypeCat to Cat. -/
noncomputable def pseudoOfSymmMonCat
    (C : Type u') [Category.{v'} C] [MonoidalCategory C] [SymmetricCategory C] :
    EffBurnsideFintype.{0} ⥤ᵖ Cat.{v', u'} :=
  pseudoFunctorCore.toPseudofunctor.comp (Kleisli.pseudoOfSymmMonCat C)

end CategoryTheory.SList.EffBurnside
