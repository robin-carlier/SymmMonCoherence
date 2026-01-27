/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.Equivalence
public import SymmMonCoherence.SList.Linear
public import Mathlib.CategoryTheory.Pi.Monoidal
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-! # The multiset of a symmetric list.

Given a symmetric list `L`, we define its underlying multiset.

-/

universe u

@[expose] public section

namespace CategoryTheory.SList
open MonoidalCategory

variable {C : Type*}
def multiset (L : SList C) : Multiset C := Multiset.ofList L.toList

@[grind =]
lemma multiset_nil : ([]~ : SList C).multiset = 0 := by simp [multiset]

@[grind =]
lemma multiset_cons (x : C) (L : SList C) : (x ::~ L).multiset = x::ₘ L.multiset := by
  simp [multiset]

@[simp, grind =]
lemma multiset_singleton (x : C) : ([x]~).multiset = {x} := by
  simp [multiset]

lemma multiset_eq_of_hom {L L' : SList C} (f : L ⟶ L') : L.multiset = L'.multiset := by
  induction f using SList.hom_induction' with
  | comp f g _ _ => grind
  | id x => grind
  | cons head f _ => grind
  | swap x y l =>
    simpa [multiset] using .swap ..

@[grind =]
lemma multiset_tensor (L L' : SList C) : (L ⊗ L').multiset = L.multiset + L'.multiset := by
  induction L using SList.cons_induction with simp [multiset, SList.tensorObj_toList]

@[grind =]
lemma multiset_eq_iff_nonempty_iso (L L' : SList C) :
    L.multiset = L'.multiset ↔ Nonempty (L ≅ L') where
  mp h := by
    simp only [multiset, Multiset.coe_eq_coe] at h
    exact SList.toList_perm_iff_nonempty_iso.mp h
  mpr h := multiset_eq_of_hom h.some.hom

@[grind →]
lemma nodup_of_linear (L : SList C) [Linear L] :
    L.multiset.Nodup := by
  simp only [multiset, Multiset.coe_nodup]
  exact Linear.nodup

lemma linear_iff' (L : SList C) :
    L.Linear ↔ L.multiset.Nodup := by
  simp only [multiset, Multiset.coe_nodup, SList.linear_iff]

/-- A choice of an isomorphism between two symmetric lists with same underlying multiset.
In general, this isomorphism is not unique, but it is if either list is linear. -/
@[no_expose] noncomputable def isoOfMultisetEq (L L' : SList C) (h : L.multiset = L'.multiset) :
    L ≅ L' :=
  (multiset_eq_iff_nonempty_iso ..|>.mp h).some

end CategoryTheory.SList
