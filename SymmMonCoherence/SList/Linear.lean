/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.Equivalence
public import Mathlib.CategoryTheory.Pi.Monoidal
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-! # Linear symmetric lists.

In this file, we define linear symmetric lists as those for which
the underlying list has no duplicates.

We then prove that the type of (iso)-morphisms to and from a linear
symmetric list is a subsingleton. This recovers one of the "classical"
forms of the coherence theorem for symmetric monoidal categories that
states that "all diagrams commute as long as there are no
duplicate variables".
-/

universe u

@[expose] public section

namespace CategoryTheory.SList
open MonoidalCategory

variable {C : Type*}

@[mk_iff]
class Linear (L : SList C) where
  nodup : L.toList.Nodup

instance : ([]~ : SList C).Linear where nodup := by simp

instance (x : C) : (x::~[]~ : SList C).Linear where nodup := by simp

lemma linear_cons_of_not_mem (c : C) (x : SList C) (h : c ∉ x.toList) [l : Linear x] :
    Linear (c ::~ x) where
  nodup := by
    simp only [cons_toList, List.nodup_cons]
    exact ⟨h, l.nodup⟩

instance subsingleton_hom_of_linear_left (L L' : SList C) [h₀ : Linear L] :
    Subsingleton (L ⟶ L') where
  allEq f g := by
    classical
    rw [SList.hom_eq_iff_toPerm_eq]
    ext i : 1
    by_cases! hi : i < L.length
    · have hi' : i < L'.length := by rwa [← length_eq_of_hom f]
      have (f : L ⟶ L') : (toPerm.app f) i = L.toList.idxOf (L'.toList[i]) := by
        have := List.Nodup.idxOf_getElem h₀.nodup
        obtain ⟨i, rfl⟩ := (toPerm.app (inv f)).surjective i
        conv_lhs => rw [weight.app_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
        rw [getElem_toList_toPerm f]
        simp [this]
      simp [this]
    · rw [length_eq_of_hom f] at hi
      simp [toPerm_app_eq_of_lt _ i hi]

instance subsingleton_iso_of_linear_left (L L' : SList C) [Linear L] : Subsingleton (L ≅ L') :=
  letI : Groupoid (SList C) := Groupoid.ofIsIso (fun _ ↦ by infer_instance)
  Equiv.subsingleton (Groupoid.isoEquivHom L L')

instance subsingleton_iso_of_linear_right (L L' : SList C) [Linear L'] :
    Subsingleton (L ≅ L') :=
  Equiv.subsingleton (Equiv.ofBijective _ <| Iso.symm_bijective (X := L) (Y := L'))

instance subsingleton_hom_of_linear_right (L L' : SList C) [Linear L'] :
    Subsingleton (L ⟶ L') :=
  letI : Groupoid (SList C) := Groupoid.ofIsIso (fun _ ↦ by infer_instance)
  Equiv.subsingleton (Groupoid.isoEquivHom L L').symm


end CategoryTheory.SList
