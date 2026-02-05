/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.EffBurnside
public import SymmMonCoherence.ForMathlib.CategoryTheory.Pi.CompMonoidal
public import SymmMonCoherence.ForMathlib.CategoryTheory.Pi.FlipMonoidal
public import SymmMonCoherence.SList.Additive

universe u

/-! Duality for symmetric lists. -/
@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.SList

variable (J K : Type u)

/-- Duality for symmetric lists. -/
noncomputable def duality [Finite J] : (J → SList K) ⥤ (K → SList J) :=
  Pi.postcompFunctor J (fib₁ K) ⋙ Pi.flipFunctor _ _ _ ⋙ Pi.postcompFunctor K (fib₁ J).inv
  deriving Functor.Braided

/- Computing the underlying multisets of the dual -/
open scoped Classical in
lemma duality_obj_multiset [Fintype J] (X : J → SList K) (k : K) :
    ((duality J K).obj X k).multiset =
    ∑ j : J, .replicate ((X j).multiset.count k) j := by
  dsimp [duality]
  ext i
  simp only [fib₁_inv_multiset_count, Pi.flipFunctor_obj, Pi.postcompFunctor_obj,
    Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  have := fiber_card k (X i)
  rw [Fintype.card_eq_nat_card] at this
  simp only [fib₁, fib₀, eval₀, Functor.comp_obj, Functor.pi_obj, Functor.pi'_obj, Fin.getElem_fin,
    ofFintype_length]
  rw [Fintype.card_eq_nat_card, this]
  simp [multiset]

end CategoryTheory.SList
