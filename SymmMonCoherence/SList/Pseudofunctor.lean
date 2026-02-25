/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.Basic
public import SymmMonCoherence.SList.Equivalence

/-!
# Symmetric lists as a pseudofunctor

-/

@[expose] public section

namespace CategoryTheory.SList

/-- The action of a map of types on symmetric lists.
It is determined by the formulas
`mapFn.obj []~ ≅ []~`
and
`mapFn.obj (x ::~ l) ≅ (f x) ::~ ((mapFn f).obj l)`
-/
def mapFn {K L : Type*} (f : K → L) : SList K ⥤ SList L :=
  monoidalLift fun k ↦ f k ::~ []~
  deriving Functor.Braided

def mapFnSingletonIso {K L : Type*} (f : K → L) (k : K) :
    (mapFn f).obj (k ::~ []~) ≅ (f k ::~ []~) :=
  monoidalLiftConsNilIso _ _

-- lemma mapFn_nil {K L : Type*} (f : K → L) : (mapFn f).obj []~ = []~ :=
--   RecursiveFunctorData.functor_obj_nil _
--
-- lemma mapFn_cons {K L : Type*} (f : K → L) (k : K) (l : SList K) :
--     (mapFn f).obj (k ::~ l) = (f k) ::~ ((mapFn f).obj l) :=
--   RecursiveFunctorData.functor_obj_cons _ _ _
--
-- @[expose] def mapFnNilIso {K L : Type*} (f : K → L) : (mapFn f).obj []~ ≅ []~ :=
--   eqToIso <| mapFn_nil f
--
-- @[expose] def mapFnConsIso {K L : Type*} (f : K → L) : (mapFn f).obj []~ ≅ []~ :=
--   eqToIso <| mapFn_nil f

end CategoryTheory.SList
