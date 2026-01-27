/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Categories of symmetric monoidal functors, and their symmetric monoidal structure

In this file, we construct a bundled structure `SymmMonFunctor` for
braided monoidal functors between two braided monoidal categories and make
it a category with monoidal natural transformations as morphisms.
We show that this category is also braided monoidal for the pointwise monoidal structure.

The API here is kept minimal: the main use of this object should be that it helps
to have a bundled version to ensure that certain constructions done via universal
properties remain symmetric monoidal.
-/

@[expose] public section

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory
open MonoidalCategory


#exit


variable (C) (D) in
structure BraidedMonFunctor where
  functor : C ⥤ D
  [braided : functor.Braided]

attribute [instance] BraidedMonFunctor.braided

namespace BraidedMonFunctor

structure Hom (F G : BraidedMonFunctor C D) where
  as : F.functor ⟶ G.functor
  [IsMonoidal : NatTrans.IsMonoidal as]

attribute [instance] Hom.IsMonoidal

@[simps!]
instance : Category (BraidedMonFunctor C D) where
  Hom := Hom
  id F := Hom.mk (𝟙 _)
  comp α β := Hom.mk (α.as ≫ β.as)

variable (C) (D) in
@[simps]
def forget : (BraidedMonFunctor C D) ⥤ (C ⥤ D) where
  obj X := X.functor
  map f := f.as

@[simps!]
def homMk {F G : C ⥤ D} [F.Braided] [G.Braided] (α : F ⟶ G) [α.IsMonoidal] :
    (BraidedMonFunctor.mk F) ⟶ (BraidedMonFunctor.mk G) := .mk α

instance : MonoidalCategoryStruct (BraidedMonFunctor C D) where
  tensorObj F G := .mk (F.functor ⊗ G.functor)

/- We now show that the category is itself symmetric monoidal -/
def inducing : Monoidal.InducingFunctorData (forget C D) where

end BraidedMonFunctor

end CategoryTheory
