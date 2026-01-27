/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Pi.Monoidal
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-! # Flipping variable as a monoidal functor. -/

universe w₁ v₁ u₁
@[expose] public section

namespace CategoryTheory.Pi

variable (C : Type u₁) [Category.{v₁} C]

/- The function version of Functor.whiskeringLeft. -/
@[simps!]
def precompFunctor {I J : Type*} (f : I → J) : (J → C) ⥤ (I → C) where
  obj X := fun j ↦ X (f j)
  map φ := fun j ↦ φ (f j)

/- The mixed function version of Functor.whiskeringLeft. -/
@[simps!]
def precompFunctor' {I J : Type*} [Category* J] (f : I → J) : (J ⥤ C) ⥤ (I → C) :=
  Functor.pi' (fun x ↦ (evaluation _ _).obj (f x))

/- The mixed function version of Functor.whiskeringLeft. -/
@[simps]
abbrev precomposingFunctor (I J : Type*) [Category* J] : (I → J) ⥤ (J ⥤ C) ⥤ (I → C) where
  obj f := precompFunctor' C f
  map φ := NatTrans.pi' (fun x ↦ (evaluation _ _).map (φ x))

@[simps!]
instance precompFunctorMonoidal {I J : Type*} (f : I → J) [MonoidalCategory C] :
    Functor.Monoidal (precompFunctor C f) :=
  letI : Functor.CoreMonoidal (precompFunctor C f) :=
    { εIso := .refl _
      μIso X Y := .refl _  }
  this.toMonoidal

instance {I J : Type*} (f : I → J) [MonoidalCategory C] [BraidedCategory C] :
    Functor.Braided (precompFunctor C f) where
  braided X Y := by ext i; simp

@[simps!]
instance precompFunctor'Monoidal {I J : Type*} [Category* J] (f : I → J) [MonoidalCategory C] :
    Functor.Monoidal (precompFunctor' C f) :=
  letI : Functor.CoreMonoidal (precompFunctor' C f) :=
    { εIso := .refl _
      μIso X Y := .refl _  }
  this.toMonoidal

instance {I J : Type*} [Category* J] (f : I → J) [MonoidalCategory C] [BraidedCategory C] :
    Functor.Braided (precompFunctor' C f) where
  braided X Y := by ext i; simp [BraidedCategory.braiding]

/- The mixed function version of Functor.whiskeringLeft. -/
@[simps!]
def precompFunctor'AssocIso {I J K : Type*} [Category* J] [Category* K]
    (f : I → J) (g : J ⥤ K) (h : K ⥤ C) :
    (precompFunctor' _ f).obj (g ⋙ h) ≅ (precompFunctor' _ ((precompFunctor' _ f).obj g)).obj h :=
  .refl _

/- The mixed function version of Functor.whiskeringLeft. -/
@[simps!]
def precompFunctor'Id {I J : Type*} [Category* J] (f : I → J) :
    (precompFunctor' _ f).obj (𝟭 _) ≅ f :=
  .refl _

instance {I J : Type*} [Category* J] {f g : I → J} (φ : f ⟶ g)
    [MonoidalCategory C] [BraidedCategory C] :
    ((precomposingFunctor C I J).map φ).IsMonoidal where
  unit := by
    ext
    simp
  tensor X Y := by
    ext
    simp

variable {C}

/- The function version of Functor.whiskeringRight. -/
@[simps!]
def postcompFunctor {D : Type*} [Category* D] (I : Type*) (F : C ⥤ D) : (I → C) ⥤ (I → D) :=
  Functor.pi fun _ ↦ F

@[simps!]
instance postcompFunctorMonoidal {D : Type*} [Category* D] {I : Type*}
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] :
    (postcompFunctor I F).Monoidal := by
  dsimp [postcompFunctor]
  infer_instance

instance {D : Type*} [Category* D] {I : Type*}
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.Braided] :
    (postcompFunctor I F).Braided where
  braided X Y := by ext i; simp

end CategoryTheory.Pi
