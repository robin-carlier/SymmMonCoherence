/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.Kleisli
public import SymmMonCoherence.SList.ToPseudofunctor.Defs
public import SymmMonCoherence.SList.ToPseudofunctor.LaxNatTrans
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax

/-! # Unbiasing of strong symmetric monoidal functors.

In this file, we show that if `F : C ⥤ D` is a braided monoidal
functor of symmetric monoidal categories, `F` defines a strong natural
transformation of the pseudofunctors from the Kleisli bicategory induced by the
source and target symmetric monoidal categories.

We give this as a `Oplax.LaxTrans.StrongCore` on the transformation underlying
-/

@[expose] public section


namespace CategoryTheory.SList

namespace Kleisli

section

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
  (F : C ⥤ D) [F.Braided]

/-- A natural isomorphism filling in the square
```
(K → C) ---> (SList K ⥤ C)
   |              |
   | F_*   ⇙      | F_*
   v              v
(K → D) ---> (SList K ⥤ D)
```
This is a `K`-ary version of `Functor.Monoidal.μIso`. -/
def generalizedμIso (K : Type*) :
    (Pi.postcompFunctor _ F) ⋙ SList.monoidalLiftFunctor K D ≅
    (SList.monoidalLiftFunctor K C) ⋙ (Functor.whiskeringRight _ _ _|>.obj F) :=
  NatIso.ofComponents (fun X ↦
    (SList.monoidalLiftNatIso (fun c ↦
      (SList.monoidalLiftConsNilIso ..) ≪≫ F.mapIso ((SList.monoidalLiftConsNilIso ..).symm)) :
      SList.monoidalLift ((Pi.postcompFunctor K F).obj X) ≅ SList.monoidalLift X ⋙ F))
    (fun {X Y} f => by
      dsimp
      apply SList.monoidalNatTrans_ext_app_singleton
      intro c
      simp)

section

end

instance (K : Type*) (X : K → C) :
    (((Pi.postcompFunctor _ F) ⋙ SList.monoidalLiftFunctor K D).obj X).LaxMonoidal :=
  inferInstanceAs (SList.monoidalLift (Pi.postcompFunctor _ F |>.obj X)).LaxMonoidal

instance (K : Type*) (X : K → C) :
    ((SList.monoidalLiftFunctor K C) ⋙
      (Functor.whiskeringRight _ _ _|>.obj F)|>.obj X).LaxMonoidal :=
  inferInstanceAs (monoidalLift X ⋙ F).LaxMonoidal

instance (K : Type*) (X : K → C) : ((generalizedμ F K).app X).IsMonoidal := by
  dsimp [generalizedμ]
  infer_instance

end

section

universe v u

/-- A braided monoidal functor between monoidal categories interprets as a strong natural
transformation between the pseudofunctors out of the Kleisli bicategory classifying the source and
target monoidal categories. -/
@[simps!]
def strongTransOfLaxBraided {C D : Type u} [Category.{v} C] [Category.{v} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [SymmetricCategory C] [SymmetricCategory D]
    (F : C ⥤ D) [F.Braided] :
    Lax.StrongTrans
      (SList.Kleisli.pseudoOfSymmMonCat C).toLax
      (SList.Kleisli.pseudoOfSymmMonCat D).toLax :=
  letI : Lax.LaxTrans.StrongCore (natTransOfLaxBraided F) := {
    naturality _ := Cat.Hom.isoMk <|
      (Functor.associator _ _ _).symm ≪≫ (Functor.isoWhiskerRight (generalizedμIso _ _) _)
    naturality_hom _ := rfl }
  Lax.StrongTrans.mkOfLax _ this

end

end Kleisli

end CategoryTheory.SList

