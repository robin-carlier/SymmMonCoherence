/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.Kleisli
public import SymmMonCoherence.SList.ToPseudofunctor.Defs
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax

/-! # Unbiasing of lax symmetric monoidal functors.

In this file, we show that if `F : C ⥤ D` is a lax braided monoidal
functor of symmetric monoidal categories, `F` defines a lax natural
transformation of the pseudofunctors from the Kleisli bicategory induced by the
source and target symmetric monoidal categories. -/

@[expose] public section


namespace CategoryTheory.SList

namespace Kleisli

section

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
  (F : C ⥤ D) [F.LaxBraided]

/-- A natural transformation filling in the square
```
(K → C) ---> (SList K ⥤ C)
   |              |
   | F_*   ⇙      | F_*
   v              v
(K → D) ---> (SList K ⥤ D)
```
This is a `K`-ary version of Functor.LaxMonoidal.μ. -/
def generalizedμ (K : Type*) :
    (Pi.postcompFunctor _ F) ⋙ SList.monoidalLiftFunctor K D ⟶
    (SList.monoidalLiftFunctor K C) ⋙ (Functor.whiskeringRight _ _ _|>.obj F) where
  app X :=
    (SList.monoidalLiftNatTrans (fun c ↦
      (SList.monoidalLiftConsNilIso ..).hom ≫ F.map ((SList.monoidalLiftConsNilIso ..).inv)) :
      SList.monoidalLift ((Pi.postcompFunctor K F).obj X) ⟶ SList.monoidalLift X ⋙ F)
  naturality {X Y} f := by
    dsimp
    apply SList.monoidalNatTrans_ext_app_singleton
    intro c
    simp

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

section

local notation3 "Θ" => SList.monoidalLift
local notation3 "□" => Pi.postcompFunctor
local notation3 "⊚" => Pi.precompFunctor'
/- The associativity diagram from [arkor2025, 3.5].
Proving that this commutes is essentially saying that `generalizedμ`
defines a lax morphism of pseudoalgebras
between `C` and `D` viewed as pseudoalgebras for the relative pseudomonad `SList`. -/
lemma laxAssoc {J K : Type*} (f : J → SList K) (g : K → C) :
    (RelativePseudomonad.μ (□ _ F |>.obj g) f).hom ≫
      Functor.whiskerLeft (monoidalLift f) (generalizedμ F _ |>.app g) ≫
        (Functor.associator _ _ _).inv =
    (monoidalLiftFunctor ..).map ((⊚ D f).map (generalizedμ F _ |>.app g)) ≫
      (monoidalLiftFunctor ..).map ((Pi.precompFunctor'AssocIso ..).hom) ≫
        (generalizedμ F _ |>.app _) ≫
      Functor.whiskerRight (RelativePseudomonad.μ g f).hom F := by
  apply SList.monoidalNatTrans_ext_app_singleton
  intro c
  simp [generalizedμ, show monoidalLiftConsNilIso ((⊚ D ((⊚ C f).obj (Θ g))).obj F) c =
      monoidalLiftConsNilIso ((□ J F).obj ((⊚ C f).obj (Θ g))) c by rfl]

end

end

section

universe v u

-- When bundled as pseudofunctors, the categories need to live in the same universe levels.
-- We could potentially consider a version with ULifts everywhere.
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
  (F : C ⥤ D) [F.LaxBraided]

/-- A lax monoidal functor between monoidal categories interprets as a lax natural transformation
between the pseudfunctors out of the Kleisli bicategory classifying the source and
target monoidal categories. -/
@[simps!]
def natTransOfLaxBraided {C D : Type u} [Category.{v} C] [Category.{v} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [SymmetricCategory C] [SymmetricCategory D]
    (F : C ⥤ D) [F.LaxBraided] :
      Lax.LaxTrans
        (SList.Kleisli.pseudoOfSymmMonCat C).toLax
        (SList.Kleisli.pseudoOfSymmMonCat D).toLax where
  app J := Cat.Hom.ofFunctor <| Pi.postcompFunctor J.of F
  naturality {J K} f := Cat.Hom₂.ofNatTrans <|
    (Functor.associator _ _ _).inv ≫ (Functor.whiskerRight (generalizedμ _ _) _)
  naturality_id J := by
    ext X
    dsimp [SList.Kleisli.pseudoOfSymmMonCat] at X ⊢
    ext j
    simp [generalizedμ]
  naturality_comp {J K L} f g := by
    ext X
    dsimp [SList.Kleisli.pseudoOfSymmMonCat] at X ⊢
    ext j
    dsimp [Functor.postcompose₂]
    simp only [Category.id_comp]
    have := congr_app (laxAssoc F f.of X) (g.of j)
    dsimp at this
    simp only [Category.comp_id, Category.id_comp] at this
    rw [this]
    rw [← NatTrans.comp_app_assoc, SList.monoidalLiftNatTrans_comp]
    congr
    ext k
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
    rfl
  naturality_naturality := by cat_disch

end

end Kleisli

end CategoryTheory.SList
