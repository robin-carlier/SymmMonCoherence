/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import SymmMonCoherence.ForMathlib.Tactic.CategoryTheory.RotateIso

/-! # Relative pseudomonads

In this file, we formalize the notion of a pseudomonad relative to a pseudofunctor
`J : C ⥤ᵖ D`. This notion was introduced in [1], as
a generalization of the notion of a pseudomonad (the bicategorical enhancements of monads).
Roughly speaking, a relative pseudomonad is the structure of an assignment `T : C → D`, and the
data of "extensions" functors that turns a 1-morphism `J X ⟶ T Y` to a 1-morphism `T X ⟶ T Y`,
equipped with associativity and naturality isomorphisms.

An example is given by presheaves: it defines a pseudomonad relative to the inclusion of small
categories in the category of large categories. In this case, the extension functor corresponds to
left Kan extension along the Yoneda embedding.

For this project, we are interested in the pseudomonad that sends a type `C` to the
free symmetric monoidal category on `C`; the extension functor is the functor
that sends a type-level function to a symmetric monoidal functor.
Pseudo-algebras for this pseudomonad correspond to symmetric monoidal categories.
An other example would be the assigment sending a type to the free (non-symmetric) monoidal
category, with similar structure map.

## Main definitions
- `RelativePseudoMonad`: the structure of a relative pseudomonad, following [1].
- `RelativePseudoMonad.Kleisli` : the Kleisli bicategory for a relative pseudomonad.
- `RelativePseudoMonad.PseudoAlgebra`: the structure of a pseudoalgebras for a
  relative pseudomonad, following [2].
- `RelativePseudoMonad.PseudoAlgebra.LaxMorphism`,
  `RelativePseudoMonad.PseudoAlgebra.OplaxMorphism`, and `PseudoAlgebra.StrongMorphism`: structures
  for various flavors of morphisms of pseudoalgebras. We also give a (scoped) bicategory
  instance on pseudoalgebras and lax morphisms.
- `RelativePseudoMonad.KleisliToAlg`: the pseudofunctor that sends an object of the Kleisli
  bicategory to the corresponding free pseudoalgebra.

## References

* [1] [Relative pseudomonads, Kleisli bicategories, and substitution monoidal structures](https://link.springer.com/article/10.1007/s00029-017-0361-3)
* [2] [Bicategories of algebras for relative pseudomonads](https://arxiv.org/abs/2501.12510)

-/

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂
namespace CategoryTheory.Bicategory

variable {C D : Type*} [Bicategory.{w₁, v₁} C] [Bicategory.{w₂, v₂} D]

variable (J : C ⥤ᵖ D)

/-- A pseudomonad relative to a pseudofunctor `J : C ⥤ᵖ D` is the data of
a function `C → D`, equipped with the additional structure of extension
functors `(J.obj X ⟶ obj Y) ⥤ (obj X ⟶ obj Y)`, equipped with a "unit"
"multiplication" operation satisfying associativity and unitality conditions.

This is [Fiore-Gambino-Hyland-Winskel, Def 3.1].
-/
structure RelativePseudoMonad where
  /-- The object-level assignment. -/
  obj (X : C) : D
  /-- The extension functors. -/
  extension {X Y : C} : (J.obj X ⟶ obj Y) ⥤ (obj X ⟶ obj Y)
  /-- The unit 1-morphism. -/
  ι (X : C) : J.obj X ⟶ obj X
  /-- The multiplication natural 2-isomorphism. -/
  μ {X Y Z : C} (f : J.obj X ⟶ obj Y) (g : J.obj Y ⟶ obj Z) :
    extension.obj (f ≫ extension.obj g) ≅ extension.obj f ≫ extension.obj g
  /-- The "restriction" isomorphism. -/
  η {X Y : C} (f : J.obj X ⟶ obj Y) : f ≅ ι X ≫ extension.obj f
  /-- The unit 2-isomorphism. -/
  θ (X : C) : extension.obj (ι X) ≅ 𝟙 (obj X)
  μ_natural_left {X Y Z : C} {f f' : J.obj X ⟶ obj Y} (φ : f ⟶ f') (g : J.obj Y ⟶ obj Z) :
    extension.map (φ ▷ extension.obj g) ≫ (μ _ _).hom =
    (μ _ _).hom ≫ extension.map φ ▷ extension.obj g := by cat_disch
  μ_natural_right {X Y Z : C} (f : J.obj X ⟶ obj Y) {g g' : J.obj Y ⟶ obj Z} (φ : g ⟶ g') :
    extension.map (f ◁ extension.map φ) ≫ (μ _ _).hom =
    (μ _ _).hom ≫ extension.obj f ◁ extension.map φ := by cat_disch
  η_natural {X Y : C} {f f' : J.obj X ⟶ obj Y} (φ : f ⟶ f') :
     φ ≫ (η _).hom = (η _).hom ≫ ι _ ◁ extension.map φ := by cat_disch
  /-- Associativity for the pseudomonad. -/
  assoc {X Y Z V : C} (f : J.obj X ⟶ obj Y)
    (g : J.obj Y ⟶ obj Z) (h : J.obj Z ⟶ obj V) :
    (μ f (g ≫ extension.obj h)).hom ≫ _ ◁ (μ _ _).hom ≫ (α_ _ _ _).inv =
    extension.map (_ ◁ (μ _ _).hom) ≫ extension.map (α_ _ _ _).inv ≫
      (μ _ _).hom ≫ (μ _ _).hom ▷ _
  /-- Unitality for the pseudomonad -/
  unit {X Y : C} (f : J.obj X ⟶ obj Y) :
    extension.map (η f).hom ≫ (μ _ _).hom ≫ (θ _).hom ▷ _ = (λ_ _).inv

namespace RelativePseudoMonad

attribute [reassoc (attr := simp)] μ_natural_left μ_natural_right η_natural assoc unit
variable {J} (T : RelativePseudoMonad J)

/-- The Kleisli bicategory of a relative pseudomonad. It has the same objects as
the underlying category `C`, and has morphisms `J.obj X ⟶ T.obj Y` as the category of
morphisms from `X` to `Y`. This is realized as a one-field structure wrapper around `C`. -/
structure Kleisli (T : RelativePseudoMonad J) where
  /-- The underlying object of `C` -/
  as : C

variable {T}

/-- 1-Morphisms `X ⇝ Y` in the Kleisli bicategory are morphisms `J.obj X ⟶ T.obj Y` ind `D`. -/
structure Kleisli.Hom (X Y : T.Kleisli) where
  /-- The underlying morphism. -/
  of : J.obj X.as ⟶ (T.obj Y.as)

instance : Quiver T.Kleisli where Hom := Kleisli.Hom

@[simps!]
instance : CategoryStruct T.Kleisli where
  id X := .mk <| T.ι X.as
  comp {_ _ _} f g := .mk <| f.of ≫ (T.extension.obj g.of)

/-- 2-morphisms in `T.Kleisli`. This is a one-field structure wrapper around
2-morphisms in `D`. -/
structure Kleisli.Hom₂ {X Y : T.Kleisli} (f g : X ⟶ Y) where
  /-- The underlying morphism. -/
  hom : f.of ⟶ g.of

@[simps!]
instance (X Y : T.Kleisli) : Category (X ⟶ Y) where
  Hom f g := Kleisli.Hom₂ f g
  id f := .mk <| 𝟙 f.of
  comp {f g h} α β := .mk <| α.hom ≫ β.hom

@[ext]
lemma ext₂ (X Y : T.Kleisli) {f g : X ⟶ Y} {α β : f ⟶ g} (h : α.hom = β.hom) :
    α = β := by
  cases α
  cases β
  grind

/-- Constructor for 2-isomorphisms in `T.Kleisli`. -/
@[simps]
def isoMk₂ {X Y : T.Kleisli} {f g : X ⟶ Y} (e : f.of ≅ g.of) :
    f ≅ g where
  hom.hom := e.hom
  inv.hom := e.inv

/-- The bicategory structure on `T.Kleisli`. This is [Fiore-Gambino-Hyland-Winskel, Thm. 4.1]. -/
@[simps! whiskerLeft_hom whiskerRight_hom
  associator_hom_hom associator_inv_hom
  leftUnitor_hom_hom leftUnitor_inv_hom
  rightUnitor_hom_hom rightUnitor_inv_hom]
instance bicategory : Bicategory T.Kleisli where
  homCategory X Y := inferInstance
  whiskerLeft {X Y Z} f {g h} φ := .mk <| f.of ◁ T.extension.map φ.hom
  whiskerRight {X Y Z} {f g} φ h := .mk <| φ.hom ▷ T.extension.obj h.of
  associator {X Y Z V} f g h := isoMk₂ <| α_ _ _ _ ≪≫ (whiskerLeftIso f.of (T.μ _ _).symm)
  leftUnitor {X Y} f := isoMk₂ <| (T.η _).symm
  rightUnitor {X Y} g := isoMk₂ <| whiskerLeftIso g.of (T.θ _) ≪≫ ρ_ _
  id_whiskerLeft {a b} {f g} φ := by
    ext
    simp [η_natural]
  whiskerRight_id {x y} {f g} φ := by
    ext
    simp [← cancel_mono (g.of ◁ (T.θ y.as).hom), ← whisker_exchange]
  comp_whiskerLeft _ _ _ _ _ := by
    ext
    dsimp
    simp only [comp_whiskerLeft, Category.assoc,
      ← cancel_mono (α_ _ _ _).hom,
      Iso.inv_hom_id, Category.comp_id, Iso.cancel_iso_hom_left, ← whiskerLeft_comp]
    simp [μ_natural_right]
  whiskerRight_comp _ _ _ := by
    ext
    dsimp
    simp_rw [associator_naturality_left_assoc,
      Category.assoc, Iso.inv_hom_id_assoc,
      whisker_exchange_assoc]
    simp
  whisker_assoc _ _ _ _ _ := by
    ext
    dsimp
    simp only [whisker_assoc, Category.assoc, ← cancel_mono (α_ _ _ _).hom, Iso.inv_hom_id,
      Category.comp_id, ← whiskerLeft_comp, Iso.cancel_iso_hom_left]
    simp [μ_natural_left]
  whisker_exchange _ _ := by
    ext
    simp [whisker_exchange]
  pentagon {_ _ _ _ _} f g h k := by
    ext
    dsimp
    simp only [comp_whiskerRight, whisker_assoc, Functor.map_comp, whiskerLeft_comp, Category.assoc,
      Iso.inv_hom_id_assoc, comp_whiskerLeft]
    simp [← pentagon_hom_hom_inv_hom_hom_assoc, ← whiskerLeft_comp,
      rotate_isos% 2 0 T.assoc g.of h.of k.of]
  triangle f g := by
    ext
    dsimp
    have := rotate_isos% 2 0 T.unit g.of
    simp [← whiskerLeft_comp, this]

variable (T) in
/-- The structure of a pseudoalgebra for the relative pseudomonad `T` over
`J : C ⥤ᵖ D`. This is the data of an object `A` , along with extensions
functors `(J.obj c ⟶ A) ⥤ (T.obj c ⟶ A)` for every object `c : C`.

This is [Arkor-Saville-Slattery, Def 3.1]. -/
structure PseudoAlgebra where
  /-- The object of `D` underlying the pseudoalgebra. -/
  A : D
  /-- The extension functors. -/
  extension {c : C} : (J.obj c ⟶ A) ⥤ (T.obj c ⟶ A)
  /-- The multiplication 2-isomorphisms. -/
  μ {X Y : C} (f : J.obj X ⟶ T.obj Y) (g : J.obj Y ⟶ A) :
    extension.obj (f ≫ extension.obj g) ≅ T.extension.obj f ≫ extension.obj g
  μ_natural_left {X Y : C} {f f' : J.obj X ⟶ T.obj Y} (φ : f ⟶ f') (g : J.obj Y ⟶ A) :
    extension.map (φ ▷ extension.obj g) ≫ (μ _ _).hom =
    (μ _ _).hom ≫ T.extension.map φ ▷ extension.obj g := by cat_disch
  μ_natural_right {X Y : C} (f : J.obj X ⟶ T.obj Y) {g g': J.obj Y ⟶ A} (φ : g ⟶ g') :
    extension.map (f ◁ extension.map φ) ≫ (μ _ _).hom =
    (μ _ _).hom ≫ T.extension.obj f ◁ extension.map φ
  /-- The unit 2-isomorphisms. -/
  η {X : C} (f : J.obj X ⟶ A) : f ≅ T.ι _ ≫ extension.obj f
  η_natural {X : C} {f f' : J.obj X ⟶ A} (φ : f ⟶ f') :
    φ ≫ (η _).hom = (η _).hom ≫ T.ι _ ◁ extension.map φ
  /-- Associativity for the pseudoalgebra. -/
  assoc {X Y Z : C} (f : J.obj X ⟶ T.obj Y) (g : J.obj Y ⟶ T.obj Z) (h : J.obj Z ⟶ A) :
    (μ f (g ≫ extension.obj h)).hom ≫ _ ◁ (μ _ _).hom ≫ (α_ _ _ _).inv =
    extension.map (f ◁ (μ _ _).hom) ≫ extension.map (α_ _ _ _).inv ≫
      (μ _ _).hom ≫ (T.μ _ _).hom ▷ _
  /-- Unitality for the pseudoalgebra. -/
  unit {X : C} (f : J.obj X ⟶ A) :
    extension.map (η f).hom ≫ (μ _ _).hom ≫ (T.θ _).hom ▷ _ = (λ_ _).inv

namespace PseudoAlgebra

attribute [reassoc (attr := simp)] μ_natural_left μ_natural_right η_natural unit assoc

/-- The free pseudoalgebra on an object `X : C`: it is given by `T.obj X`,
with the multiplication and unit taken from the pseudomonad structure. -/
@[simps]
abbrev Free (X : C) : T.PseudoAlgebra where
  A := T.obj X
  extension := T.extension
  μ := T.μ
  μ_natural_right := T.μ_natural_right
  η := T.η
  η_natural := T.η_natural
  assoc := T.assoc
  unit := T.unit

/-- [Arkor-Saville-Slattery, Lemma 3.15] -/
lemma unit' {A : T.PseudoAlgebra} {X Y : C} (f : J.obj X ⟶ T.obj Y) (g : J.obj Y ⟶ A.A) :
    (A.η (f ≫ A.extension.obj g)).hom ≫ T.ι X ◁ (A.μ _ _).hom ≫ (α_ _ _ _).inv =
    (T.η _).hom ▷ _ := by
  rw [← cancel_mono (A.η _).hom]
  simp only [Category.assoc, η_natural, η_natural_assoc, Iso.cancel_iso_hom_left]
  simp_rw [← whiskerLeft_comp, rotate_isos% ← 0 2 @A.unit, Category.assoc,
    ← rotate_isos% 1 2 A.assoc (T.ι _) f g, ← whisker_exchange_assoc,
    ← leftUnitor_inv_naturality_assoc, whiskerRight_comp_assoc, cancelIso,
    ← comp_whiskerRight_assoc, ← rotate_isos% 0 1 rotate_isos% 3 1 T.unit]
  simp only [comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_comp]
  rotate_isos ← 1 0
  simp [← whiskerLeft_comp]

end PseudoAlgebra

@[reassoc (attr := simp)]
lemma extension_ι_θ_inv_hom (X : C) :
    T.extension.obj (T.ι X) ◁ (T.θ X).inv ≫ (T.θ X).hom ▷ T.extension.obj (T.ι X) =
    (ρ_ (T.extension.obj (T.ι X))).hom ≫ (λ_ (T.extension.obj (T.ι X))).inv := by
  /- The idea is that `ρ_ (T.extension.obj (T.ι X))` is essentially `ρ_ (𝟙 _)` through
  T.θ, and that `ρ_ (𝟙 _) = λ_ (𝟙 _)` in a bicategory. -/
  have lun := leftUnitor_inv_naturality (T.θ X).inv
  rw [unitors_inv_equal] at lun
  have run := rotate_isos% 0 1 rightUnitor_inv_naturality (T.θ X).inv
  rw [← run] at lun
  simp_rw [Category.assoc, ← whisker_exchange] at lun
  simp only [Iso.cancel_iso_inv_left] at lun
  rotate_isos ← 1 0 at lun
  exact lun.symm

lemma η_ι_extension_eq_whiskerLeft_ι {X Y : C} (f : J.obj X ⟶ T.obj Y) :
    (T.η (T.ι X ≫ T.extension.obj f)).hom =
    T.ι X ◁ T.extension.map (T.η f).hom := by
  have := T.η_natural (T.η f).hom
  rwa [Iso.cancel_iso_hom_left] at this

/-- [Fiore-Gambino-Hyland-Winskel, Lemma 3.2.(iii)] -/
lemma η_ι_whiskerLeft_θ (X : C) :
    (T.η (T.ι X)).hom ≫ _ ◁ (T.θ _).hom = (ρ_ _).inv := by
  rw [← cancel_mono ((T.η (T.ι X)).hom ▷ _), Category.assoc, whisker_exchange,
    ← (PseudoAlgebra.Free (T := T) X).unit' (T.ι X) (T.ι X)]
  -- TODO: have an inv% elab
  have r1 := congr(inv $(rotate_isos% ← 0 1 extension_ι_θ_inv_hom (T := T) X))
  push inv at r1
  simp [r1, rotate_isos% 1 0 rotate_isos% ← 0 1 T.unit (T.ι X), η_ι_extension_eq_whiskerLeft_ι]

/-- [Fiore-Gambino-Hyland-Winskel, Lemma 3.2.(ii)] -/
@[reassoc]
lemma unit_right {X Y : C} (f : J.obj X ⟶ T.obj Y) :
    (T.μ f (T.ι Y)).hom ≫ _ ◁ (T.θ _).hom  ≫ (ρ_ _).hom =
    T.extension.map (f ◁ (T.θ _).hom) ≫ T.extension.map (ρ_ _).hom := by
  /- Not a very nice proof. The idea is to look at associativity for f and the the unit twice, and
  then use unitality to create some redundancy that we can start cancelling.
  By shaking enough the diagrams, we can get rid of all the μ's and η's and be left with a "pure
  bicategory goal" -/
  have assoc₀ := T.extension.map (f ◁ T.extension.map (T.η (T.ι Y)).hom) ≫=
    T.assoc f (T.ι Y) (T.ι Y)
  simp_rw [T.μ_natural_right_assoc f (T.η (T.ι _)).hom ,
    ← rotate_isos% 0 1 T.μ_natural_left (_ ◁ (T.θ _).hom ≫ (ρ_ f).hom) (T.ι _)] at assoc₀
  simp only [comp_whiskerRight, whisker_assoc, Category.assoc, triangle_assoc_comp_right,
    Functor.map_comp, Iso.map_inv_hom_id_assoc] at assoc₀
  simp_rw [← Functor.map_comp_assoc, ← whiskerLeft_comp_assoc, rotate_isos% ← 0 1 T.unit,
    reassoc_of% rotate_isos% ← 0 1 T.unit] at assoc₀
  simp only [whiskerLeft_comp, Category.assoc, inv_hom_whiskerRight, Category.comp_id,
    whiskerLeft_inv_hom, Functor.map_id, Category.id_comp, Iso.cancel_iso_hom_left] at assoc₀
  rotate_isos ← 2 0 at assoc₀
  rw [← cancel_epi (ρ_ _).hom, ← cancel_epi (_ ◁ (T.θ _).hom), ← rightUnitor_naturality_assoc]
  simp_rw [whisker_exchange_assoc , ← assoc₀, comp_whiskerLeft, Category.assoc,
    Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc, ← whisker_exchange,
    ← leftUnitor_inv_naturality_assoc,
    ← whisker_exchange_assoc]
  simp [← whisker_exchange_assoc]

/-- [Fiore-Gambino-Hyland-Winskel, Lemma 3.2.(i)]. -/
lemma η_comp_μ' {X Y Z : C} (f : J.obj X ⟶ T.obj Y) (g : J.obj Y ⟶ T.obj Z) :
    (T.η (f ≫ T.extension.obj g)).hom ≫ T.ι _ ◁ (T.μ f g).hom =
    (T.η f).hom ▷ T.extension.obj g ≫ (α_ _ _ _).hom := by
  simpa using rotate_isos% ← 0 1 (PseudoAlgebra.Free (T := T) Z).unit' f g

namespace PseudoAlgebra

/-- The structure of a lax morphism of pseudoalgebras. It consists of a morphism
between the underlying object, as well as a 2-morphism intertwining the extension
operations.
This is [Arkor-Saville-Slattery, Def 3.5]. -/
structure LaxMorphism (A B : T.PseudoAlgebra) where
  /-- The morphism between the underlying objects of the algebras. -/
  h : A.A ⟶ B.A
  /-- The 2-morphism intertwining the extension operations. -/
  ψ {X : C} (f : J.obj X ⟶ A.A) : B.extension.obj (f ≫ h) ⟶ A.extension.obj f ≫ h
  ψ_natural {X : C} {f f' : J.obj X ⟶ A.A} (φ : f ⟶ f') :
    B.extension.map (φ ▷ h) ≫ ψ _ = ψ _ ≫ A.extension.map φ ▷ h := by cat_disch
  /-- Compatibility with associativity. -/
  assoc {X Y : C} (f : J.obj X ⟶ T.obj Y) (g : J.obj Y ⟶ A.A) :
    B.extension.map (_ ◁ ψ g) ≫ B.extension.map (α_ _ _ _).inv ≫
      ψ _ ≫ (A.μ _ _).hom ▷ _ =
    (B.μ f (g ≫ h)).hom ≫ _ ◁ ψ g ≫ (α_ _ _ _).inv := by cat_disch
  /-- Compatibility with unitality. -/
  unit {X : C} (f : J.obj X ⟶ A.A) :
    (B.η (f ≫ h)).hom ≫ _ ◁ ψ _ ≫ (α_ _ _ _).inv = (A.η f).hom ▷ _ := by cat_disch

attribute [reassoc (attr := simp)] LaxMorphism.assoc LaxMorphism.unit LaxMorphism.ψ_natural

/-- The structure of an oplax morphism of pseudoalgebras. It consists of a morphism
between the underlying object, as well as a 2-morphism intertwining the extension
operations.
This is [Arkor-Saville-Slattery, Def 3.5]. -/
structure OplaxMorphism (A B : T.PseudoAlgebra) where
  /-- The morphism between the underlying objects of the algebras. -/
  h : A.A ⟶ B.A
  /-- The 2-morphism intertwining the extension operations. -/
  ψ {X : C} (f : J.obj X ⟶ A.A) :
     A.extension.obj f ≫ h ⟶ B.extension.obj (f ≫ h)
  ψ_natural {X : C} {f f' : J.obj X ⟶ A.A} (φ : f ⟶ f') :
     A.extension.map φ ▷ h ≫ ψ _ = ψ _ ≫ B.extension.map (φ ▷ h) := by cat_disch
  /-- Compatibility with associativity. -/
  assoc {X Y : C} (f : J.obj X ⟶ T.obj Y) (g : J.obj Y ⟶ A.A) :
    ψ (f ≫ A.extension.obj g) ≫ B.extension.map (α_ _ _ _).hom ≫
      B.extension.map (_ ◁ ψ _) ≫ (B.μ _ _).hom =
    (A.μ _ _).hom ▷ h ≫ (α_ _ _ _).hom ≫ _ ◁ ψ _ := by cat_disch
  /-- Compatibility with unitality. -/
  unit {X : C} (f : J.obj X ⟶ A.A) :
     (A.η f).hom ▷ _ ≫ (α_ _ _ _).hom  ≫ _ ◁ ψ _ = (B.η (f ≫ h)).hom := by cat_disch

attribute [reassoc (attr := simp)] OplaxMorphism.assoc OplaxMorphism.unit OplaxMorphism.ψ_natural

/-- A lax morphism is "strong" if the intertwining morphisms are all isomorphisms. -/
class LaxMorphism.IsStrong {A B : T.PseudoAlgebra} (h : LaxMorphism A B) where
  isIso {X : C} (f : J.obj X ⟶ A.A) : IsIso (h.ψ f)

/-- An oplax morphism is "strong" if the intertwining morphisms are all isomorphisms. -/
class OplaxMorphism.IsStrong {A B : T.PseudoAlgebra} (h : OplaxMorphism A B) where
  isIso {X : C} (f : J.obj X ⟶ A.A) : IsIso (h.ψ f)

attribute [instance] LaxMorphism.IsStrong.isIso OplaxMorphism.IsStrong.isIso

/-- The structure of a strong morphism of pseudoalgebras. It consists of a morphism
between the underlying object, as well as a 2-isomorphism intertwining the extension
operations.
This is [Arkor-Saville-Slattery, Def 3.5]. -/
structure StrongMorphism (A B : T.PseudoAlgebra) where
  /-- The morphism between the underlying objects of the algebras. -/
  h : A.A ⟶ B.A
  /-- The 2-isomorphism intertwining the extension operations. -/
  ψ {X : C} (f : J.obj X ⟶ A.A) : B.extension.obj (f ≫ h) ≅ A.extension.obj f ≫ h
  ψ_natural {X : C} {f f' : J.obj X ⟶ A.A} (φ : f ⟶ f') :
    B.extension.map (φ ▷ h) ≫ (ψ _).hom = (ψ _).hom ≫ A.extension.map φ ▷ h := by cat_disch
  /-- Compatibility with associativity. -/
  assoc {X Y : C} (f : J.obj X ⟶ T.obj Y) (g : J.obj Y ⟶ A.A) :
    (B.μ f (g ≫ h)).hom ≫ _ ◁ (ψ g).hom ≫ (α_ _ _ _).inv =
    B.extension.map (_ ◁ (ψ g).hom) ≫ B.extension.map (α_ _ _ _).inv ≫
      (ψ _).hom ≫ (A.μ _ _).hom ▷ _ := by cat_disch
  /-- Compatibility with unitality. -/
  unit {X : C} (f : J.obj X ⟶ A.A) :
    (B.η (f ≫ h)).hom ≫ _ ◁ (ψ _).hom ≫ (α_ _ _ _).inv = (A.η f).hom ▷ _ := by cat_disch

attribute [reassoc (attr := simp)] StrongMorphism.assoc StrongMorphism.unit StrongMorphism.ψ_natural

namespace StrongMorphism

/-- Construct a strong morphism from a lax morphism with an `IsStrong` instance. -/
@[simps]
noncomputable def ofStrongLax
    {A B : T.PseudoAlgebra} (h : LaxMorphism A B) [h.IsStrong] :
    StrongMorphism A B where
  h := h.h
  ψ _ := asIso <| h.ψ ..
  ψ_natural := by cat_disch
  assoc := by cat_disch
  unit := by cat_disch

/-- Construct a strong morphism from an oplax morphism with an `IsStrong` instance. -/
@[simps]
noncomputable def ofStrongOplax
    {A B : T.PseudoAlgebra} (h : OplaxMorphism A B) [h.IsStrong] :
    StrongMorphism A B where
  h := h.h
  ψ _ := asIso <| inv <| h.ψ ..
  ψ_natural := by
    intros
    symm
    simp
  assoc := by
    intros
    rw [← IsIso.inv_eq_inv]
    rotate_isos ← 0 1
    push inv
    simp
  unit := by
    intros
    rw [← IsIso.inv_eq_inv]
    rotate_isos ← 1 0
    push inv
    simp

/-- Project a strong morphism to a lax morphism. -/
@[simps]
def toLax {A B : T.PseudoAlgebra} (h : StrongMorphism A B) : LaxMorphism A B where
  h := h.h
  ψ _ := (h.ψ _).hom
  ψ_natural := by cat_disch
  assoc := by cat_disch
  unit := by cat_disch

instance {A B : T.PseudoAlgebra} (h : StrongMorphism A B) : LaxMorphism.IsStrong h.toLax where
  isIso _ := by dsimp; infer_instance

/-- Project a strong morphism to an oplax morphism. -/
@[simps]
def toOplax {A B : T.PseudoAlgebra} (h : StrongMorphism A B) : OplaxMorphism A B where
  h := h.h
  ψ _ := (h.ψ _).inv
  ψ_natural := by
    intros
    symm
    rotate_isos 1 0
    simp [← ψ_natural_assoc]
  assoc := by
    intros
    rotate_isos 1 2
    simp [h.assoc]
  unit := by
    intros
    rw [← IsIso.inv_eq_inv]
    rotate_isos ← 1 0
    push inv
    simp

instance {A B : T.PseudoAlgebra} (h : StrongMorphism A B) : OplaxMorphism.IsStrong h.toOplax where
  isIso _ := by dsimp; infer_instance

-- TODO: put a category structure on strong morphisms.
end StrongMorphism

namespace LaxMorphism

/-! Category structure on lax morphisms of pseudoalgebras -/

/-- Morphisms of lax morphisms are given by 2-morphisms compatible with the
intertwining maps. -/
structure Hom {A B : T.PseudoAlgebra} (Φ Φ' : LaxMorphism A B) where
  /-- The underlying 2-morphism of a morphism between lax morphism. -/
  α : Φ.h ⟶ Φ'.h
  w {X : C} (f : J.obj X ⟶ A.A) :
    B.extension.map (f ◁ α) ≫ (Φ'.ψ _) = Φ.ψ _ ≫ A.extension.obj f ◁ α := by cat_disch

attribute [reassoc (attr := local simp)] Hom.w

/-- Morphisms in the bicategory of pseudoalgebra with lax morphisms.
Run `open scoped RelativePseudoMonad.PseudoAlgebra.LaxMorphism` to use. -/
scoped instance : Quiver T.PseudoAlgebra where Hom A B := LaxMorphism A B

-- TODO: move away from this design and have 3 type aliases `PseudoAlgebraₛ`, `PseudoAlgebraₒ`,
-- and `PseudoAlgebraₗ`? This seems like the only way to talk about forgetful pseudofunctors.

/-- 2-Morphisms in the bicategory of pseudoalgebras and lax morphism
Run `open scoped RelativePseudoMonad.PseudoAlgebra.LaxMorphism` to use. -/
scoped instance (A B : T.PseudoAlgebra) : Quiver (A ⟶ B) where Hom

@[ext]
lemma ext₂ {A B : T.PseudoAlgebra} {Φ Φ' : A ⟶ B} {u v : Φ ⟶ Φ'} (h : u.α = v.α) :
    u = v := by
  cases u
  cases v
  grind

/-- Morphisms in the bicategory of pseudoalgebras and lax morphism form a category.
Run `open scoped RelativePseudoMonad.PseudoAlgebra.LaxMorphism` to use. -/
@[simps!]
scoped instance (A B : T.PseudoAlgebra) : Category (A ⟶ B) where
  id Φ := { α := 𝟙 _ }
  comp {Φ Φ' Φ''} u v := { α := u.α ≫ v.α }

/-- Pseudoalgebras and their lax morphism admit a category structure.
Run `open scoped RelativePseudoMonad.PseudoAlgebra.LaxMorphism` to use. -/
@[simps!]
scoped instance : CategoryStruct T.PseudoAlgebra where
  id A :=
    { h := 𝟙 _
      ψ f := A.extension.map (ρ_ _).hom ≫ (ρ_ _).inv }
  comp {A B C} Φ Φ' :=
    { h := Φ.h ≫ Φ'.h
      ψ f := C.extension.map (α_ _ _ _).inv ≫ Φ'.ψ _ ≫ (Φ.ψ _) ▷ _ ≫ (α_ _ _ _).hom
      ψ_natural {X f f'} φ := by simp [← comp_whiskerRight_assoc, -comp_whiskerRight]
      assoc {X Y} f g := by
        simp only [whiskerLeft_comp, Functor.map_comp, whiskerRight_comp, Category.assoc,
          Iso.hom_inv_id_assoc]
        simp_rw [← C.μ_natural_right_assoc, whisker_assoc_symm, Category.assoc,
          ← Φ'.assoc_assoc f (g ≫ Φ.h), ← Functor.map_comp_assoc]
        simp only [whisker_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Iso.inv_hom_id_assoc, pentagon_hom_inv_inv_inv_inv, Functor.map_comp, ψ_natural_assoc,
          pentagon_hom_hom_inv_inv_hom, pentagon_inv_inv_hom_hom_inv]
        simp_rw [← Functor.map_comp_assoc, associator_inv_naturality_middle,
          Functor.map_comp_assoc, cancel_epi, ψ_natural_assoc, ← comp_whiskerRight_assoc,
          Φ.assoc f g]
        simp
      unit {X} f := by
        simp only [whiskerLeft_comp, Category.assoc, whiskerRight_comp]
        simp_rw [← C.η_natural_assoc, whisker_assoc_symm, Category.assoc, Φ'.unit_assoc,
          ← comp_whiskerRight_assoc, rotate_isos% ← 0 1 Φ.unit f]
        simp }

/-- Constructor for 2-isomorphisms of pseudoalgebras. -/
@[simps]
def mkIso₂ {A B : T.PseudoAlgebra} {Φ Φ' : A ⟶ B}
    (α : Φ.h ≅ Φ'.h)
    (w : ∀ {X : C} (f : J.obj X ⟶ A.A),
      B.extension.map (f ◁ α.hom) ≫ (Φ'.ψ _) = Φ.ψ _ ≫ A.extension.obj f ◁ α.hom := by cat_disch) :
    Φ ≅ Φ' where
  hom.α := α.hom
  inv.α := α.inv
  inv.w {X} f := by
    rotate_isos 1 1
    simp [w]

/-- The bicategory structure on pseudoalgebras with lax morphisms.
This is [Arkor-Saville-Slattery, Thm. 3.9]. -/
@[simps! whiskerLeft_α whiskerRight_α
  associator_hom_α associator_inv_α
  leftUnitor_hom_α leftUnitor_inv_α
  rightUnitor_hom_α rightUnitor_inv_α]
scoped instance : Bicategory T.PseudoAlgebra where
  homCategory A B := inferInstance
  whiskerLeft {a b c} f {g h} φ :=
    { α := f.h ◁ φ.α
      w {X} m := by
        dsimp
        simp_rw [← Functor.map_comp_assoc, associator_inv_naturality_right, Functor.map_comp_assoc,
          φ.w_assoc, whisker_exchange_assoc]
        simp }
  whiskerRight {a b c} {f g} φ h :=
    { α := φ.α ▷ h.h
      w {X} m := by
        dsimp
        simp_rw [← Functor.map_comp_assoc, associator_inv_naturality_middle, Functor.map_comp_assoc,
          h.ψ_natural_assoc, Category.assoc, ← associator_naturality_middle,
          ← comp_whiskerRight_assoc, φ.w] }
  associator {a b c d} f g h :=
    mkIso₂ (α_ f.h g.h h.h) fun {X} m ↦ by
      dsimp
      simp_rw [Category.assoc, ← Functor.map_comp_assoc, pentagon_hom_inv_inv_inv_inv,
        Functor.map_comp_assoc,
        h.ψ_natural_assoc]
      simp
  leftUnitor {a b} f :=
    mkIso₂ (λ_ f.h) fun {X} m ↦ by
      simp only [comp_h, id_h, comp_ψ, id_ψ, comp_whiskerRight, Category.assoc,
        triangle_assoc_comp_right_inv, whiskerLeft_inv_hom, Category.comp_id]
      simp_rw [← f.ψ_natural (ρ_ m).hom, ← Functor.map_comp_assoc, ← triangle, cancelIso]
  rightUnitor {a b} f :=
    mkIso₂ (ρ_ f.h) fun {X} m ↦ by simp
  whisker_exchange {a b c d f g h} u v := by
    ext
    simp [whisker_exchange]

end LaxMorphism

namespace StrongMorphism

/-! Category structure on strong morphisms of pseudoalgebras -/

/-- Morphisms of strong morphisms are given by 2-morphisms compatible with the
intertwining maps. -/
structure Hom {A B : T.PseudoAlgebra} (Φ Φ' : StrongMorphism A B) where
  /-- The underlying 2-morphism of a morphism between strong morphism. -/
  α : Φ.h ⟶ Φ'.h
  w {X : C} (f : J.obj X ⟶ A.A) :
    B.extension.map (f ◁ α) ≫ (Φ'.ψ _).hom = (Φ.ψ _).hom ≫ A.extension.obj f ◁ α := by cat_disch

attribute [reassoc (attr := local simp)] Hom.w

/-- Morphisms in the bicategory of pseudoalgebra with strong morphisms.
Run `open scoped RelativePseudoMonad.PseudoAlgebra.StrongMorphism` to use. -/
scoped instance : Quiver T.PseudoAlgebra where Hom A B := StrongMorphism A B

/-- 2-Morphisms in the bicategory of pseudoalgebras and strong morphism
Run `open scoped RelativePseudoMonad.PseudoAlgebra.StrongMorphism` to use. -/
scoped instance (A B : T.PseudoAlgebra) : Quiver (A ⟶ B) where Hom

@[ext]
lemma ext₂ {A B : T.PseudoAlgebra} {Φ Φ' : A ⟶ B} {u v : Φ ⟶ Φ'} (h : u.α = v.α) :
    u = v := by
  cases u
  cases v
  grind

/-- Morphisms in the bicategory of pseudoalgebras and strong morphisms form a category.
Run `open scoped RelativePseudoMonad.PseudoAlgebra.StrongMorphism` to use. -/
@[simps!]
scoped instance (A B : T.PseudoAlgebra) : Category (A ⟶ B) where
  id Φ := { α := 𝟙 _ }
  comp {Φ Φ' Φ''} u v := { α := u.α ≫ v.α }

/-- Pseudoalgebras and their strong morphism admit a category structure.
Run `open scoped RelativePseudoMonad.PseudoAlgebra.StrongMorphism` to use. -/
@[simps!]
scoped instance : CategoryStruct T.PseudoAlgebra where
  id A :=
    { h := 𝟙 _
      ψ f := A.extension.mapIso (ρ_ _) ≪≫ (ρ_ _).symm }
  comp {A B C} Φ Φ' :=
    { h := Φ.h ≫ Φ'.h
      ψ f := (C.extension.mapIso (α_ _ _ _).symm) ≪≫ (Φ'.ψ _) ≪≫ whiskerRightIso (Φ.ψ _) Φ'.h ≪≫
        (α_ _ _ _)
      ψ_natural {X f f'} φ := by simp [← comp_whiskerRight_assoc, -comp_whiskerRight]
      assoc {X Y} f g := by
        dsimp
        simp only [whiskerLeft_comp, Category.assoc, Functor.map_comp, whiskerRight_comp,
          Iso.hom_inv_id_assoc]
        simp_rw [← C.μ_natural_right_assoc, whisker_assoc_symm, Category.assoc,
          Φ'.assoc_assoc f (g ≫ Φ.h), ← Functor.map_comp_assoc]
        simp only [whisker_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Iso.inv_hom_id_assoc, pentagon_hom_inv_inv_inv_inv, Functor.map_comp, ψ_natural_assoc,
          pentagon_hom_hom_inv_inv_hom, pentagon_inv_inv_hom_hom_inv]
        simp_rw [← Functor.map_comp_assoc, associator_inv_naturality_middle,
          Functor.map_comp_assoc, cancel_epi, ψ_natural_assoc, ← comp_whiskerRight_assoc,
          ← Φ.assoc f g]
        simp [-assoc]
      unit {X} f := by
        dsimp
        simp only [whiskerLeft_comp, Category.assoc, whiskerRight_comp]
        simp_rw [← C.η_natural_assoc, whisker_assoc_symm, Category.assoc, Φ'.unit_assoc,
          ← comp_whiskerRight_assoc, rotate_isos% ← 0 1 Φ.unit f]
        simp }

/-- Constructor for 2-isomorphisms of pseudoalgebras. -/
@[simps]
def mkIso₂ {A B : T.PseudoAlgebra} {Φ Φ' : A ⟶ B}
    (α : Φ.h ≅ Φ'.h)
    (w : ∀ {X : C} (f : J.obj X ⟶ A.A),
        B.extension.map (f ◁ α.hom) ≫ (Φ'.ψ _).hom = (Φ.ψ _).hom ≫ A.extension.obj f ◁ α.hom := by
      cat_disch) :
    Φ ≅ Φ' where
  hom.α := α.hom
  inv.α := α.inv
  inv.w {X} f := by
    rotate_isos 1 1
    simp [w]

/-- The bicategory structure on pseudoalgebras with strong morphisms.
This is [Arkor-Saville-Slattery, Thm. 3.9]. -/
@[simps! whiskerLeft_α whiskerRight_α
  associator_hom_α associator_inv_α
  leftUnitor_hom_α leftUnitor_inv_α
  rightUnitor_hom_α rightUnitor_inv_α]
scoped instance : Bicategory T.PseudoAlgebra where
  homCategory A B := inferInstance
  whiskerLeft {a b c} f {g h} φ :=
    { α := f.h ◁ φ.α
      w {X} m := by
        dsimp
        simp_rw [← Functor.map_comp_assoc, associator_inv_naturality_right, Functor.map_comp_assoc,
          φ.w_assoc, whisker_exchange_assoc]
        simp }
  whiskerRight {a b c} {f g} φ h :=
    { α := φ.α ▷ h.h
      w {X} m := by
        dsimp
        simp_rw [← Functor.map_comp_assoc, associator_inv_naturality_middle, Functor.map_comp_assoc,
          h.ψ_natural_assoc, Category.assoc, ← associator_naturality_middle,
          ← comp_whiskerRight_assoc, φ.w] }
  associator {a b c d} f g h :=
    mkIso₂ (α_ f.h g.h h.h) fun {X} m ↦ by
      dsimp
      simp_rw [Category.assoc, ← Functor.map_comp_assoc, pentagon_hom_inv_inv_inv_inv,
        Functor.map_comp_assoc,
        h.ψ_natural_assoc]
      simp
  leftUnitor {a b} f :=
    mkIso₂ (λ_ f.h) fun {X} m ↦ by
      dsimp
      simp only [comp_whiskerRight, Category.assoc,
        triangle_assoc_comp_right_inv, whiskerLeft_inv_hom, Category.comp_id]
      simp_rw [← f.ψ_natural (ρ_ m).hom, ← Functor.map_comp_assoc, ← triangle, cancelIso]
  rightUnitor {a b} f :=
    mkIso₂ (ρ_ f.h) fun {X} m ↦ by simp
  whisker_exchange {a b c d f g h} u v := by
    ext
    simp [whisker_exchange]

end StrongMorphism

end PseudoAlgebra

open PseudoAlgebra in
open StrongMorphism in
/-- The pseudofunctor realizing ther Kleisli bicategory as the category of free pseudoalgebras (with
strong morphisms).
TODO: show that it is fully faithful. -/
@[simps!]
def KleisliToAlg : T.Kleisli ⥤ᵖ T.PseudoAlgebra where
  obj X := Free X.as
  map {X Y} f :=
    { h := T.extension.obj f.of
      ψ {Z} g := (T.μ g f.of)
      unit {Z} g := by simpa using (PseudoAlgebra.Free (T := T) Y.as).unit' .. }
  map₂ {X Y} {f g} Φ := { α := T.extension.map Φ.hom }
  mapComp {a b c} f g := mkIso₂ (T.μ ..) (fun {X} m ↦ by simp [← T.assoc_assoc m f.of g.of])
  mapId a := mkIso₂ (T.θ a.as) (fun {X} (m : J.obj X ⟶ T.obj a.as) ↦ by
    simp [rotate_isos% ← 0 1 T.unit_right])
  map₂_associator {a b c d} f g h := by
    ext
    simp [rotate_isos% ← 2 3 T.assoc f.of g.of h.of]
  map₂_left_unitor {a b} f := by
    ext;
    simp [rotate_isos% 1 0 T.unit_assoc f.of]
  map₂_right_unitor {a b} f := by
    ext;
    simp [T.unit_right f.of]
  map₂_whisker_left {a b c} f {g h} η := by
    ext
    simp [← T.μ_natural_right_assoc f.of η.hom]
  map₂_whisker_right{a b c} {f g} η h := by
    ext
    simp [← T.μ_natural_left_assoc η.hom h.of]

end RelativePseudoMonad

end CategoryTheory.Bicategory
