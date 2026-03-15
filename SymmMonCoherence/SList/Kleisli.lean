/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.EffBurnside
public import SymmMonCoherence.SList.Substitution
public import SymmMonCoherence.SList.Duality
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

universe u

@[expose] public section

/-! # The Kleisli bicategory of symmetric lists

In this file, we introduce the Kleisli bicategory of symmetric lists,
i.e the bicategory whose objects are types, and arrows
J -> K are functions J -> SList K.

This category is a tool to abstract the monoidal computations required to build
a pseudofunctor `EffBurnside FintypeCat ⥤ᵖ Cat` out of a symmetric monoidal category:
we will show that any symmetric monoidal category in fact defines a pseudofunctor
`Kleisliᵒᵖ ⥤ᵖ Cat` first.
Then, the natural target for the functor out of
`Burnside (FintypeCat)` will be `Kleisliᵒᵖ` instead of `Cat`: this fully encodes the
idea that "all of the formulas involved are universal".
In practice, this will reduce the amount of back and forth between
the category we interpret the formulas in and the category of symmetric lists.
-/

namespace CategoryTheory.SList

namespace RelativePseudomonad

/-! In this section, we give the assignment `X ↦ SList X` the structure of a relative pseudomonad
over the inclusion `Type ⥤ᵖ Cat` (though we state it in an unbundled way).
This is mostly a sanity check. -/

/-- The structure isomorphism (g^* f)^* ⟶ g^*f^* of the relative pseudomonad
of symmetric lists, we generalize the target of `g` to be any symmetric monoidal category
rather than just a free one, as this is useful. -/
def μ {X Y Z : Type*} [Category* Z] [MonoidalCategory Z] [SymmetricCategory Z]
    (g : Y → Z) (f : X → SList Y) :
    monoidalLift ((Pi.precompFunctor' _ f).obj (monoidalLift g)) ≅
    monoidalLift f ⋙ monoidalLift g :=
  monoidalLiftNatIso (fun x ↦
    monoidalLiftConsNilIso ((Pi.precompFunctor' Z f).obj (monoidalLift g)) x ≪≫
      (monoidalLift g).mapIso (monoidalLiftConsNilIso f x).symm)

section

variable {X Y Z : Type*} [Category* Z] [MonoidalCategory Z] [SymmetricCategory Z]
  (g : Y → Z) (f : X → SList Y)

instance : (μ g f).hom.IsMonoidal := by
  dsimp [μ]
  infer_instance

@[simp]
lemma μ_hom_app_singleton
    (x : X) :
    (μ g f).hom.app [x]~ =
    (monoidalLiftConsNilIso ((Pi.precompFunctor' Z f).obj (monoidalLift g)) x).hom ≫
      (monoidalLift g).map (monoidalLiftConsNilIso f x).inv := by
  simp [μ]

@[simp]
lemma μ_inv_app_singleton (x : X) :
    (μ g f).inv.app [x]~ =
    (monoidalLift g).map (monoidalLiftConsNilIso f x).hom ≫
      (monoidalLiftConsNilIso
        ((Pi.precompFunctor' Z f).obj (monoidalLift g)) x).inv := by
  simp [μ]

end

variable {X Y Z : Type*} (f : X → SList Y) (g : Y → SList Z)

abbrev ι (X : Type*) (x : X) : SList X := [x]~

abbrev η {X : Type*} (f : X → SList Y) :
    f ≅ (Pi.precompFunctor' _ (ι X)).obj (monoidalLift f) :=
  Pi.isoMk (fun c ↦ (monoidalLiftConsNilIso f c).symm)

abbrev θ (X : Type*) :
    monoidalLift (ι X) ≅ 𝟭 (SList X) :=
  monoidalLiftNatIso (fun _ ↦ (monoidalLiftConsNilIso ..))

set_option backward.isDefEq.respectTransparency false in
lemma assoc {X Y Z V : Type*} (f : X → SList Y) (g : Y → SList Z) (h : Z → SList V) :
    (monoidalLiftFunctor ..).map ((Pi.precompFunctor' _ f).map (μ h g).hom) ≫
      (monoidalLiftFunctor ..).map (Pi.precompFunctor'AssocIso ..).hom ≫
      (μ _ _).hom ≫
      Functor.whiskerRight (μ _ _).hom ((monoidalLiftFunctor ..).obj h) =
    (μ _ _).hom ≫ (Functor.whiskerLeft (((monoidalLiftFunctor ..).obj f)) (μ _ _).hom) ≫
      (Functor.associator _ _ _).inv := by
  apply monoidalNatTrans_ext_app_singleton
  intro c
  simp

set_option backward.isDefEq.respectTransparency false in
lemma assoc' {X Y Z V : Type*} [Category* V] [MonoidalCategory V] [SymmetricCategory V]
    (f : X → SList Y) (g : Y → SList Z) (h : Z → V) :
    (monoidalLiftFunctor ..).map ((Pi.precompFunctor' _ f).map (μ h g).hom) ≫
      (monoidalLiftFunctor ..).map (Pi.precompFunctor'AssocIso ..).hom ≫
      (μ _ _).hom ≫
      Functor.whiskerRight (μ _ _).hom ((monoidalLiftFunctor ..).obj h) =
    (μ _ _).hom ≫ (Functor.whiskerLeft (((monoidalLiftFunctor ..).obj f)) (μ _ _).hom) ≫
      (Functor.associator _ _ _).inv := by
  apply monoidalNatTrans_ext_app_singleton
  intro c
  simp

set_option backward.isDefEq.respectTransparency false in
lemma unit {X Y : Type*} (f : X → SList Y) :
    (monoidalLiftFunctor ..).map (η f).hom ≫ (μ f (ι X)).hom ≫
      Functor.whiskerRight (θ X).hom ((monoidalLiftFunctor ..).obj f) =
    (Functor.leftUnitor _).inv := by
  apply monoidalNatTrans_ext_app_singleton
  intro c
  simp

end RelativePseudomonad

@[pp_with_univ]
structure Kleisli where
  of : Type u

namespace Kleisli

/- The Hom-types in Kleisli: a morphism `X ⟶ Y` is
a function `X.of → SList Y.of`. -/
structure Hom (X Y : Kleisli.{u}) where
  of : X.of → SList Y.of

instance : Quiver Kleisli where
  Hom := Hom

@[simps! -fullyApplied]
instance homCategory (X Y : Kleisli.{u}) : Category.{u} (X ⟶ Y) :=
  inferInstanceAs (Category <| InducedCategory _ (·.of))

@[ext]
lemma hom₂_ext {X Y : Kleisli.{u}} {f g : X ⟶ Y} {η θ : f ⟶ g} (h : η.hom = θ.hom) :
    η = θ := by
  apply InducedCategory.hom_ext
  exact h

@[simps! -fullyApplied id_of comp_of]
instance : CategoryStruct Kleisli.{u} where
  comp f g := .mk <| (Pi.precompFunctor'.{u} _ f.of).obj ((monoidalLiftFunctor ..).obj g.of)
  id _ := .mk (RelativePseudomonad.ι _)

@[simps]
abbrev mkIso₂ {X Y : Kleisli.{u}} {f g : X ⟶ Y} (e : f.of ≅ g.of) : f ≅ g where
  hom := .mk e.hom
  inv := .mk e.inv
  hom_inv_id := by
    ext : 1
    simp
  inv_hom_id := by
    ext : 1
    simp

abbrev associator {X Y Z T : Kleisli.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (f ≫ g) ≫ h ≅ f ≫ g ≫ h :=
  mkIso₂ <| (Pi.precompFunctor'AssocIso _ f.of (monoidalLift g.of) (monoidalLift h.of)) ≪≫
      (Pi.precompFunctor' (SList T.of) f.of).mapIso (RelativePseudomonad.μ h.of g.of).symm

abbrev rightUnitor {X Y : Kleisli.{u}} (f : X ⟶ Y) : (f ≫ 𝟙 _) ≅ f :=
  mkIso₂ <|
    (Pi.precompFunctor' ..).mapIso (RelativePseudomonad.θ _) ≪≫
      Pi.precompFunctor'Id _

abbrev leftUnitor {X Y : Kleisli.{u}} (f : X ⟶ Y) :
    𝟙 _ ≫ f ≅ f :=
  mkIso₂ <| (RelativePseudomonad.η f.of).symm

set_option backward.isDefEq.respectTransparency false in
@[simps! whiskerRight_hom whiskerLeft_hom associator_hom_hom associator_inv_hom
rightUnitor_hom_hom rightUnitor_inv_hom leftUnitor_hom_hom leftUnitor_inv_hom]
instance : Bicategory Kleisli.{u} where
  homCategory := homCategory.{u}
  whiskerLeft {X Y Z} f {g h} η :=
    .mk <| fun z ↦
      ((monoidalLiftFunctor ..).map (η.hom)).app (f.of z)
  whiskerRight {X Y Z} {f g} η h :=
    .mk <| fun z ↦
      ((monoidalLiftFunctor ..).obj h.of).map (η.hom z)
  associator f g h := associator f g h
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  comp_whiskerLeft {a b c d} f g {h h'} η := by
    ext i
    dsimp
    simp only [Category.id_comp, Category.comp_id]
    simp_rw [← NatTrans.comp_app_assoc, ← NatTrans.comp_app]
    rw [← Functor.whiskerLeft_app]
    congr 1
    apply monoidalNatTrans_ext_app_singleton
    intro c
    simp
  whiskerLeft_id {a b c} f g := by
    ext i
    dsimp
    simp only [Category.id_comp, Iso.hom_inv_id]
    suffices H : monoidalLiftNatTrans (fun k ↦ 𝟙 ((monoidalLift g.of).obj [k]~)) = 𝟙 _ by
      rw [H]
      simp
    apply monoidalNatTrans_ext_app_singleton
    intro c
    simp
  whiskerLeft_comp {a b c} f {g h k} η θ := by
    ext i
    dsimp
    simp_rw [← NatTrans.comp_app]
    congr 1
    apply monoidalNatTrans_ext_app_singleton
    intro c
    simp
  whiskerRight_comp {a b c d} {f g} η h k := by
    ext i
    dsimp
    have := (RelativePseudomonad.μ k.of h.of).hom.naturality (η.hom i)
      =≫ (RelativePseudomonad.μ k.of h.of).inv.app (g.of i)
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at this
    simpa using this
  whiskerRight_id {a b} f g η := by
    ext i
    dsimp
    simp only [Category.comp_id, Category.id_comp]
    let e : monoidalLift (RelativePseudomonad.ι b.of) ≅ 𝟭 _ := RelativePseudomonad.θ _
    have := e.hom.naturality (η.hom i) =≫ e.inv.app (g.of i)
    simp only [Functor.id_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      Functor.id_map] at this
    rw [this]
    congr
  whisker_assoc {a b c d} f g h η k := by
    ext i
    dsimp
    simp only [Category.comp_id, Category.id_comp]
    simp_rw [← Functor.whiskerRight_app, ← NatTrans.comp_app_assoc, ← NatTrans.comp_app]
    congr 1
    apply monoidalNatTrans_ext_app_singleton
    intro c
    simp
  pentagon {a b c d e} f g h k := by
    ext i
    dsimp
    simp only [Category.id_comp]
    simp_rw [← Functor.whiskerRight_app, ← Functor.whiskerLeft_app, ← NatTrans.comp_app_assoc,
      ← NatTrans.comp_app]
    congr 1
    /- Rewriting `Category.id_comp` followed by `congr` as we did above yields an expression that
    abuses associativity of functor composition (one of the `Category.id_comp` that
    got rewritten was secretly a `Functor.associator ..`).
    Resolving the abuse as below is a bit ugly but still faster than trying to avoid the
    rewriting of that identity (which would involve precisely identifying from which
    associator every identity comes from, using nth-rewrite to only rewrite this one and
    not the other etc). -/
    apply (config := {allowSynthFailures := true}) monoidalNatTrans_ext_app_singleton
    · apply (config := {allowSynthFailures := true}) NatTrans.IsMonoidal.comp
      haveI : NatTrans.IsMonoidal <|
        (monoidalLift g.of).whiskerLeft (RelativePseudomonad.μ k.of h.of).inv := by infer_instance
      convert this
      ext
      · simp [Functor.LaxMonoidal.ε]
      · simp [Functor.LaxMonoidal.μ]
    · intro c
      have := (RelativePseudomonad.μ k.of h.of).inv.naturality (monoidalLiftConsNilIso g.of c).hom
      dsimp at this
      simp [this]
  triangle {f g h} x y := by
    ext i
    dsimp
    simp only [Iso.hom_inv_id, Functor.map_comp, ← Functor.whiskerRight_app]
    rw [Functor.map_id (monoidalLift y.of)]
    nth_rw 2 [← Functor.leftUnitor_hom_app (monoidalLift y.of)]
    simp_rw [Category.id_comp, ← NatTrans.comp_app]
    congr 1
    apply monoidalNatTrans_ext_app_singleton
    intro c
    simp

universe v' u'
open Bicategory

/-- The action of a morphism in the Kleisli bicategory on a symmetric monoidal category. -/
abbrev extendedPullback (C : Type u') [Category.{v'} C]
    [MonoidalCategory C] [SymmetricCategory C] {X Y : Kleisli.{u}}
    (f : Y ⟶ X) : (X.of → C) ⥤ (Y.of → C) :=
  monoidalLiftFunctor _ _ ⋙ Pi.precompFunctor' _ f.of

/-- The action of a 2-morphism in the Kleisli bicategory on a symmetric monoidal category. -/
abbrev extendedPullback₂ (C : Type u') [Category.{v'} C]
    [MonoidalCategory C] [SymmetricCategory C] {X Y : Kleisli.{u}}
    {f g : Y ⟶ X} (η : f ⟶ g) : extendedPullback C f ⟶ extendedPullback C g :=
  (monoidalLiftFunctor _ _).whiskerLeft ((Pi.precomposingFunctor C _ _).map η.hom)

example (C : Type u') [Category.{v'} C]
    [MonoidalCategory C] [SymmetricCategory C] {X Y : Kleisli.{u}}
    {f g : X ⟶ Y} (η : f ⟶ g) : (extendedPullback₂ C η).IsMonoidal := by infer_instance

set_option backward.isDefEq.respectTransparency false in
abbrev extendedPullbackComp (C : Type*) [Category* C] [MonoidalCategory C] [SymmetricCategory C]
    {X Y Z : Kleisli.{u}}
    (f : Z ⟶ Y) (g : Y ⟶ X) :
    extendedPullback C (f ≫ g) ≅ extendedPullback C g ⋙ extendedPullback C f :=
  NatIso.ofComponents (fun X ↦ Pi.isoMk (fun i ↦ (RelativePseudomonad.μ _ _).symm.app (f.of i)))
    (fun {U V} η ↦ by
      ext k
      simp only [Functor.comp_obj, comp_of, monoidalLiftFunctor_obj, Pi.precompFunctor'_obj,
        Functor.comp_map, Pi.comp_apply,
        Pi.precompFunctor'_map, Pi.isoMk_hom, Iso.app_hom, Iso.symm_hom]
      simp_rw [← Functor.whiskerLeft_app, ← NatTrans.comp_app]
      congr 1
      apply monoidalNatTrans_ext_app_singleton
      intro c
      simp)

set_option backward.isDefEq.respectTransparency false in
/-- Any symmetric monoidal category can be interpreted as a pseudofunctor
`Kleisliᵒᵖ ⥤ᵖ Cat`, sending `J` to the category of families `J → C`
and using monoidal substitutions on arrow:
a morphism `φ : K → SList J` is sent to the natural transformation sending
`X : J → C` to the restriction along `φ` of the symmetric monoidal functor `SList J ⥤ C` induced
by `X`.

This construction can be interpreted as restricting the (bicategorical) Yoneda embedding
of `C` (in the bicategory of pseudoalgebras for the relative pseudomonad of
free symmetric monoidal categories) along the inclusion of the Kleisli bicategory as the
full sub-bicategory of free algebras.

For instance, for `K := Fin 1`, `J := Fin 2`, `φ : * ↦ 0 ::~ [1]~` and `X := ![c₁, c₂]`,
((pseudoOfSymmMonCat (C : Type u')).map φ.op).obj X identifies to `c₁ ⊗ c₂`. -/
@[simps!]
def pseudoOfSymmMonCat (C : Type u') [Category.{v'} C] [MonoidalCategory C] [SymmetricCategory C] :
    (Kleisli.{0})ᵒᵖ ⥤ᵖ Cat.{v', u'} where
  obj X := .of <| X.unop.of → C
  map f := (extendedPullback C f.unop).toCatHom
  map₂ η := NatTrans.toCatHom₂ <| extendedPullback₂ _ η.unop2
  mapId K := Cat.Hom.isoMk <|
    NatIso.ofComponents (fun X ↦ Pi.isoMk fun i ↦ monoidalLiftConsNilIso ..)
  mapComp {K K' K''} f g := Cat.Hom.isoMk <| extendedPullbackComp ..
  map₂_whisker_right {a b c} {f g} η h := by
    ext (X : a.unop.of → C)
    dsimp
    ext i
    dsimp
    simp_rw [← NatTrans.comp_app, ← Functor.whiskerRight_app]
    congr 1
    apply monoidalNatTrans_ext_app_singleton
    intro c
    simp
  map₂_associator {a b c d} f g h := by
    ext (X : a.unop.of → C)
    dsimp
    ext i
    simp only [Pi.precompFunctor'_obj, associator_inv_hom, NatTrans.pi'_app, evaluation_map_app,
      Category.id_comp, Pi.comp_apply, Pi.isoMk_hom, Iso.app_hom, Iso.symm_hom,
      Pi.precompFunctor'_map, Pi.isoMk_inv, Iso.app_inv, Iso.symm_inv]
    /- again, there is an abuse of functor associativity, when trying to go back to the level of
    natural transforms, this time the fastest way is to manually add the correction term -/
    rw [← Category.comp_id
      ((RelativePseudomonad.μ X f.unop.of).hom.app ((monoidalLift g.unop.of).obj (h.unop.of i))),
      show
        (𝟙 ((monoidalLift f.unop.of ⋙ monoidalLift X).obj
          ((monoidalLift g.unop.of).obj (h.unop.of i)))) =
        ((monoidalLift g.unop.of).associator
          (monoidalLift f.unop.of) (monoidalLift X)).inv.app (h.unop.of i) by simp]
    simp_rw [← Functor.whiskerRight_app, ← Functor.whiskerLeft_app, ← NatTrans.comp_app]
    congr 1
    apply monoidalNatTrans_ext_app_singleton
    intro c
    simp
  map₂_left_unitor {a b} f := by
    ext (X : a.unop.of → C)
    dsimp
    ext i
    simp only [Pi.precompFunctor'_obj, rightUnitor_hom_hom, NatTrans.pi'_app, evaluation_map_app,
      Iso.hom_inv_id, Pi.comp_apply, Pi.isoMk_hom, Iso.app_hom, Iso.symm_hom,
      Pi.precompFunctor'_map, Pi.id_apply]
    rw [show 𝟙 ((monoidalLift X).obj (f.unop.of i)) =
      (monoidalLift X).leftUnitor.inv.app (f.unop.of i) by rfl]
    simp_rw [← Functor.whiskerRight_app, ← NatTrans.comp_app]
    congr 1
    apply monoidalNatTrans_ext_app_singleton
    intro c
    simp

end Kleisli

end CategoryTheory.SList
