/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # The free symmetric monoidal category over a type -/

@[expose] public section

universe v' u u'

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u}

section

variable (C)

/--
Given a type `C`, the free symmetric monoidal category on `C` has as objects formal
expressions built from (formal) tensor products of terms of `C` and a formal unit.
Note that this is the same as the free non-symmetric monoidal category on `C`.
-/
inductive FreeSymmetricMonoidalCategory : Type u
  | of : C → FreeSymmetricMonoidalCategory
  | unit : FreeSymmetricMonoidalCategory
  | tensor : FreeSymmetricMonoidalCategory →
      FreeSymmetricMonoidalCategory → FreeSymmetricMonoidalCategory
  deriving Inhabited

end

local notation "F" => FreeSymmetricMonoidalCategory

namespace FreeSymmetricMonoidalCategory

/-- Formal compositions and tensor products of identities, unitors, associators and
braidings.
The morphisms of the free monoidal category are obtained as a quotient of these formal
morphisms by the relations defining a symmetric monoidal category.

We will later also describe a Path-oriented approach that is more suited for
rewriting arguments. -/
inductive Hom : F C → F C → Type u
  | id (X) : Hom X X
  | α_hom (X Y Z : F C) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : F C) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X) : Hom (unit.tensor X) X
  | l_inv (X) : Hom X (unit.tensor X)
  | ρ_hom (X : F C) : Hom (X.tensor unit) X
  | ρ_inv (X : F C) : Hom X (X.tensor unit)
  | β_hom (X Y : F C) : Hom (X.tensor Y) (Y.tensor X)
  | β_inv (X Y : F C) : Hom (Y.tensor X) (X.tensor Y)
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : F C) {Y₁ Y₂} (f : Hom Y₁ Y₂) : Hom (X.tensor Y₁) (X.tensor Y₂)
  | whiskerRight {X₁ X₂} (f : Hom X₁ X₂) (Y : F C) : Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W.tensor X) (Y.tensor Z)

local infixr:10 " ⟶ᵐ " => Hom

/-- The morphisms of the free symmetric monoidal category satisfies
relations ensuring that the resulting category is in fact a category and that it is
symmetric monoidal. Compare to the relations -/
inductive HomEquiv : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (X ⟶ᵐ Y) → Prop
  | refl {X Y} (f : X ⟶ᵐ Y) : HomEquiv f f
  | symm {X Y} (f g : X ⟶ᵐ Y) : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : X ⟶ᵐ Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h
  | comp {X Y Z} {f f' : X ⟶ᵐ Y} {g g' : Y ⟶ᵐ Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
  | whiskerLeft (X) {Y Z} (f f' : Y ⟶ᵐ Z) :
      HomEquiv f f' → HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
  | whiskerRight {Y Z} (f f' : Y ⟶ᵐ Z) (X) :
      HomEquiv f f' → HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
  | tensor {W X Y Z} {f f' : W ⟶ᵐ X} {g g' : Y ⟶ᵐ Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.tensor g) (f'.tensor g')
  | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
      HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
  | comp_id {X Y} (f : X ⟶ᵐ Y) : HomEquiv (f.comp (Hom.id _)) f
  | id_comp {X Y} (f : X ⟶ᵐ Y) : HomEquiv ((Hom.id _).comp f) f
  | assoc {X Y U V : F C} (f : X ⟶ᵐ U) (g : U ⟶ᵐ V) (h : V ⟶ᵐ Y) :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
  | tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : F C} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (g₁ : Y₁ ⟶ᵐ Z₁)
      (g₂ : Y₂ ⟶ᵐ Z₂) :
    HomEquiv ((f₁.comp g₁).tensor (f₂.comp g₂)) ((f₁.tensor f₂).comp (g₁.tensor g₂))
  | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
  | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
  | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
  | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) :
      HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
        ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
  | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
  | ρ_naturality {X Y} (f : X ⟶ᵐ Y) :
      HomEquiv ((f.whiskerRight unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
  | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
  | l_naturality {X Y} (f : X ⟶ᵐ Y) :
      HomEquiv ((f.whiskerLeft unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  | pentagon {W X Y Z} :
      HomEquiv
        (((Hom.α_hom W X Y).whiskerRight Z).comp
          ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W)))
        ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
  | triangle {X Y} :
      HomEquiv ((Hom.α_hom X unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
        ((Hom.ρ_hom X).whiskerRight Y)
  | β_hom_inv {X Y} : HomEquiv ((Hom.β_hom X Y).comp (Hom.β_inv X Y)) (Hom.id _)
  | β_inv_hom {X Y} : HomEquiv ((Hom.β_inv X Y).comp (Hom.β_hom X Y)) (Hom.id _)
  | β_self {X Y} : HomEquiv ((Hom.β_hom X Y).comp (Hom.β_hom Y X)) (Hom.id _)
  | β_naturality_left {X Y} (f : X ⟶ᵐ Y) (Z) :
      HomEquiv
        ((Hom.whiskerRight f Z).comp (Hom.β_hom Y Z))
        ((Hom.β_hom X Z).comp (Hom.whiskerLeft Z f))
  | β_naturality_right (X) {Y Z} (f : Y ⟶ᵐ Z) :
      HomEquiv
        ((Hom.whiskerLeft X f).comp (Hom.β_hom X Z))
        ((Hom.β_hom X Y).comp (Hom.whiskerRight f X))
  | hexagon_forward (X Y Z) :
      -- (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      --   ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braiding X Z).hom) := by
      HomEquiv
        ((Hom.α_hom X Y Z).comp ((Hom.β_hom X (Y.tensor Z)).comp (Hom.α_hom Y Z X)))
        ((Hom.whiskerRight (Hom.β_hom X Y) Z).comp <|
          (Hom.α_hom Y X Z).comp <| Hom.whiskerLeft Y (Hom.β_hom X Z))
  | hexagon_reverse (X Y Z) :
      -- (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      -- (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ▷ Y)
      HomEquiv
        ((Hom.α_inv X Y Z).comp ((Hom.β_hom (X.tensor Y) Z).comp (Hom.α_inv Z X Y)))
        ((Hom.whiskerLeft X (Hom.β_hom Y Z)).comp <|
          (Hom.α_inv X Z Y).comp <| Hom.whiskerRight (Hom.β_hom X Z) Y)

/-- We say that two formal morphisms in the free monoidal category are equivalent if they become
equal if we apply the relations that are true in a symmetric monoidal category. -/
def setoidHom (X Y : F C) : Setoid (X ⟶ᵐ Y) :=
  ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

attribute [instance] setoidHom

section

open FreeSymmetricMonoidalCategory.HomEquiv

instance categoryFreeMonoidalCategory : Category.{u} (F C) where
  Hom X Y := Quotient (FreeSymmetricMonoidalCategory.setoidHom X Y)
  id X := ⟦Hom.id X⟧
  comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg)
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (comp_id f)
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound (assoc f g h)

instance : MonoidalCategory (F C) where
  tensorObj X Y := FreeSymmetricMonoidalCategory.tensor X Y
  tensorHom := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg)
  whiskerLeft X _ _ f := Quot.map (fun f ↦ Hom.whiskerLeft X f) (fun f f' ↦ .whiskerLeft X f f') f
  whiskerRight f Y := Quot.map (fun f ↦ Hom.whiskerRight f Y) (fun f f' ↦ .whiskerRight f f' Y) f
  tensorHom_def {W X Y Z} := by
    rintro ⟨f⟩ ⟨g⟩
    exact Quotient.sound (tensorHom_def _ _)
  id_tensorHom_id _ _ := Quot.sound id_tensorHom_id
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    exact Quotient.sound (tensor_comp _ _ _ _).symm
  whiskerLeft_id X Y := Quot.sound (HomEquiv.whiskerLeft_id X Y)
  id_whiskerRight X Y := Quot.sound (HomEquiv.id_whiskerRight X Y)
  tensorUnit := FreeSymmetricMonoidalCategory.unit
  associator X Y Z :=
    ⟨⟦Hom.α_hom X Y Z⟧, ⟦Hom.α_inv X Y Z⟧, Quotient.sound α_hom_inv, Quotient.sound α_inv_hom⟩
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    exact Quotient.sound (associator_naturality _ _ _)
  leftUnitor X := ⟨⟦Hom.l_hom X⟧, ⟦Hom.l_inv X⟧, Quotient.sound l_hom_inv, Quotient.sound l_inv_hom⟩
  leftUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    exact Quotient.sound (l_naturality _)
  rightUnitor X :=
    ⟨⟦Hom.ρ_hom X⟧, ⟦Hom.ρ_inv X⟧, Quotient.sound ρ_hom_inv, Quotient.sound ρ_inv_hom⟩
  rightUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    exact Quotient.sound (ρ_naturality _)
  pentagon _ _ _ _ := Quotient.sound pentagon
  triangle _ _ := Quotient.sound triangle

@[simp]
theorem mk_comp {X Y Z : F C} (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z) :
    ⟦f.comp g⟧ = @CategoryStruct.comp (F C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_tensor {X₁ Y₁ X₂ Y₂ : F C} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
    ⟦f.tensor g⟧ = @MonoidalCategory.tensorHom (F C) _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_whiskerLeft (X : F C) {Y₁ Y₂ : F C} (f : Y₁ ⟶ᵐ Y₂) :
    ⟦f.whiskerLeft X⟧ = MonoidalCategory.whiskerLeft (C := F C) (X := X) (f := ⟦f⟧) :=
  rfl

@[simp]
theorem mk_whiskerRight {X₁ X₂ : F C} (f : X₁ ⟶ᵐ X₂) (Y : F C) :
    ⟦f.whiskerRight Y⟧ = MonoidalCategory.whiskerRight (C := F C) (f := ⟦f⟧) (Y := Y) :=
  rfl

@[simp]
theorem mk_id {X : F C} : ⟦Hom.id X⟧ = 𝟙 X :=
  rfl

@[simp]
theorem mk_α_hom {X Y Z : F C} : ⟦Hom.α_hom X Y Z⟧ = (α_ X Y Z).hom :=
  rfl

@[simp]
theorem mk_α_inv {X Y Z : F C} : ⟦Hom.α_inv X Y Z⟧ = (α_ X Y Z).inv :=
  rfl

@[simp]
theorem mk_ρ_hom {X : F C} : ⟦Hom.ρ_hom X⟧ = (ρ_ X).hom :=
  rfl

@[simp]
theorem mk_ρ_inv {X : F C} : ⟦Hom.ρ_inv X⟧ = (ρ_ X).inv :=
  rfl

@[simp]
theorem mk_l_hom {X : F C} : ⟦Hom.l_hom X⟧ = (λ_ X).hom :=
  rfl

@[simp]
theorem mk_l_inv {X : F C} : ⟦Hom.l_inv X⟧ = (λ_ X).inv :=
  rfl

@[simp]
theorem tensor_eq_tensor {X Y : F C} : X.tensor Y = X ⊗ Y :=
  rfl

@[simp]
theorem unit_eq_unit : FreeSymmetricMonoidalCategory.unit = 𝟙_ (F C) :=
  rfl

/-- The abbreviation for `⟦f⟧`. -/
/- This is useful since the notation `⟦f⟧` often behaves like an element of the quotient set,
but not like a morphism. This is why we need weird `@CategoryStruct.comp (F C) ...` in the
statement in `mk_comp` above. -/
abbrev homMk {X Y : F C} (f : X ⟶ᵐ Y) : X ⟶ Y := ⟦f⟧

instance : SymmetricCategory (F C) where
  braiding X Y :=
    { hom := (homMk <| .β_hom X Y)
      inv := (homMk <| .β_inv X Y)
      hom_inv_id := Quotient.sound β_hom_inv
      inv_hom_id := Quotient.sound β_inv_hom}
  braiding_naturality_left := by
    rintro _ _ ⟨f⟩ c
    exact Quotient.sound <| β_naturality_left f c
  braiding_naturality_right := by
    rintro c _ _ ⟨f⟩
    exact Quotient.sound <| β_naturality_right c f
  hexagon_forward _ _ _ := Quotient.sound (hexagon_forward _ _ _)
  hexagon_reverse _ _ _ := Quotient.sound (hexagon_reverse _ _ _)
  symmetry _ _ := Quotient.sound β_self

@[simp]
theorem braiding_hom_eq {X Y : F C} : ⟦Hom.β_hom X Y⟧ = (β_ X Y).hom := rfl

@[simp]
theorem braiding_inv_eq {X Y : F C} : ⟦Hom.β_inv X Y⟧ = (β_ X Y).inv := rfl

theorem Hom.inductionOn {motive : {X Y : F C} → (X ⟶ Y) → Prop} {X Y : F C} (t : X ⟶ Y)
    (id : (X : F C) → motive (𝟙 X))
    (α_hom : (X Y Z : F C) → motive (α_ X Y Z).hom)
    (α_inv : (X Y Z : F C) → motive (α_ X Y Z).inv)
    (l_hom : (X : F C) → motive (λ_ X).hom)
    (l_inv : (X : F C) → motive (λ_ X).inv)
    (ρ_hom : (X : F C) → motive (ρ_ X).hom)
    (ρ_inv : (X : F C) → motive (ρ_ X).inv)
    (β_hom : (X Y : F C) → motive (β_ X Y).hom)
    (β_inv : (X Y : F C) → motive (β_ X Y).inv)
    (comp : {X Y Z : F C} → (f : X ⟶ Y) → (g : Y ⟶ Z) → motive f → motive g → motive (f ≫ g))
    (whiskerLeft : (X : F C) → {Y Z : F C} → (f : Y ⟶ Z) → motive f → motive (X ◁ f))
    (whiskerRight : {X Y : F C} → (f : X ⟶ Y) → (Z : F C) → motive f → motive (f ▷ Z)) :
    motive t := by
  apply Quotient.inductionOn
  intro f
  induction f with
  | id X => exact id X
  | α_hom X Y Z => exact α_hom X Y Z
  | α_inv X Y Z => exact α_inv X Y Z
  | l_hom X => exact l_hom X
  | l_inv X => exact l_inv X
  | ρ_hom X => exact ρ_hom X
  | ρ_inv X => exact ρ_inv X
  | β_hom X Y => exact β_hom X Y
  | β_inv X Y => exact β_inv X Y
  | comp f g hf hg => exact comp _ _ (hf ⟦f⟧) (hg ⟦g⟧)
  | whiskerLeft X f hf => exact whiskerLeft X _ (hf ⟦f⟧)
  | whiskerRight f X hf => exact whiskerRight _ X (hf ⟦f⟧)
  | @tensor W X Y Z f g hf hg =>
      have : homMk f ⊗ₘ homMk g = homMk f ▷ X ≫ Y ◁ homMk g :=
        Quotient.sound (HomEquiv.tensorHom_def f g)
      change motive (homMk f ⊗ₘ homMk g)
      rw [this]
      exact comp _ _ (whiskerRight _ _ (hf ⟦f⟧)) (whiskerLeft _ _ (hg ⟦g⟧))

section Functor

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [SymmetricCategory D] (f : C → D)

/-- Auxiliary definition for `free_monoidal_category.project`. -/
def projectObj : F C → D
  | FreeSymmetricMonoidalCategory.of X => f X
  | FreeSymmetricMonoidalCategory.unit => 𝟙_ D
  | FreeSymmetricMonoidalCategory.tensor X Y => projectObj X ⊗ projectObj Y

section

open Hom

/-- Auxiliary definition for `FreeMonoidalCategory.project`. -/
@[simp]
def projectMapAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (projectObj f X ⟶ projectObj f Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, l_hom _ => (λ_ _).hom
  | _, _, l_inv _ => (λ_ _).inv
  | _, _, ρ_hom _ => (ρ_ _).hom
  | _, _, ρ_inv _ => (ρ_ _).inv
  | _, _, β_hom _ _ => (β_ _ _).hom
  | _, _, β_inv _ _ => (β_ _ _).inv
  | _, _, Hom.comp f g => projectMapAux f ≫ projectMapAux g
  | _, _, Hom.whiskerLeft X p => projectObj f X ◁ projectMapAux p
  | _, _, Hom.whiskerRight p X => projectMapAux p ▷ projectObj f X
  | _, _, Hom.tensor f g => projectMapAux f ⊗ₘ projectMapAux g

-- Porting note: this declaration generates the same panic.
/-- Auxiliary definition for `FreeMonoidalCategory.project`. -/
def projectMap (X Y : F C) : (X ⟶ Y) → (projectObj f X ⟶ projectObj f Y) :=
  Quotient.lift (projectMapAux f) <| by
    intro f g h
    induction h with
    | refl => rfl
    | symm _ _ _ hfg' => exact hfg'.symm
    | trans _ _ hfg hgh => exact hfg.trans hgh
    | comp _ _ hf hg => dsimp only [projectMapAux]; rw [hf, hg]
    | whiskerLeft _ _ _ _ hf => dsimp only [projectMapAux, projectObj]; rw [hf]
    | whiskerRight _ _ _ _ hf => dsimp only [projectMapAux, projectObj]; rw [hf]
    | tensor _ _ hfg hfg' => dsimp only [projectMapAux]; rw [hfg, hfg']
    | tensorHom_def _ _ =>
        dsimp only [projectMapAux, projectObj]; rw [MonoidalCategory.tensorHom_def]
    | comp_id => dsimp only [projectMapAux]; rw [Category.comp_id]
    | id_comp => dsimp only [projectMapAux]; rw [Category.id_comp]
    | assoc => dsimp only [projectMapAux]; rw [Category.assoc]
    | id_tensorHom_id => dsimp only [projectMapAux]; rw [MonoidalCategory.id_tensorHom_id]; rfl
    | tensor_comp => dsimp only [projectMapAux]; rw [MonoidalCategory.tensorHom_comp_tensorHom]
    | whiskerLeft_id =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.whiskerLeft_id]
    | id_whiskerRight =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.id_whiskerRight]
    | α_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | α_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | associator_naturality =>
        dsimp only [projectMapAux]; rw [MonoidalCategory.associator_naturality]
    | ρ_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | ρ_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | ρ_naturality =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.rightUnitor_naturality]
    | l_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | l_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | l_naturality =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.leftUnitor_naturality]
    | pentagon =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.pentagon]
    | triangle =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.triangle]
    | β_hom_inv => simp [projectMapAux, projectObj]
    | β_inv_hom => simp [projectMapAux, projectObj]
    | β_self => simp [projectMapAux, projectObj]
    | β_naturality_left f Z => simp [projectMapAux, projectObj]
    | β_naturality_right X f => simp [projectMapAux, projectObj]
    | hexagon_forward X Y Z => simp [projectMapAux, projectObj]
    | hexagon_reverse X Y Z => simp [projectMapAux, projectObj]

end

/-- If `D` is a monoidal category and we have a function `C → D`, then we have a
monoidal functor from the free monoidal category over `C` to the category `D`. -/
def project : F C ⥤ D where
  obj := projectObj f
  map := projectMap f _ _
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

@[simps!]
instance : (project f).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := fun f _ => by
        induction f using Quotient.recOn
        all_goals aesop
      μIso_hom_natural_right := fun _ f => by
        induction f using Quotient.recOn
        all_goals aesop }

instance : (project f).Braided where
  braided X Y := by
    simp only [Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, μ_def,
      Category.id_comp, Category.comp_id]
    rfl

end Functor

section NatTrans

section

def liftNatTransAux
    {D : Type*} [Category D] [MonoidalCategory D] [SymmetricCategory D]
    {G G' : F C ⥤ D}
    [G.Braided] [G'.LaxBraided]
    (e : ∀ c : C, G.obj (of c) ⟶ G'.obj (of c)) :
    ∀ (x : FreeSymmetricMonoidalCategory C), (G.obj x) ⟶ (G'.obj x)
  | .unit => (Functor.OplaxMonoidal.η G) ≫ (Functor.LaxMonoidal.ε G')
  | .of x => e x
  | .tensor x y =>
    (Functor.OplaxMonoidal.δ G x y) ≫
      ((liftNatTransAux e x) ⊗ₘ (liftNatTransAux e y)) ≫
      (Functor.LaxMonoidal.μ G' x y)

variable
  {D : Type*} [Category D] [MonoidalCategory D] [SymmetricCategory D]
  {G G' : F C ⥤ D}
  [G.Braided] [G'.LaxBraided]
  (e : ∀ c : C, G.obj (of c) ⟶ G'.obj (of c))

@[local simp]
lemma liftNatTransAux_unit :
    liftNatTransAux e (𝟙_ (F C)) = (Functor.OplaxMonoidal.η G) ≫ (Functor.LaxMonoidal.ε G') :=
  rfl

@[local simp]
lemma liftNatTransAux_of (c : C) : liftNatTransAux e (of c) = e c := rfl

@[local simp]
lemma liftNatTransAux_tensor (x y : F C) :
    liftNatTransAux e (x ⊗ y) =
    (Functor.OplaxMonoidal.δ G x y) ≫
      ((liftNatTransAux e x) ⊗ₘ (liftNatTransAux e y)) ≫
      (Functor.LaxMonoidal.μ G' x y) := rfl

@[no_expose] def liftNatTrans :
    G ⟶ G' where
  app := liftNatTransAux e
  naturality {x y} f := by
    induction f using Hom.inductionOn with
    | id X => simp
    | α_hom X Y Z =>
      simp only [liftNatTransAux_tensor, MonoidalCategory.tensorHom_def, Category.assoc,
        whiskerLeft_comp, comp_whiskerRight, whisker_assoc]
      simp_rw [whiskerRight_tensor_symm_assoc, Functor.OplaxMonoidal.associativity_assoc,
        Iso.inv_hom_id_assoc, whisker_exchange_assoc, tensor_whiskerLeft_symm_assoc,
        ← Functor.LaxMonoidal.associativity]
      simp_rw [whisker_exchange_assoc]
    | α_inv X Y Z =>
      rw [← cancel_epi (G.map (α_ X Y Z).hom), ← cancel_mono (G'.map (α_ X Y Z).hom), Eq.comm]
      -- and now this is the same as the case α_hom
      simp only [liftNatTransAux_tensor, MonoidalCategory.tensorHom_def, Category.assoc,
        comp_whiskerRight, whisker_assoc, Iso.map_hom_inv_id_assoc, whiskerLeft_comp,
        Functor.LaxMonoidal.associativity_inv, Functor.LaxMonoidal.associativity,
        Iso.inv_hom_id_assoc]
      simp_rw [whiskerRight_tensor_symm_assoc, Functor.OplaxMonoidal.associativity_assoc,
        Iso.inv_hom_id_assoc, whisker_exchange_assoc, tensor_whiskerLeft_symm_assoc,
        ← Functor.LaxMonoidal.associativity]
      simp_rw [whisker_exchange_assoc]
    | l_hom X => simp [MonoidalCategory.tensorHom_def, ← whisker_exchange_assoc]
    | l_inv X => simp [MonoidalCategory.tensorHom_def, ← whisker_exchange_assoc]
    | ρ_hom X => simp [MonoidalCategory.tensorHom_def, ← whisker_exchange_assoc]
    | ρ_inv X => simp [MonoidalCategory.tensorHom_def, ← whisker_exchange_assoc]
    | β_hom X Y => simp [Functor.LaxBraided.braided]
    | β_inv X Y =>
      rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
      simp [Functor.LaxBraided.braided]
    | comp f g ihf ihg => simp [reassoc_of% ihf, ihg]
    | whiskerLeft X f hf =>
      have := congr(G'.obj X ◁ $hf)
      simp only [whiskerLeft_comp] at this
      simp only [liftNatTransAux_tensor, MonoidalCategory.tensorHom_def, Category.assoc]
      simp_rw [Functor.Monoidal.map_whiskerLeft_assoc, Functor.Monoidal.μ_δ_assoc,
        whisker_exchange_assoc, reassoc_of% this]
      simp
    | whiskerRight f Z hf =>
      have := congr($hf ▷ G.obj Z)
      simp only [comp_whiskerRight] at this
      simp only [liftNatTransAux_tensor, MonoidalCategory.tensorHom_def, Category.assoc]
      simp_rw [Functor.Monoidal.map_whiskerRight_assoc, Functor.Monoidal.μ_δ_assoc,
        reassoc_of% this]
      simp [← whisker_exchange_assoc]

@[simp, reassoc]
lemma liftNatTrans_app_unit :
    (liftNatTrans e).app (𝟙_ (F C)) = (Functor.OplaxMonoidal.η G) ≫ (Functor.LaxMonoidal.ε G') :=
  (rfl)

@[simp]
lemma liftNatTrans_app_of (c : C) : (liftNatTrans e).app (of c) = e c := (rfl)

@[simp, reassoc]
lemma liftNatTrans_app_tensor (x y : F C) :
    (liftNatTrans e).app (x ⊗ y) =
    (Functor.OplaxMonoidal.δ G x y) ≫
      ((liftNatTrans e |>.app x) ⊗ₘ (liftNatTrans e |>.app y)) ≫
      (Functor.LaxMonoidal.μ G' x y) := (rfl)

instance : (liftNatTrans e).IsMonoidal where

end

def liftNatIso
    {D : Type*} [Category D] [MonoidalCategory D] [SymmetricCategory D]
    {G G' : FreeSymmetricMonoidalCategory C ⥤ D}
    [G.Braided] [G'.Braided]
    (e : ∀ c : C, G.obj (of c) ≅ G'.obj (of c)) :
    G ≅ G' where
  hom := liftNatTrans (fun x ↦ (e x).hom)
  inv := liftNatTrans (fun x ↦ (e x).inv)
  hom_inv_id := by
    ext x
    induction x with
    | of _ => simp
    | unit => simp
    | tensor x y hx hy =>
      dsimp
      simp only [liftNatTrans_app_tensor, Category.assoc, Functor.Monoidal.μ_δ_assoc,
        tensorHom_comp_tensorHom_assoc, ← NatTrans.comp_app, hx, hy]
      simp
  inv_hom_id := by
    ext x
    induction x with
    | of _ => simp
    | unit => simp
    | tensor x y hx hy =>
      dsimp
      simp only [liftNatTrans_app_tensor, Category.assoc, Functor.Monoidal.μ_δ_assoc,
        tensorHom_comp_tensorHom_assoc, ← NatTrans.comp_app, hx, hy]
      simp

section

variable
    {D : Type*} [Category D] [MonoidalCategory D] [SymmetricCategory D]
    {G G' : FreeSymmetricMonoidalCategory C ⥤ D}
    [G.Braided] [G'.Braided]
    (e : ∀ c : C, G.obj (of c) ≅ G'.obj (of c))

@[simp, reassoc]
lemma liftNatIso_hom_app_unit :
    (liftNatIso e).hom.app (𝟙_ (F C)) = (Functor.OplaxMonoidal.η G) ≫ (Functor.LaxMonoidal.ε G') :=
  (rfl)

@[simp, reassoc]
lemma liftNatIso_inv_app_unit :
    (liftNatIso e).inv.app (𝟙_ (F C)) = (Functor.OplaxMonoidal.η G') ≫ (Functor.LaxMonoidal.ε G) :=
  (rfl)

@[simp]
lemma liftNatIso_hom_app_of (c : C) : (liftNatIso e).hom.app (of c) = (e c).hom := (rfl)

@[simp]
lemma liftNatIso_inv_app_of (c : C) : (liftNatIso e).inv.app (of c) = (e c).inv := (rfl)

@[simp, reassoc]
lemma liftNatIso_hom_app_tensor (x y : F C) :
    (liftNatIso e).hom.app (x ⊗ y) =
    (Functor.OplaxMonoidal.δ G x y) ≫
      ((liftNatIso e |>.hom.app x) ⊗ₘ (liftNatIso e |>.hom.app y)) ≫
      (Functor.LaxMonoidal.μ G' x y) := (rfl)

@[simp, reassoc]
lemma liftNatIso_inv_app_tensor (x y : F C) :
    (liftNatIso e).inv.app (x ⊗ y) =
    (Functor.OplaxMonoidal.δ G' x y) ≫
      ((liftNatIso e |>.inv.app x) ⊗ₘ (liftNatIso e |>.inv.app y)) ≫
      (Functor.LaxMonoidal.μ G x y) := (rfl)

instance : (liftNatIso e).hom.IsMonoidal := by
  dsimp [liftNatIso]
  infer_instance

instance : (liftNatIso e).inv.IsMonoidal := by
  dsimp [liftNatIso]
  infer_instance

end

section

lemma ext_of_monoidal
    {D : Type*} [Category D] [MonoidalCategory D] [SymmetricCategory D]
    {G G' : FreeSymmetricMonoidalCategory C ⥤ D}
    [G.Braided] [G'.LaxBraided]
    {η η' : G ⟶ G'} [η.IsMonoidal] [η'.IsMonoidal]
    (h : ∀ (x : C), η.app (of x) = η'.app (of x)) :
    η = η' := by
  ext x
  induction x with
  | of c => exact h c
  | unit =>
    dsimp
    simp [← cancel_epi (Functor.LaxMonoidal.ε G)]
  | tensor x y hx hy =>
    dsimp
    simp [← cancel_epi (Functor.LaxMonoidal.μ G x y), hx, hy]

end

end NatTrans

end

end FreeSymmetricMonoidalCategory

end CategoryTheory
