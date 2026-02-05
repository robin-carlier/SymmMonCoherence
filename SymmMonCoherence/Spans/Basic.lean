/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-! # Bicategories of spans in a category

In this file, given a category `C` and two morphism properties
Wₗ Wᵣ in C satisfying suitable assumptions regarding identities and base changes,
we construt the bicategory of spans in C with left morphism in Wᵣ and right morphism
in Wₗ.

-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C]
    (Wₗ : MorphismProperty C)
    (Wᵣ : MorphismProperty C)

/-- A (Wₗ, Wᵣ)-span from c to c' is the data of an
object `a : C`, together with a morphism `a ⟶ c` in Wₗ,
and a morphism `a ⟶ c'` in Wᵣ -/
structure Span (c c' : C) where
  /- The "apex" of the span -/
  apex : C
  /- The left map -/
  l : apex ⟶ c
  /- The right map -/
  r : apex ⟶ c'
  wl : Wₗ l
  wr : Wᵣ r

namespace Span

variable {Wₗ Wᵣ} {c c' : C}

/-- A morphism of span is a morphism betwen the apices compatible
with the projections. -/
structure Hom (S₁ S₂ : Span Wₗ Wᵣ c c') : Type _ where
  hom : S₁.apex ⟶ S₂.apex
  hom_l : hom ≫ S₂.l = S₁.l := by cat_disch
  hom_r : hom ≫ S₂.r = S₁.r := by cat_disch

attribute [reassoc (attr := simp)] Hom.hom_l Hom.hom_r
attribute [grind =] Hom.hom_l Hom.hom_r

@[simps!]
instance : Category (Span Wₗ Wᵣ c c') where
  Hom := Hom
  comp φ φ' := { hom := φ.hom ≫ φ'.hom }
  id S := { hom := 𝟙 _ }

attribute [grind =] id_hom comp_hom

attribute [local ext] Hom in
@[local ext, local grind ext]
lemma hom_ext {S S' : Span Wₗ Wᵣ c c'} {f g : S ⟶ S'} (h : f.hom = g.hom) :
    f = g := by
  change S.Hom S' at f g
  change @Eq (S.Hom S') _ _
  ext
  exact h

set_option mathlib.tactic.category.grind true in
@[simps]
def mkIso {S S' : Span Wₗ Wᵣ c c'} (e : S.apex ≅ S'.apex)
    (hₗ : e.hom ≫ S'.l = S.l := by cat_disch)
    (hᵣ : e.hom ≫ S'.r = S.r := by cat_disch) :
    S ≅ S' where
  hom.hom := e.hom
  inv.hom := e.inv

attribute [grind =] mkIso_hom_hom mkIso_inv_hom

section MorphismProperty
-- TODO: need to be upstreamed and moved elsewhere

/-- `P.IsStableUnderBaseChangeAgainst P'` states that for any morphism `f`satisfying `P` and
any morphism `g` with the same codomain as `f` satisfying `P'`, any pullback of `f` along `g`
also satisfies `P`. -/
class _root_.CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst
    (P P' : MorphismProperty C) : Prop where
  isStableUnderBaseChangeAlong ⦃X Y : C ⦄ (f : X ⟶ Y) (hf : P' f) :
    P.IsStableUnderBaseChangeAlong f

instance (P : MorphismProperty C) [P.IsStableUnderBaseChange] (P' : MorphismProperty C) :
    P.IsStableUnderBaseChangeAgainst P' where
  isStableUnderBaseChangeAlong := inferInstance

lemma _root_.CategoryTheory.MorphismProperty.isStableUnderBaseChangeAgainst_top_iff
    (P : MorphismProperty C) :
    P.IsStableUnderBaseChangeAgainst ⊤ ↔ P.IsStableUnderBaseChange :=
  ⟨ fun h ↦ ⟨fun {_ _ _ _} _ _ _ _ h' h'' ↦
      (h.isStableUnderBaseChangeAlong _ (by tauto)).of_isPullback h' h''⟩,
    fun _ ↦ inferInstance⟩

/-- `P.IsStableUnderBaseChangeAgainst P'` states that for any morphism `f`satisfying `P` and
any morphism `g` with the same codomain as `f` satisfying `P'`, any pullback of `f` along `g`
also satisfies `P`. -/
class _root_.CategoryTheory.MorphismProperty.HasPullbacksAgainst
    (P P' : MorphismProperty C) : Prop where
  hasPullbacksAlong ⦃X Y : C ⦄ (f : X ⟶ Y) (hf : P' f) :
    P.HasPullbacksAlong f

instance (P : MorphismProperty C) [P.HasPullbacks] (P' : MorphismProperty C) :
    P.HasPullbacksAgainst P' where
  hasPullbacksAlong := inferInstance

lemma _root_.CategoryTheory.MorphismProperty.HasPullbacksAgainst_top_iff
    (P : MorphismProperty C) :
    P.IsStableUnderBaseChangeAgainst ⊤ ↔ P.IsStableUnderBaseChange :=
  ⟨ fun h ↦ ⟨fun {_ _ _ _} _ _ _ _ h' h'' ↦
      (h.isStableUnderBaseChangeAlong _ (by tauto)).of_isPullback h' h''⟩,
    fun _ ↦ inferInstance⟩

lemma _root_.CategoryTheory.Limits.hasPullback_ofHasPullbacksAgainst
    {P : MorphismProperty C} {P' : MorphismProperty C} {c c' c'' : C}
    {f : c ⟶ c'} {g : c'' ⟶ c'} [P.HasPullbacksAgainst P'] (hf : P f) (hg : P' g) :
    Limits.HasPullback f g :=
  letI : P.HasPullbacksAlong g :=
    MorphismProperty.HasPullbacksAgainst.hasPullbacksAlong g hg
  MorphismProperty.HasPullbacksAlong.hasPullback f hf

end MorphismProperty

section bicategory
variable [Wₗ.ContainsIdentities] [Wᵣ.ContainsIdentities] [Wₗ.HasPullbacksAgainst Wᵣ]
    [Wₗ.IsStableUnderBaseChangeAgainst Wᵣ] [Wᵣ.IsStableUnderBaseChangeAgainst Wₗ]
    [Wₗ.IsStableUnderComposition] [Wᵣ.IsStableUnderComposition]

instance {c c' c'' : C}
    (S₁ : Span Wₗ Wᵣ c c') (S₂ : Span Wₗ Wᵣ c' c'') :
    Limits.HasPullback S₁.r S₂.l :=
  letI : Limits.HasPullback S₂.l S₁.r :=
    Limits.hasPullback_ofHasPullbacksAgainst S₂.wl S₁.wr
  Limits.hasPullback_symmetry _ _

instance (S₁ : Span Wₗ Wᵣ c c') : Wₗ.IsStableUnderBaseChangeAlong S₁.r :=
  MorphismProperty.IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong _ S₁.wr

instance (S₁ : Span Wₗ Wᵣ c c') : Wᵣ.IsStableUnderBaseChangeAlong S₁.l :=
  MorphismProperty.IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong _ S₁.wl

/-- The identity span, where both legs are identity morphisms. -/
@[simps]
def id (c : C) :
    Span Wₗ Wᵣ c c where
  apex := c
  l := 𝟙 _
  r := 𝟙 _
  wl := MorphismProperty.ContainsIdentities.id_mem _
  wr := MorphismProperty.ContainsIdentities.id_mem _

/-- The composition of two spans: if the relevant pullback exists and if the
morphism properties are stable under the relevant base change, it is given by the span
```
<MISSING DIAGRAM>
```
-/
@[simps]
noncomputable def comp {c c' c'' : C}
    (S₁ : Span Wₗ Wᵣ c c') (S₂ : Span Wₗ Wᵣ c' c'') :
    Span Wₗ Wᵣ c c'' :=
  { apex := Limits.pullback S₁.r S₂.l
    l := Limits.pullback.fst S₁.r S₂.l ≫ S₁.l
    r := Limits.pullback.snd S₁.r S₂.l ≫ S₂.r
    wl :=
      MorphismProperty.IsStableUnderComposition.comp_mem
        _ _ (MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback
        (.flip <| .of_hasPullback S₁.r S₂.l) S₂.wl) S₁.wl
    wr :=
      MorphismProperty.IsStableUnderComposition.comp_mem
      _ _ (MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback
        (.of_hasPullback S₁.r S₂.l) S₁.wr) S₂.wr }

end bicategory

end Span

variable (C) in
structure Spans (Wₗ Wᵣ : MorphismProperty C) : Type _ where of : C

variable [Wₗ.ContainsIdentities] [Wᵣ.ContainsIdentities] [Wₗ.HasPullbacksAgainst Wᵣ]
    [Wₗ.IsStableUnderBaseChangeAgainst Wᵣ] [Wᵣ.IsStableUnderBaseChangeAgainst Wₗ]
    [Wₗ.IsStableUnderComposition] [Wᵣ.IsStableUnderComposition]

namespace Spans

noncomputable instance : CategoryStruct (Spans C Wₗ Wᵣ) where
  Hom x y := Span Wₗ Wᵣ x.of y.of
  id x := Span.id x.of
  comp S₁ S₂ := Span.comp S₁ S₂

variable {Wₗ Wᵣ}

@[simp, grind =]
lemma id_apex (X : Spans C Wₗ Wᵣ) : (𝟙 X : X ⟶ X).apex = X.of := rfl

@[simp, grind =]
lemma id_l {X : Spans C Wₗ Wᵣ} : (𝟙 X : X ⟶ X).l = 𝟙 X.of := rfl

@[simp, grind =]
lemma id_r {X : Spans C Wₗ Wᵣ} : (𝟙 X : X ⟶ X).r = 𝟙 X.of := rfl

instance {X Y : Spans C Wₗ Wᵣ} : Category (X ⟶ Y) :=
  inferInstanceAs (Category <| Span Wₗ Wᵣ X.of Y.of)

@[simp, grind =]
lemma hom₂_comp_hom {X Y : Spans C Wₗ Wᵣ} {S S' S'' : X ⟶ Y} (f : S ⟶ S')
    (g : S' ⟶ S'') :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[simp, grind =]
lemma hom₂_id_hom {X Y : Spans C Wₗ Wᵣ} (S : X ⟶ Y) :
    (𝟙 S : S ⟶ S).hom = 𝟙 S.apex := rfl

@[ext, grind ext]
lemma hom₂_ext {X Y : Spans C Wₗ Wᵣ} {S S' : X ⟶ Y} {f g : S ⟶ S'}
    (h : f.hom = g.hom) :
    f = g :=
  Span.hom_ext h

/- Constructor for 1-morphisms in Spans C -/
abbrev mkHom {X Y : Spans C Wₗ Wᵣ} (apex : C) (l : apex ⟶ X.of) (r : apex ⟶ Y.of)
    (wl : Wₗ l) (wr : Wᵣ r) :
    X ⟶ Y where
  apex := apex
  l := l
  r := r
  wl := wl
  wr := wr

-- TODO: (lowprio): set up a delaborator for mkHom so that it appears nicely in the pretty printer

/- Constructor for 2-morphisms in Spans C -/
@[simps]
def mkHom₂ {X Y : Spans C Wₗ Wᵣ} {S S' : X ⟶ Y}
    (e : S.apex ⟶ S'.apex)
    (hₗ : e ≫ S'.l = S.l := by cat_disch)
    (hᵣ : e ≫ S'.r = S.r := by cat_disch) :
    S ⟶ S' where
  hom := e

/- Constructor for 2-isomorphisms in Spans C -/
abbrev mkIso₂ {X Y : Spans C Wₗ Wᵣ} {S S' : X ⟶ Y}
    (e : S.apex ≅ S'.apex)
    (hₗ : e.hom ≫ S'.l = S.l := by cat_disch)
    (hᵣ : e.hom ≫ S'.r = S.r := by cat_disch) :
    S ≅ S' where
  hom.hom := e.hom
  inv.hom := e.inv
  inv.hom_l := by grind
  inv.hom_r := by grind

section compAPI
/-! The goal of this section is to abstract as much as possible the fact that the
composition uses an arbitrary pullback, and provides some "proxy" for working
with the fact that apices of compositions of spans are pullbacks.

This way, if spans ever get refactored in a way that use chosen pullbacks instead
of arbitrary ones, most of downstream applications will not be affected
as long as they are careful to use the API provided here.

The "primitives" of this API is the data of the two projections
`πₗ : (S₁ ≫ S₂).apex ⟶ S₁.apex` and `πᵣ : (S₁ ≫ S₂).apex ⟶ S₂.apex`, the
equalities `(S₁ ≫ S₂).l = πₗ ≫ S₁.l` and `(S₁ ≫ S₂).r = πᵣ ≫ S₂.r`,
the commutative square `πₗ ≫ S₁.r = πᵣ ≫ S₂.l` and the fact that this defines a pullback square. -/

variable {X Y Z : Spans C Wₗ Wᵣ} (S₁ : X ⟶ Y) (S₂ : Y ⟶ Z)

@[no_expose] noncomputable def πₗ :
    (S₁ ≫ S₂).apex ⟶ S₁.apex := Limits.pullback.fst _ _

@[no_expose] noncomputable def πᵣ :
    (S₁ ≫ S₂).apex ⟶ S₂.apex := Limits.pullback.snd _ _

@[simp, reassoc, grind =] lemma comp_l : (S₁ ≫ S₂).l = πₗ S₁ S₂ ≫ S₁.l := (rfl)

@[simp, reassoc, grind =] lemma comp_r : (S₁ ≫ S₂).r = πᵣ S₁ S₂ ≫ S₂.r := (rfl)

@[reassoc (attr := simp), grind _=_] lemma comp_comm : πₗ S₁ S₂ ≫ S₁.r = πᵣ S₁ S₂ ≫ S₂.l :=
  Limits.pullback.condition

/-- The pullback cone that defines the apex for the composition of spans. -/
@[simps! (attr := grind =) pt]
noncomputable def compPullbackCone :
    Limits.PullbackCone S₁.r S₂.l :=
  Limits.PullbackCone.mk (πₗ _ _) (πᵣ _ _) (comp_comm _ _)

@[simp, grind =]
lemma compPullbackCone_fst :
  (compPullbackCone S₁ S₂).fst = πₗ S₁ S₂ := rfl

@[simp, grind =]
lemma compPullbackCone_snd :
  (compPullbackCone S₁ S₂).snd = πᵣ S₁ S₂ := rfl

/-- The pullback cone that defines the apex for the composition of spans is a limit
cone. -/
@[no_expose] noncomputable def isLimitCompPullbackCone :
    Limits.IsLimit (compPullbackCone S₁ S₂) :=
  Limits.PullbackCone.IsLimit.mk (comp_comm S₁ S₂)
    (fun x ↦ Limits.pullback.lift x.fst x.snd x.condition)
    (fun x ↦ by simp [πₗ])
    (fun x ↦ by simp [πᵣ])
    (fun f g h k ↦ by apply Limits.pullback.hom_ext <;> cat_disch)

variable {S₁ S₂}

@[ext high, grind ext]
lemma comp_hom_ext_apex {c : C} {f g : c ⟶ (S₁ ≫ S₂).apex}
    (hₗ : f ≫ πₗ S₁ S₂ = g ≫ πₗ S₁ S₂)
    (hᵣ : f ≫ πᵣ S₁ S₂ = g ≫ πᵣ S₁ S₂) :
    f = g := by
  apply Limits.PullbackCone.IsLimit.hom_ext (isLimitCompPullbackCone S₁ S₂) <;> grind

/-- A restatement of the universal property of (S₁ ≫ S₂).apex as coming from a pullback.
This is the main intended way to produce morphisms towards the apex of a composition of spans. -/
noncomputable def compLiftApex {c : C} (fₗ : c ⟶ S₁.apex) (fᵣ : c ⟶ S₂.apex)
    (hₘ : fₗ ≫ S₁.r = fᵣ ≫ S₂.l := by cat_disch) :
    c ⟶ (S₁ ≫ S₂).apex :=
  Limits.PullbackCone.IsLimit.lift (isLimitCompPullbackCone S₁ S₂) fₗ fᵣ hₘ

@[reassoc (attr := simp), grind =]
lemma compLiftApex_πₗ {c : C} (fₗ : c ⟶ S₁.apex) (fᵣ : c ⟶ S₂.apex)
    (hₘ : fₗ ≫ S₁.r = fᵣ ≫ S₂.l := by cat_disch) :
    compLiftApex fₗ fᵣ hₘ ≫ πₗ S₁ S₂ = fₗ := by
  simp [← compPullbackCone_fst, compLiftApex]

@[reassoc (attr := simp), grind =]
lemma compLiftApex_πᵣ {c : C} (fₗ : c ⟶ S₁.apex) (fᵣ : c ⟶ S₂.apex)
    (hₘ : fₗ ≫ S₁.r = fᵣ ≫ S₂.l := by cat_disch) :
    compLiftApex fₗ fᵣ hₘ ≫ πᵣ S₁ S₂ = fᵣ := by
  simp [← compPullbackCone_snd, compLiftApex]

/-- A restatement of the universal property of S₁ ≫ S₂ as coming from a pullback.
This is the main intended way to produce morphisms towards a composition of spans. -/
@[simps (attr := grind =)]
noncomputable def compLift {S : X ⟶ Z} (fₗ : S.apex ⟶ S₁.apex) (fᵣ : S.apex ⟶ S₂.apex)
    (hₗ : fₗ ≫ S₁.l = S.l := by cat_disch)
    (hₘ : fₗ ≫ S₁.r = fᵣ ≫ S₂.l := by cat_disch)
    (hᵣ : fᵣ ≫ S₂.r = S.r := by cat_disch) :
    S ⟶ (S₁ ≫ S₂) where
  hom := compLiftApex fₗ fᵣ

section

variable (S : X ⟶ Z) (fₗ : S.apex ⟶ S₁.apex) (fᵣ : S.apex ⟶ S₂.apex)

lemma compLift_hom_πₗ
    (hₗ : fₗ ≫ S₁.l = S.l := by cat_disch)
    (hₘ : fₗ ≫ S₁.r = fᵣ ≫ S₂.l := by cat_disch)
    (hᵣ : fᵣ ≫ S₂.r = S.r := by cat_disch) :
    (compLift fₗ fᵣ hₗ hₘ hᵣ).hom ≫ πₗ S₁ S₂ = fₗ := by
  simp

lemma compLift_hom_πᵣ
    (hₗ : fₗ ≫ S₁.l = S.l := by cat_disch)
    (hₘ : fₗ ≫ S₁.r = fᵣ ≫ S₂.l := by cat_disch)
    (hᵣ : fᵣ ≫ S₂.r = S.r := by cat_disch) :
    (compLift fₗ fᵣ hₗ hₘ hᵣ).hom ≫ πᵣ S₁ S₂ = fᵣ := by
  simp

end

end compAPI

/-- The associator isomorphisms for the bicategory structure on spans -/
noncomputable def associator
    {c₁ c₂ c₃ c₄ : Spans C Wₗ Wᵣ}
    (S₁ : c₁ ⟶ c₂) (S₂ : c₂ ⟶ c₃) (S₃ : c₃ ⟶ c₄) :
    (S₁ ≫ S₂) ≫ S₃ ≅ S₁ ≫ (S₂ ≫ S₃) where
  hom := compLift (πₗ .. ≫ πₗ ..) (compLiftApex (πₗ .. ≫ πᵣ ..) (πᵣ ..) (by grind))
  inv := compLift (compLiftApex (πₗ ..) (πᵣ .. ≫ πₗ ..)) (πᵣ .. ≫ πᵣ ..)

noncomputable def rightUnitor {c c' : Spans C Wₗ Wᵣ} (S₁ : c ⟶ c') :
    S₁ ≫ (𝟙 c') ≅ S₁ where
  hom.hom := πₗ _ _
  inv := compLift (𝟙 _) S₁.r

noncomputable def leftUnitor {c c' : Spans C Wₗ Wᵣ} (S₁ : c ⟶ c') :
    (𝟙 c) ≫ S₁ ≅ S₁ where
  hom.hom := πᵣ _ S₁
  hom.hom_l := by grind
  inv := compLift S₁.l (𝟙 _)
  hom_inv_id := by grind

attribute [local ext] Span.hom_ext in
/- @[simps] lemmas generated by this instance are unfortunately very poor, and we must
register them by hand as we do below. -/
noncomputable instance : Bicategory (Spans C Wₗ Wᵣ) where
  homCategory := inferInstance
  whiskerLeft {_ _ _} S₀ {S₁ S₂} f := compLift (πₗ ..) (πᵣ .. ≫ f.hom)
  whiskerRight {_ _ _} {S₀ S₁} f S₂ := compLift (πₗ .. ≫ f.hom) (πᵣ ..)
  associator S₀ S₁ S₂ := associator _ _ _
  leftUnitor _ := leftUnitor _
  rightUnitor _ := rightUnitor _
  id_whiskerLeft := by grind [leftUnitor]
  whiskerRight_id := by grind [rightUnitor]
  comp_whiskerLeft := by grind (ematch := 10) [associator]
  whiskerRight_comp := by grind (ematch := 10) [associator]
  whisker_assoc := by
    intros
    ext <;> simp [associator]
  pentagon := by
    intros
    ext <;> simp [associator]
  triangle := by
    intros
    ext <;> simp [associator, leftUnitor, rightUnitor]

open CategoryTheory.Bicategory

@[reassoc (attr := simp), grind =]
lemma whiskerLeft_hom_πₗ {X Y Z : Spans C Wₗ Wᵣ} (S : X ⟶ Y) {S₁ S₂ : Y ⟶ Z} (f : S₁ ⟶ S₂) :
    (S ◁ f).hom ≫ πₗ .. = πₗ .. := by simp [whiskerLeft]

@[reassoc (attr := simp), grind =]
lemma whiskerLeft_hom_πᵣ {X Y Z : Spans C Wₗ Wᵣ} (S : X ⟶ Y) {S₁ S₂ : Y ⟶ Z} (f : S₁ ⟶ S₂) :
    (S ◁ f).hom ≫ πᵣ .. = πᵣ .. ≫ f.hom := by simp [whiskerLeft]

@[reassoc (attr := simp), grind =]
lemma whiskerRight_hom_πₗ {X Y Z : Spans C Wₗ Wᵣ} {S₁ S₂ : X ⟶ Y} (f : S₁ ⟶ S₂) (S : Y ⟶ Z) :
    (f ▷ S).hom ≫ πₗ .. = (πₗ .. ≫ f.hom) := by simp [whiskerRight]

@[reassoc (attr := simp), grind =]
lemma whiskerRight_hom_πᵣ {X Y Z : Spans C Wₗ Wᵣ} {S₁ S₂ : X ⟶ Y} (f : S₁ ⟶ S₂) (S : Y ⟶ Z) :
    (f ▷ S).hom ≫ πᵣ .. = πᵣ .. := by simp [whiskerRight]

@[reassoc (attr := simp), grind =]
lemma associator_hom_hom_πₗ {W X Y Z : Spans C Wₗ Wᵣ} (S₁ : W ⟶ X) (S₂ : X ⟶ Y) (S₃ : Y ⟶ Z) :
    (α_ S₁ S₂ S₃).hom.hom ≫ πₗ .. = πₗ .. ≫ πₗ .. := by
  simp [Bicategory.associator, Spans.associator]

@[reassoc (attr := simp), grind =]
lemma associator_hom_hom_πᵣ_πₗ {W X Y Z : Spans C Wₗ Wᵣ} (S₁ : W ⟶ X) (S₂ : X ⟶ Y) (S₃ : Y ⟶ Z) :
    (α_ S₁ S₂ S₃).hom.hom ≫ πᵣ .. ≫ πₗ .. = πₗ .. ≫ πᵣ .. := by
  simp [Bicategory.associator, Spans.associator]

@[reassoc (attr := simp), grind =]
lemma associator_hom_hom_πᵣ_πᵣ {W X Y Z : Spans C Wₗ Wᵣ} (S₁ : W ⟶ X) (S₂ : X ⟶ Y) (S₃ : Y ⟶ Z) :
    (α_ S₁ S₂ S₃).hom.hom ≫ πᵣ .. ≫ πᵣ .. = πᵣ .. := by
  simp [Bicategory.associator, Spans.associator]

@[reassoc (attr := simp), grind =]
lemma associator_inv_hom_πᵣ {W X Y Z : Spans C Wₗ Wᵣ} (S₁ : W ⟶ X) (S₂ : X ⟶ Y) (S₃ : Y ⟶ Z) :
    (α_ S₁ S₂ S₃).inv.hom ≫ πᵣ .. = πᵣ .. ≫ πᵣ .. := by
  simp [Bicategory.associator, Spans.associator]

@[reassoc (attr := simp), grind =]
lemma associator_inv_hom_πₗ_πₗ {W X Y Z : Spans C Wₗ Wᵣ} (S₁ : W ⟶ X) (S₂ : X ⟶ Y) (S₃ : Y ⟶ Z) :
    (α_ S₁ S₂ S₃).inv.hom ≫ πₗ .. ≫ πₗ .. = πₗ .. := by
  simp [Bicategory.associator, Spans.associator]

@[reassoc (attr := simp), grind =]
lemma associator_inv_hom_πₗ_πᵣ {W X Y Z : Spans C Wₗ Wᵣ} (S₁ : W ⟶ X) (S₂ : X ⟶ Y) (S₃ : Y ⟶ Z) :
    (α_ S₁ S₂ S₃).inv.hom ≫ πₗ .. ≫ πᵣ .. = πᵣ .. ≫ πₗ .. := by
  simp [Bicategory.associator, Spans.associator]

@[simp, grind =]
lemma leftUnitor_hom_hom {X Y : Spans C Wₗ Wᵣ} (S : X ⟶ Y) :
    (λ_ S).hom.hom = πᵣ .. := rfl

@[simp, grind =]
lemma leftUnitor_inv_hom_πₗ {X Y : Spans C Wₗ Wᵣ} (S : X ⟶ Y) :
    (λ_ S).inv.hom ≫ πₗ .. = S.l := by simp [Bicategory.leftUnitor, leftUnitor]

@[simp, grind =]
lemma leftUnitor_inv_hom_πᵣ {X Y : Spans C Wₗ Wᵣ} (S : X ⟶ Y) :
    (λ_ S).inv.hom ≫ πᵣ .. = 𝟙 _ := by simp [Bicategory.leftUnitor, leftUnitor]

@[simp, grind =]
lemma rightUnitor_hom_hom {X Y : Spans C Wₗ Wᵣ} (S : X ⟶ Y) :
    (ρ_ S).hom.hom = πₗ .. := rfl

@[reassoc (attr := simp), grind =]
lemma rightUnitor_inv_hom_πₗ {X Y : Spans C Wₗ Wᵣ} (S : X ⟶ Y) :
    (ρ_ S).inv.hom ≫ πₗ .. = 𝟙 _ := by simp [Bicategory.rightUnitor, rightUnitor]

@[reassoc (attr := simp), grind =]
lemma rightUnitor_inv_hom_πᵣ {X Y : Spans C Wₗ Wᵣ} (S : X ⟶ Y) :
    (ρ_ S).inv.hom ≫ πᵣ .. = S.r := by simp [Bicategory.rightUnitor, rightUnitor]

@[reassoc (attr := simp), grind =]
lemma hom_inv_id_hom {X Y : Spans C Wₗ Wᵣ} {S S' : X ⟶ Y} (e : S ≅ S') :
    e.hom.hom ≫ e.inv.hom = 𝟙 _ := by simp [← hom₂_comp_hom]

@[reassoc (attr := simp), grind =]
lemma inv_hom_id_hom {X Y : Spans C Wₗ Wᵣ} {S S' : X ⟶ Y} (e : S ≅ S') :
    e.inv.hom ≫ e.hom.hom = 𝟙 _ := by simp [← hom₂_comp_hom]

/-- extract the isomorphisms between the apices from the data of an isomorphisms of 1-morphisms
in `Spans C _ _. -/
@[simps]
abbrev apexIso {X Y : Spans C Wₗ Wᵣ} {S S' : X ⟶ Y} (e : S ≅ S') :
    S.apex ≅ S'.apex where
  hom := e.hom.hom
  inv := e.inv.hom

@[simp]
lemma apexIso_refl {X Y : Spans C Wₗ Wᵣ} (S : X ⟶ Y) : apexIso (Iso.refl S) = .refl _ := rfl

instance {X Y : Spans C Wₗ Wᵣ} {S S' : X ⟶ Y} (e : S ⟶ S') [IsIso e] : IsIso e.hom :=
  ⟨(inv e).hom, by simp [← hom₂_comp_hom]⟩

@[simp, push ←]
lemma inv_hom {X Y : Spans C Wₗ Wᵣ} {S S' : X ⟶ Y} (e : S ⟶ S') [IsIso e] :
    (inv e).hom = inv e.hom := by
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← hom₂_comp_hom]

lemma eqToHom_hom {X Y : Spans C Wₗ Wᵣ} (S S' : X ⟶ Y) (h : S = S') :
    (eqToHom h).hom = eqToHom (congr($(h).apex)) := by
  subst h
  simp

instance {X : Spans C Wₗ Wᵣ} : IsIso (𝟙 X:).r := by dsimp; infer_instance

instance {X : Spans C Wₗ Wᵣ} : IsIso (𝟙 X:).l := by dsimp; infer_instance

instance {X Y : Spans C Wₗ Wᵣ} (S : X ⟶ Y) : IsIso (πᵣ (𝟙 _) S) := by
  have := IsPullback.isIso_snd_of_isIso
    (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone (𝟙 _) S)
  exact this

instance {X Y : Spans C Wₗ Wᵣ} (S : X ⟶ Y) : IsIso (πₗ S (𝟙 _)) :=
  by
  have := IsPullback.isIso_fst_of_isIso
    (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone S (𝟙 _))
  exact this

section projections

/-- Forget the right leg of a span. -/
@[simps!]
def toOverLeft (X Y : Spans C Wₗ Wᵣ) : (X ⟶ Y) ⥤ Over X.of where
  obj S := Over.mk S.l
  map f := Over.homMk f.hom

/-- Forget the left leg of a span. -/
@[simps!]
def toOverRight (X Y : Spans C Wₗ Wᵣ) : (X ⟶ Y) ⥤ Over Y.of where
  obj S := Over.mk S.r
  map f := Over.homMk f.hom

/-- Forget both legs of a span. -/
@[simps!]
def forgetLegs (X Y : Spans C Wₗ Wᵣ) : (X ⟶ Y) ⥤ C where
  obj S := S.apex
  map f := f.hom

/-- Forgetting both legs is the same as forgetting the left leg,
then forgetting the rest. -/
@[simps!]
def toOverLeftForgetIso (X Y : Spans C Wₗ Wᵣ) :
    toOverLeft X Y ⋙ Over.forget _ ≅ forgetLegs _ _ :=
  .refl _

/-- Forgetting both legs is the same as forgetting the right leg,
then forgetting the rest. -/
@[simps!]
def toOverRightForgetIso (X Y : Spans C Wₗ Wᵣ) :
    toOverRight X Y ⋙ Over.forget _ ≅ forgetLegs _ _ :=
  .refl _

end projections

end Spans

end CategoryTheory
