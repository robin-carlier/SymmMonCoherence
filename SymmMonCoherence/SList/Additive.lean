/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.Equivalence
public import SymmMonCoherence.SList.Multiset
public import SymmMonCoherence.SList.EffBurnside
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Data.FinEnum
public import Mathlib.CategoryTheory.Pi.Monoidal
public import SymmMonCoherence.ForMathlib.CategoryTheory.Pi.IsEquivalence
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.FintypeCat

/-!
# Additivity of symmetric lists.

In this file, we construct a symmetric monoidal equivalence of categories between
SList K and `K → SList Unit` when `K : Type _` is a finite type.

-/

@[expose] public noncomputable section

namespace CategoryTheory.SList

open MonoidalCategory

universe u

variable {K : Type*}
section fiber

abbrev fiber (k : K) (L : SList K) : Type _ :=
  { i : Fin L.length // L.toList[i] = k }

@[simp, grind =]
lemma fiber_prop (k : K) (L : SList K) (i : fiber k L) :
    L.toList[(i.val : ℕ)] = k :=
  i.prop

@[simp, grind =]
lemma fiber_prop' (k : K) (L : SList K) (i : fiber k L) :
    L.toList[i.val] = k :=
  i.prop
-- def fiberInclusion (k : K) (L : SList K) : fiber k L → Fin L.length := Subtype.val

/-- Given a morphism of symmetric lists with values in K, and an element `k : K`, this
is the equivalence between the types of elements lying over a given value of `K`. -/
@[simps apply symm_apply]
def fiberEquivOfHom (k : K) {L L' : SList K} (f : L ⟶ L') :
    (fiber k L') ≃ (fiber k L) where
  toFun i := ⟨toEquiv f i.val, by
    have := i.property
    simp only [Fin.getElem_fin] at this
    -- simp only [indexSet, Finset.mem_filter] at this
    simpa [this] using (getElem_toList_toEquiv f i.val).symm ⟩
  invFun i := ⟨(toEquiv f).symm i.val, by
    have := i.property
    convert this using 1
    convert (getElem_toList_toEquiv (inv f) i.val).symm using 1
    congr 1
    simp [← toEquiv_symm]⟩
  left_inv _ := by simp
  right_inv _ := by simp

-- variable [DecidableEq K]

open scoped Classical in
@[simp]
lemma fiber_card (k : K) (L : SList K) :
    Fintype.card (fiber k L) = L.toList.count k := by
  induction L using SList.cons_induction with
  | nil =>
    simp only [fiber, nil_toList, Fin.getElem_fin, List.count_nil, Fintype.card_eq_zero_iff]
    constructor
    intro i
    have := i.val
    simp only [length_nil] at this
    exact Fin.elim0 this
  | cons x L ih =>
    simp only [fiber, cons_toList, Fin.getElem_fin, List.getElem_cons, dite_eq_iff, exists_prop,
      List.count_cons, ← ih, beq_iff_eq]
    rw [Fintype.card_subtype_or_disjoint]
    · rw [add_comm]
      congr 1
      · rw [Fintype.card_eq]
        exact ⟨{
          toFun x := ⟨⟨x.val - 1, by grind⟩, by obtain ⟨_, h⟩ := x.property; simpa using h⟩
          invFun x := ⟨Φ _ _ <| .inr x.val, by simp⟩
          left_inv t := by
            ext
            grind
          right_inv t := by
            ext
            grind }⟩
      · split_ifs with h
        · subst h
          rw [Fintype.card_of_subtype (s := {⟨0, by simp⟩})] <;> grind
        · rw [Fintype.card_of_subtype (s := ∅)] <;> grind
    · simp only [Pi.disjoint_iff, «Prop».disjoint_iff, not_and, not_exists, and_imp]
      grind

open scoped Classical in
lemma fiber_card' (k : K) (L : SList K) :
    Nat.card (fiber k L) = L.toList.count k := by
  simp

end fiber

section Pi
/- Generalities on categories of the form `K → SList J`. -/
variable {J : Type*}

abbrev Tot (X : K → SList J) : Type _ := (k : K) × Fin (X k).length

-- open scoped Classical in
-- abbrev Tot'' (X : SList K) : Type _ := (k : K) × Fin (X.toList.count k)
--
@[simps! (attr := grind =) apply_fst apply_snd symm_apply_fst symm_apply_snd]
def totEquivOfHom {X Y : K → SList J} (f : X ⟶ Y) : Tot Y ≃ Tot X :=
  Equiv.sigmaCongrRight (toEquiv <| f ·)

@[simp, grind =]
lemma totEquivOfHom_apply {X Y : K → SList J} (f : X ⟶ Y)
    (k : K) (i : Fin (Y k).length) :
    totEquivOfHom f ⟨k, i⟩ = ⟨k, toEquiv (f k) i⟩ :=
  rfl

@[simp, grind =]
lemma totEquivOfHom_id (X : K → SList J) : totEquivOfHom (𝟙 X) = .refl _ := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
lemma totEquivOfHom_comp {X Y Z : K → SList J} (f : X ⟶ Y) (g : Y ⟶ Z) :
      totEquivOfHom (f ≫ g) = (totEquivOfHom g).trans (totEquivOfHom f)  := by
  ext <;> simp

lemma totEquivOfHom_comp_apply {X Y Z : K → SList J} (f : X ⟶ Y) (g : Y ⟶ Z) (i : Tot Z) :
      totEquivOfHom (f ≫ g) i = (totEquivOfHom f) ((totEquivOfHom g) i) := by
  simp

def totTensEquiv (X Y : K → SList J) :
    (Tot X) ⊕ (Tot Y) ≃ Tot (X ⊗ Y) :=
  (Equiv.sigmaSumDistrib _ _).symm.trans (Equiv.sigmaCongrRight <| fun _ ↦ Ψ ..)

@[simp, grind =]
lemma totTensEquiv_inl (X Y : K → SList J) (j : Tot X) :
  (totTensEquiv X Y (.inl j)) = ⟨j.fst, Ψ _ _ (.inl j.snd)⟩ := rfl

@[simp, grind =]
lemma totTensEquiv_inr (X Y : K → SList J) (j : Tot Y) :
  (totTensEquiv X Y (.inr j)) = ⟨j.fst, Ψ _ _ (.inr j.snd)⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
lemma totTensEquiv_natural_right (X : K → SList J) {Y Y' : K → SList J} (f : Y ⟶ Y')
    (i : Tot X ⊕ Tot Y') :
    totEquivOfHom (X ◁ f) (totTensEquiv X Y' i) =
      totTensEquiv X Y (Equiv.sumCongr (.refl (Tot X)) (totEquivOfHom f) i) := by
  cases i with
    (simp only [totEquivOfHom, Equiv.sigmaCongrRight_apply, Equiv.sumCongr_apply]
     simp)

set_option backward.isDefEq.respectTransparency false in
lemma totTensEquiv_natural_left (X : K → SList J) {Y Y' : K → SList J} (f : Y ⟶ Y')
    (i : Tot Y' ⊕ Tot X) :
    totEquivOfHom (f ▷ X) (totTensEquiv Y' X i) =
      totTensEquiv Y X (Equiv.sumCongr (totEquivOfHom f) (.refl (Tot X)) i) := by
  cases i with
    (simp only [totEquivOfHom, Equiv.sigmaCongrRight_apply, Equiv.sumCongr_apply]
     simp)

/-- TODO make this instance more general, for pi categories
of IsGroupoid... -/
instance {K : Type*} {X Y : K → SList J} (f : X ⟶ Y) : IsIso f :=
  ⟨fun k ↦ inv (f k), by cat_disch⟩

@[simp]
lemma inv_family {K : Type*} {X Y : K → SList J} (f : X ⟶ Y) :
    (inv <| f · ) = (inv f) := by
  apply IsIso.eq_inv_of_inv_hom_id (f := f)
  cat_disch

@[simp, push]
lemma inv_family_app {K : Type*} {X Y : K → SList J} (f : X ⟶ Y) (k : K) :
    (inv <| f k) = (inv f) k := by
  rw [← inv_family]

@[simp]
lemma totEquivOfHom_symm {X X' : K → SList J} (f : X ⟶ X') :
    (totEquivOfHom f).symm = totEquivOfHom (inv f) := by
  ext i : 1
  simp [totEquivOfHom, Equiv.sigmaCongrRight, toEquiv_symm]

lemma hom_eq_of_totEquivOfHom_eq {X X' : K → SList J} {f g : X ⟶ X'}
    (h : totEquivOfHom f = totEquivOfHom g) :
    f = g := by
  ext k
  rw [hom_eq_iff_toEquiv_eq]
  ext i : 1
  have := congr($h ⟨k, i⟩)
  simpa using this

end Pi

section eval

section Tot'

abbrev Tot' (X : SList K) : Type _ := (k : K) × fiber k X

namespace Tot'

@[simps!]
def tot'Equiv (L : SList K) : Tot' L ≃ Fin L.length :=
  Equiv.sigmaFiberEquiv (L.toList[·])

@[simp, grind =]
lemma tot'Equiv_appy_prop {L : SList K} (x : Tot' L) :
    L.toList[(tot'Equiv L x)] = x.fst := by
  obtain ⟨k, i⟩ := x
  simp

@[simp, grind =]
lemma tot'Equiv_appy_prop' {L : SList K} (x : Tot' L) :
    L.toList[((tot'Equiv L x) : ℕ)] = x.fst := by
  obtain ⟨k, i⟩ := x
  simp

@[simps! (attr := grind =) symm_apply apply]
def tot'EquivOfHom {L L' : SList K} (f : L ⟶ L') : Tot' L' ≃ Tot' L :=
  Equiv.sigmaCongrRight (fiberEquivOfHom · f)

/- The equivalence `Tot' L ⊕ Tot' L' ≃ Tot' (L ⊗ L')` deduced from the equivalence
`Tot' _ ≃ Fin _.length` and the equivalence `finSumTensEquiv` -/
def tot'TensEquiv (L L' : SList K) : Tot' L ⊕ Tot' L' ≃ Tot' (L ⊗ L') :=
  ((Equiv.sumCongr (tot'Equiv L) (tot'Equiv L')).trans (Ψ ..)).trans
    (tot'Equiv _).symm

@[simp, grind =]
lemma tot'TensEquiv_apply_inl (L L' : SList K) (j : Tot' L) :
    (tot'TensEquiv L L' (.inl j)) = ⟨j.fst, ⟨Ψ _ _ (.inl j.snd.val), (by simp)⟩⟩ := by
  simp only [tot'TensEquiv, tot'Equiv, Fin.getElem_fin, Equiv.trans_apply, Equiv.sumCongr_apply]
  ext : 1 <;> simp [Equiv.sigmaFiberEquiv]

@[simp, grind =]
lemma tot'TensEquiv_apply_inr (L L' : SList K) (j : Tot' L') :
  (tot'TensEquiv L L' (.inr j)) = ⟨j.fst, ⟨Ψ _ _ (.inr j.snd.val), (by simp)⟩⟩ := by
  simp only [tot'TensEquiv, tot'Equiv, Fin.getElem_fin, Equiv.trans_apply, Equiv.sumCongr_apply]
  ext : 1 <;> simp [Equiv.sigmaFiberEquiv]

lemma tot'TensEquiv_symm_apply_inl (L L' : SList K) (k : K) (i : Fin L.length)
    (hk : L.toList[i] = k) :
    (tot'TensEquiv L L').symm ⟨k, ⟨Ψ _ _ (.inl i), (by simpa using hk)⟩⟩ =
      .inl ⟨k, ⟨i, hk⟩⟩ := by
  rw [Equiv.symm_apply_eq]
  simp

lemma tot'TensEquiv_symm_apply_inr (L L' : SList K) (k : K) (i : Fin L'.length)
    (hk : L'.toList[i] = k) :
    (tot'TensEquiv L L').symm ⟨k, ⟨Ψ _ _ (.inr i), (by simpa using hk)⟩⟩ =
      .inr ⟨k, ⟨i, hk⟩⟩ := by
  rw [Equiv.symm_apply_eq]
  simp

/- The projection Tot' L ⊕ Tot' L' → K corresponding to the sum of the projections. -/
def π (L L' : SList K) : Tot' L ⊕ Tot' L' → K := Sum.elim (·.fst) (·.fst)

@[simp, grind =] lemma π_inl {L : SList K} (t : Tot' L) (L' : SList K) :
    π L L' (.inl t) = t.fst := rfl

@[simp, grind =] lemma π_inr (L : SList K) {L' : SList K} (t : Tot' L') :
    π L L' (.inr t) = t.fst := rfl

lemma π_eq (L L' : SList K) (t : L.Tot' ⊕ L'.Tot') :
    π L L' t = ((tot'TensEquiv L L') t).fst := by
  cases t with simp

lemma tot'TensEquiv_symm_π (L L' : SList K) (t : Tot' (L ⊗ L')) :
    (π _ _ <| (tot'TensEquiv L L').symm t) = t.fst := by
  obtain ⟨t, rfl⟩ := (tot'TensEquiv L L').surjective t
  simp only [Equiv.symm_apply_apply]
  cases t with simp

def fibπEquiv (L L' : SList K) (k : K) :
    {x : Tot' L ⊕ Tot' L' // π _ _ x = k} ≃ L.fiber k ⊕ L'.fiber k where
  toFun
    | ⟨.inl x, hx⟩ => .inl ⟨x.snd, by simpa using hx⟩
    | ⟨.inr x, hx⟩ => .inr ⟨x.snd, by simpa using hx⟩
  invFun
    | .inl x => ⟨.inl ⟨k, x⟩, by simp⟩
    | .inr x => ⟨.inr ⟨k, x⟩, by simp⟩
  left_inv x := by
    obtain ⟨k, rfl⟩ := x
    cases k with simp
  right_inv x := by
    cases x with simp

@[simp, grind =]
lemma fibπEquiv_inl {L L' : SList K} (k : K) (x : L.Tot') (hx : π L L' (Sum.inl x) = k) :
  fibπEquiv L L' k ⟨.inl x, hx⟩ = .inl ⟨x.snd, by simpa using hx⟩ := rfl

@[simp, grind =]
lemma fibπEquiv_inr {L L' : SList K} (k : K) (x : L'.Tot') (hx : π L L' (Sum.inr x) = k) :
  fibπEquiv L L' k ⟨.inr x, hx⟩ = .inr ⟨x.snd, by simpa using hx⟩ := rfl

@[simp, grind =]
lemma fibπEquiv_symm_inl {L : SList K} (L' : SList K) (k : K) (x : L.fiber k) :
    (fibπEquiv L L' k).symm (.inl x) = ⟨.inl ⟨k, x⟩, by simp⟩ := rfl

@[simp, grind =]
lemma fibπEquiv_symm_inr (L : SList K) {L' : SList K} (k : K) (x : L'.fiber k) :
    (fibπEquiv L L' k).symm (.inr x) = ⟨.inr ⟨k, x⟩, by simp⟩ := rfl

end Tot'

end Tot'

section

open MonoidalCategory

public def fiberTensEquiv (k : K) (L L' : SList K) : L.fiber k ⊕ L'.fiber k ≃ (L ⊗ L').fiber k :=
  Tot'.fibπEquiv L L' k |>.symm.trans <|
    Equiv.subtypeEquiv (Tot'.tot'TensEquiv ..) (fun a ↦ by simp [Tot'.π_eq]) |>.trans <|
    Equiv.sigmaSubtype k (β := fun k ↦ fiber k (L ⊗ L'))

@[simp, grind =]
public lemma fiberTensEquiv_apply_inl (k : K) (L L' : SList K) (x : L.fiber k) :
    (fiberTensEquiv k L L') (.inl x) = ⟨Ψ _ _ (.inl x.val), (by simp)⟩ := by
  simp [fiberTensEquiv]

@[simp, grind =]
public lemma fiberTensEquiv_apply_inr (k : K) (L L' : SList K) (x : L'.fiber k) :
    (fiberTensEquiv k L L') (.inr x) = ⟨Ψ _ _ (.inr x.val), (by simp)⟩ := by
  simp [fiberTensEquiv]

-- leaving `h` as a hole so that it is exactly the right type. -/
@[simp, grind =]
public lemma fiberTensEquiv_symm_apply_inl
      (k : K) (L L' : SList K) (x : Fin L.length) (h' : L.toList[x] = k) :
    (fiberTensEquiv k L L').symm ⟨Ψ _ _ (.inl x), (by simpa using h')⟩ = .inl ⟨x, h'⟩ := by
  rw [Equiv.symm_apply_eq]
  simp

@[simp, grind =]
public lemma fiberTensEquiv_symm_apply_inr
      (k : K) (L L' : SList K) (x : Fin L'.length) (h' : L'.toList[x] = k) :
    (fiberTensEquiv k L L').symm ⟨Ψ _ _ (.inr x), (by simpa using h')⟩ = .inr ⟨x, h'⟩ := by
  rw [Equiv.symm_apply_eq]
  simp

end

section eval₀

/-- Given (k : K) and (L : SList K), `eval₀Obj k L` is the `FintypeGrpd`
corresponding to the fiber of `L` over `k`. -/
abbrev eval₀Obj (k : K) (L : SList K) : FintypeGrpd :=
  .mk <| .of <| fiber k L

/-- Given `(k : K)` and a morphism `f : L ⟶ L'` in `SList K`, `eval₀Map k f` is the
induced morphism on fibers over `k`. -/
abbrev eval₀Map (k : K) {L L' : SList K} (f : L ⟶ L') :
    eval₀Obj k L ⟶ eval₀Obj k L' :=
  FintypeGrpd.mkHom (fiberEquivOfHom k (inv f))

def eval₀ (k : K) : SList K ⥤ FintypeGrpd where
  obj L := eval₀Obj k L
  map {L L'} f := eval₀Map k f
  map_id x := by
    ext i
    dsimp [eval₀Map, eval₀Obj] at i ⊢
    rw [FintypeGrpd.mkHom_iso_hom_apply]
    simp
  map_comp f g := by
    ext i
    dsimp [eval₀Map, eval₀Obj] at i ⊢
    rw [FintypeGrpd.mkHom_iso_hom_apply]
    simp only [IsIso.inv_comp, ConcreteCategory.comp_apply]
    rw [FintypeGrpd.mkHom_iso_hom_apply]
    rw [FintypeGrpd.mkHom_iso_hom_apply]
    simp

-- Set up the usual nice API for eval₀

public irreducible_def eval₀.ι {k : K} {L : SList K} : L.fiber k ≃ (eval₀ k).obj L := .refl _

open eval₀
set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
public lemma eval₀_map_iso_hom_ι (k : K) {L L' : SList K} (f : L ⟶ L') (i : L.fiber k) :
    ((eval₀ k).map f).iso.hom (ι i) = ι (fiberEquivOfHom k (inv f) i) := by
  dsimp [eval₀]
  rw [ι_def, FintypeGrpd.mkHom_iso_hom_apply, ι_def]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
public lemma eval₀_map_iso_inv_ι (k : K) {L L' : SList K} (f : L ⟶ L') (i : L'.fiber k) :
    ((eval₀ k).map f).iso.inv (ι i) = ι (fiberEquivOfHom k f i) := by
  dsimp [eval₀]
  rw [ι_def, FintypeGrpd.mkHom_iso_inv_apply, ι_def]
  simp [fiberEquivOfHom, toEquiv_symm]

open MonoidalCategory

instance (k : K) : IsEmpty <| (eval₀ k).obj (𝟙_ (SList K)) := by
  rw [Equiv.isEmpty_congr eval₀.ι.symm]
  infer_instance

public instance (k : K) : (eval₀ k).Monoidal :=
  letI : (eval₀ k).CoreMonoidal :=
    { εIso := FintypeGrpd.mkIso <| Equiv.equivEmpty _ |>.trans <| (Equiv.equivEmpty _).symm
      μIso X Y :=
        FintypeGrpd.mkIso <|
          FintypeGrpd.tensorObjEquiv _ _ |>.symm.trans <|
            Equiv.sumCongr eval₀.ι.symm eval₀.ι.symm |>.trans <|
              fiberTensEquiv .. |>.trans <|
                eval₀.ι
      μIso_hom_natural_left {X Y} f Z := by
        ext i
        obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
        cases i with
        | inl i =>
          obtain ⟨i, rfl⟩ := eval₀.ι.surjective i
          simp [fiberEquivOfHom]
        | inr i =>
          obtain ⟨i, rfl⟩ := eval₀.ι.surjective i
          simp [fiberEquivOfHom]
      μIso_hom_natural_right X {Y Z} f := by
        ext i
        obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
        cases i with
        | inl i =>
          obtain ⟨i, rfl⟩ := eval₀.ι.surjective i
          simp [fiberEquivOfHom]
        | inr i =>
          obtain ⟨i, rfl⟩ := eval₀.ι.surjective i
          simp [fiberEquivOfHom]
      associativity X Y Z := by
        ext i
        obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
        cases i with
        | inl i =>
          obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
          cases i with
          | inl i =>
            obtain ⟨i, rfl⟩ := eval₀.ι.surjective i
            simp [fiberEquivOfHom]
          | inr i =>
            obtain ⟨i, rfl⟩ := eval₀.ι.surjective i
            simp [fiberEquivOfHom]
        | inr i =>
          obtain ⟨i, rfl⟩ := eval₀.ι.surjective i
          simp [fiberEquivOfHom]
      left_unitality X := by
        ext i
        obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
        cases i with
        | inl i => exfalso; exact IsEmpty.false i
        | inr i =>
          obtain ⟨i, rfl⟩ := eval₀.ι.surjective i
          simp [fiberEquivOfHom]
      right_unitality X := by
        ext i
        obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
        cases i with
        | inl i =>
          obtain ⟨i, rfl⟩ := eval₀.ι.surjective i
          simp [fiberEquivOfHom]
        | inr i => exfalso; exact IsEmpty.false i }
  this.toMonoidal

lemma eval₀_μIso_def (k : K) (X Y : SList K) :
    Functor.Monoidal.μIso (eval₀ k) X Y =
    (FintypeGrpd.mkIso <|
      FintypeGrpd.tensorObjEquiv _ _ |>.symm.trans <|
        Equiv.sumCongr eval₀.ι.symm eval₀.ι.symm |>.trans <|
          fiberTensEquiv .. |>.trans <|
            eval₀.ι) :=
  rfl

@[simp, grind =]
lemma eval₀_μ_hom_left (k : K) (L L' : SList K) (t : L.fiber k) :
    (Functor.LaxMonoidal.μ (eval₀ k) L L').iso.hom (FintypeGrpd.inl _ _ (eval₀.ι t)) =
    eval₀.ι ⟨Ψ _ _ (.inl t.val), (by simp)⟩ := by
  simp [← Functor.Monoidal.μIso_hom, eval₀_μIso_def]

@[simp, grind =]
lemma eval₀_μ_hom_right (k : K) (L L' : SList K) (t : L'.fiber k) :
    (Functor.LaxMonoidal.μ (eval₀ k) L L').iso.hom (FintypeGrpd.inr _ _ (eval₀.ι t)) =
    eval₀.ι ⟨Ψ _ _ (.inr t.val), (by simp)⟩ := by
  simp [← Functor.Monoidal.μIso_hom, eval₀_μIso_def]

@[simp, grind =]
lemma eval₀_δ_hom_left (k : K) (L L' : SList K) (t : L.fiber k) :
    (Functor.OplaxMonoidal.δ (eval₀ k) L L').iso.hom
      (eval₀.ι ⟨Ψ _ _ (.inl t.val), (by simp)⟩) = (FintypeGrpd.inl _ _ (eval₀.ι t)) := by
  simp [← Functor.Monoidal.μIso_inv, eval₀_μIso_def]

@[simp, grind =]
lemma eval₀_δ_hom_right (k : K) (L L' : SList K) (t : L'.fiber k) :
    (Functor.OplaxMonoidal.δ (eval₀ k) L L').iso.hom
      (eval₀.ι ⟨Ψ _ _ (.inr t.val), (by simp)⟩) = (FintypeGrpd.inr _ _ (eval₀.ι t)) := by
  simp [← Functor.Monoidal.μIso_inv, eval₀_μIso_def]

@[simp, grind =]
lemma eval₀_μ_inv_left (k : K) (L L' : SList K) (t : L.fiber k) :
    (Functor.OplaxMonoidal.δ (eval₀ k) L L').iso.inv (FintypeGrpd.inl _ _ (eval₀.ι t)) =
    eval₀.ι ⟨Ψ _ _ (.inl t.val), (by simp)⟩ := by
  simp [← Functor.Monoidal.μIso_inv, eval₀_μIso_def]

@[simp, grind =]
lemma eval₀_μ_inv_right (k : K) (L L' : SList K) (t : L'.fiber k) :
    (Functor.OplaxMonoidal.δ (eval₀ k) L L').iso.inv (FintypeGrpd.inr _ _ (eval₀.ι t)) =
    eval₀.ι ⟨Ψ _ _ (.inr t.val), (by simp)⟩ := by
  simp [← Functor.Monoidal.μIso_inv, eval₀_μIso_def]

@[simp, grind =]
lemma eval₀_δ_inv_left (k : K) (L L' : SList K) (t : L.fiber k) :
    (Functor.LaxMonoidal.μ (eval₀ k) L L').iso.inv
      (eval₀.ι ⟨Ψ _ _ (.inl t.val), (by simp)⟩) = (FintypeGrpd.inl _ _ (eval₀.ι t)) := by
  simp [← Functor.Monoidal.μIso_hom, eval₀_μIso_def]

@[simp, grind =]
lemma eval₀_δ_inv_right (k : K) (L L' : SList K) (t : L'.fiber k) :
    (Functor.LaxMonoidal.μ (eval₀ k) L L').iso.inv
      (eval₀.ι ⟨Ψ _ _ (.inr t.val), (by simp)⟩) = (FintypeGrpd.inr _ _ (eval₀.ι t)) := by
  simp [← Functor.Monoidal.μIso_hom, eval₀_μIso_def]

instance (k : K) : (eval₀ k).Braided where
  braided X Y := by
    ext i
    obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
    cases i with
    | inl i =>
      obtain ⟨i, rfl⟩ := eval₀.ι.surjective i
      simp [fiberEquivOfHom, toEquiv_symm, ← SymmetricCategory.braiding_swap_eq_inv_braiding]
    | inr i =>
      obtain ⟨i, rfl⟩ := eval₀.ι.surjective i
      simp [fiberEquivOfHom, toEquiv_symm, ← SymmetricCategory.braiding_swap_eq_inv_braiding]

public def eval (k : K) : SList K ⥤ SList Unit := (eval₀ k) ⋙ ofFiniteGrpdFunctor
  deriving Functor.Braided

variable (K) in
public def fib₀ : SList K ⥤ (K → FintypeGrpd) := Functor.pi' (eval₀ ·)
  deriving Functor.Braided

variable (K) in
public def fib₁ : SList K ⥤ (K → SList Unit) :=
    fib₀ K ⋙ Functor.pi (fun _ ↦ ofFiniteGrpdFunctor.{0})
  deriving Functor.Braided

-- TODO API for eval: need a natural equivalence w/ Tot', characterization as monoidalLift (δ k)

public irreducible_def fib₀.ι (L : SList K) k : (fib₀ K |>.obj L) k ≃ L.fiber k := eval₀.ι.symm

public irreducible_def fib₁.ι (L : SList K) k : Fin ((fib₁ K |>.obj L) k).length ≃ L.fiber k :=
    ofFinite.ι _ |>.symm.trans eval₀.ι.symm

public irreducible_def fib₁.ι' (L : SList K) : Tot (fib₁ K |>.obj L) ≃ Tot' L :=
  Equiv.sigmaCongrRight (fun k ↦ fib₁.ι L k)

@[simp, grind =]
lemma fib₁.ι'_fst (L : SList K) (t : Tot (fib₁ K |>.obj L)) : (fib₁.ι' L t).fst = t.fst := by
  rw [fib₁.ι'_def]
  rfl

@[simp, grind =]
lemma fib₁.ι'_symm_fst (L : SList K) (t : Tot' L) : (fib₁.ι' L |>.symm t).fst = t.fst := by
  rw [fib₁.ι'_def]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
public lemma fib₁_map_apply {L L' : SList K} (f : L ⟶ L') (k : K) (l : L'.fiber k) :
    totEquivOfHom (fib₁ K |>.map f) ⟨k, (fib₁.ι _ _).symm l⟩ =
      ⟨k, (fib₁.ι _ _).symm (fiberEquivOfHom _ f l)⟩ := by
  simp [fib₁, fib₁.ι_def, fib₀]

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
public lemma fib₁_map_apply_ι' {L L' : SList K} (f : L ⟶ L') (t : Tot' L') :
    totEquivOfHom (fib₁ K |>.map f) ((fib₁.ι' _).symm t) =
    (fib₁.ι' _).symm (Tot'.tot'EquivOfHom f t) := by
  obtain ⟨k, i⟩ := t
  simp [fib₁.ι'_def, Tot'.tot'EquivOfHom, Equiv.sigmaCongrRight,
    fib₁, fib₁.ι_def, fib₀]

-- @[simp, grind =]
-- public lemma fib₁_map_apply_ι'' {L L' : K → SList PUnit} (f : L ⟶ L') (t : Tot L') :
--     totEquivOfHom f ((fib₁.ι' _).symm t) =
--     (fib₁.ι' _).symm _ := by
--   obtain ⟨k, i⟩ := t
--   simp [fib₁.ι'_def, Tot'.tot'EquivOfHom, Equiv.sigmaCongrRight,
--     fib₁, fib₁.ι_def, fib₀]

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
public lemma fib₁_δ_left {L L' : SList K} (t : Tot' L) :
    totEquivOfHom (Functor.OplaxMonoidal.δ (fib₁ K) L L')
      (totTensEquiv _ _ <| .inl <| (fib₁.ι' _).symm t) =
    (fib₁.ι' _).symm (Tot'.tot'TensEquiv _ _ <| .inl t) := by
  simp only [fib₁, fib₀, Functor.comp_obj, Functor.OplaxMonoidal.comp_δ, totEquivOfHom_comp,
    fib₁.ι'_def, Equiv.sigmaCongrRight, Functor.pi_obj, Functor.pi'_obj, ofFiniteGrpdFunctor_obj,
    fib₁.ι_def, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk,
    totTensEquiv_inl, Pi.monoidalCategoryStruct_tensorObj, totEquivOfHom_apply,
    Pi.opLaxMonoidalPi_δ, Functor.pi_map,
    Pi.opLaxMonoidalPi'_δ, Tot'.tot'TensEquiv_apply_inl, Fin.getElem_fin, Sigma.mk.injEq, heq_eq_eq,
    true_and]
  rw [toEquiv_ofFiniteGrpdFunctor_δ_left]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
public lemma fib₁_δ_right {L L' : SList K} (t : Tot' L') :
    totEquivOfHom (Functor.OplaxMonoidal.δ (fib₁ K) L L')
      (totTensEquiv _ _ <| .inr <| (fib₁.ι' _).symm t) =
    (fib₁.ι' _).symm (Tot'.tot'TensEquiv _ _ <| .inr t) := by
  simp only [fib₁, fib₀, Functor.comp_obj, Functor.OplaxMonoidal.comp_δ, totEquivOfHom_comp,
    fib₁.ι'_def, Equiv.sigmaCongrRight, Functor.pi_obj, Functor.pi'_obj, ofFiniteGrpdFunctor_obj,
    fib₁.ι_def, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk,
    totTensEquiv_inr, Pi.monoidalCategoryStruct_tensorObj, totEquivOfHom_apply,
    Pi.opLaxMonoidalPi_δ, Functor.pi_map,
    Pi.opLaxMonoidalPi'_δ, Tot'.tot'TensEquiv_apply_inr, Fin.getElem_fin, Sigma.mk.injEq, heq_eq_eq,
    true_and]
  rw [toEquiv_ofFiniteGrpdFunctor_δ_right]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
public lemma fib₁_μ_left {L L' : SList K} (t : Tot' L) :
    totEquivOfHom (Functor.LaxMonoidal.μ (fib₁ K) L L')
      ((fib₁.ι' _).symm (Tot'.tot'TensEquiv _ _ <| .inl t)) =
    (totTensEquiv _ _ <| .inl <| (fib₁.ι' _).symm t) := by
  simp only [fib₁, fib₀, Functor.comp_obj, Functor.LaxMonoidal.comp_μ, totEquivOfHom_comp,
    fib₁.ι'_def, Equiv.sigmaCongrRight, Functor.pi_obj, Functor.pi'_obj, ofFiniteGrpdFunctor_obj,
    fib₁.ι_def, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
    Tot'.tot'TensEquiv_apply_inl, Fin.getElem_fin, Equiv.coe_fn_symm_mk, totEquivOfHom_apply,
    Pi.monoidalCategoryStruct_tensorObj, Functor.pi_map, Pi.laxMonoidalPi'_μ,
    toEquiv_ofFiniteHomOfEquiv_ι,
    FintypeCat.equivEquivIso_symm_apply_symm_apply, eval₀_δ_inv_left, Pi.laxMonoidalPi_μ,
    totTensEquiv_inl, Sigma.mk.injEq, heq_eq_eq, true_and]
  rw [toEquiv_ofFiniteGrpdFunctor_μ_left]

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
public lemma fib₁_μ_right {L L' : SList K} (t : Tot' L') :
    totEquivOfHom (Functor.LaxMonoidal.μ (fib₁ K) L L')
      ((fib₁.ι' _).symm (Tot'.tot'TensEquiv _ _ <| .inr t)) =
    (totTensEquiv _ _ <| .inr <| (fib₁.ι' _).symm t) := by
  simp only [fib₁, fib₀, Functor.comp_obj, Functor.LaxMonoidal.comp_μ, totEquivOfHom_comp,
    fib₁.ι'_def, Equiv.sigmaCongrRight, Functor.pi_obj, Functor.pi'_obj, ofFiniteGrpdFunctor_obj,
    fib₁.ι_def, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
    Tot'.tot'TensEquiv_apply_inr, Fin.getElem_fin, Equiv.coe_fn_symm_mk, totEquivOfHom_apply,
    Pi.monoidalCategoryStruct_tensorObj, Functor.pi_map, Pi.laxMonoidalPi'_μ,
    toEquiv_ofFiniteHomOfEquiv_ι,
    FintypeCat.equivEquivIso_symm_apply_symm_apply, eval₀_δ_inv_right, Pi.laxMonoidalPi_μ,
    totTensEquiv_inr, Sigma.mk.injEq, heq_eq_eq, true_and]
  rw [toEquiv_ofFiniteGrpdFunctor_μ_right]

end eval₀

end eval

set_option backward.isDefEq.respectTransparency false in
/- A (noncomputable) construction of an explicit object in SList K isomorphic
to the image by fib₀ of a given family.
It’s useful to know a model of such an object rather than the generic
fact that the functor is essentially surjective.
(Note that the construction could be made computable by taking as
input a [FinEnum] instance on `K`, telling "which order" should
be used to construct the symmetric list.) -/
def fib₀.liftEssIm [Finite K] (X : K → FintypeGrpd) : SList K :=
  letI φ := Finite.equivFin K
  SList.ofList <| List.flatten <| .ofFn (n := (Nat.card K)) (fun l ↦
    List.replicate (Nat.card <| X (φ.symm l)) (φ.symm l))

private lemma fib₀.liftEssImIso_aux [Finite K] (X : K → FintypeGrpd) :
    Nonempty ((fib₀ K).obj (fib₀.liftEssIm X) ≅ X) := by
  classical
  let φ := Finite.equivFin K
  refine ⟨Pi.isoMk ?_⟩
  intro i
  apply Nonempty.some
  obtain ⟨l, rfl⟩ := φ.symm.surjective i
  refine ⟨FintypeGrpd.mkIso ?_⟩
  dsimp [fib₀]
  refine (eval₀.ι).symm.trans ?_
  refine (Finite.card_eq.mp ?_).some
  have := fiber_card (φ.symm l) (fib₀.liftEssIm X)
  simp only [Nat.card_eq_fintype_card, this]
  simp [fib₀.liftEssIm, List.count_flatten, List.sum_ofFn, List.count_replicate,
    Equiv.symm_apply_eq]

@[no_expose] noncomputable def fib₀.liftEssImIso [Finite K] (X : K → FintypeGrpd) :
    (fib₀ K).obj (fib₀.liftEssIm X) ≅ X :=
  fib₀.liftEssImIso_aux X |>.some

def fib₁.liftEssIm [Finite K] (X : K → SList Unit) : SList K :=
  fib₀.liftEssIm (fun k ↦ toFintypeGrpdFunctor.{0, 0}.obj (X k))

def fib₁.liftEssImIso [Finite K] (X : K → SList Unit) :
    (fib₁ K).obj (fib₁.liftEssIm X) ≅ X :=
  Pi.isoMk fun k ↦
    ofFiniteGrpdFunctor.{0, 0}.mapIso
      (Pi.isoApp (fib₀.liftEssImIso (fun k ↦ toFintypeGrpdFunctor.{0,0}.obj (X k))) k) ≪≫
    unitEquivalence.unitIso.symm.app _

set_option backward.isDefEq.respectTransparency false in
instance [Finite K] : (fib₀ K).EssSurj where
  mem_essImage X := by
    let φ := Finite.equivFin K
    let L₀ :=
      SList.ofList <| List.flatten <| .ofFn (n := Nat.card K) (fun l ↦
        List.replicate (Nat.card <| X (φ.symm l)) (φ.symm l))
    use L₀
    refine ⟨Pi.isoMk ?_⟩
    intro i
    apply Nonempty.some
    obtain ⟨l, rfl⟩ := φ.symm.surjective i
    refine ⟨FintypeGrpd.mkIso ?_⟩
    dsimp [fib₀]
    refine (eval₀.ι).symm.trans (Finite.card_eq.mp ?_).some
    rw [fiber_card']
    simp [L₀, List.count_flatten, List.sum_ofFn, List.count_replicate]

instance [Finite K] : (fib₁ K).EssSurj :=
  Functor.essSurj_comp ..

set_option backward.isDefEq.respectTransparency false in
def fullyFaithfulFib₁ : (fib₁ K).FullyFaithful where
  preimage {X Y} φ :=
    liftEquiv
      ((Tot'.tot'Equiv Y).symm.trans <| (fib₁.ι' _).symm.trans <|
        (totEquivOfHom φ).trans <| (fib₁.ι' _).trans <| Tot'.tot'Equiv X)
      (fun i ↦ by
        obtain ⟨⟨k, i⟩, rfl⟩ := (Tot'.tot'Equiv Y).surjective i
        simp [fib₁.ι'_def, Equiv.sigmaCongrRight])
  preimage_map {X Y} f := by
    rw [hom_eq_iff_toEquiv_eq]
    ext i : 1
    obtain ⟨⟨k, i⟩, rfl⟩ := (Tot'.tot'Equiv Y).surjective i
    simp
  map_preimage {X Y} f := by
    apply hom_eq_of_totEquivOfHom_eq
    ext i : 1
    obtain ⟨⟨k, ⟨i₀, rfl⟩⟩, rfl⟩ := (fib₁.ι' _).symm.surjective i
    simp only [Fin.getElem_fin, fib₁_map_apply_ι', Tot'.tot'EquivOfHom_apply, toEquiv_liftEquiv,
      Equiv.trans_apply, Tot'.tot'Equiv_apply]
    apply (fib₁.ι' X).injective
    simp only [totEquivOfHom, Equiv.sigmaCongrRight_apply, Equiv.apply_symm_apply]
    ext : 1
    · simp
    · dsimp
      rw! [fib₁.ι'_def, Tot'.tot'Equiv]
      simp [Equiv.sigmaFiberEquiv]

instance : (fib₁ K).Faithful := fullyFaithfulFib₁.faithful
instance : (fib₁ K).Full := fullyFaithfulFib₁.full

instance [Finite K] : (fib₁ K).IsEquivalence where

set_option backward.isDefEq.respectTransparency false in
instance [Finite K] : (fib₁ K).inv.Braided :=
  letI : (Functor.asEquivalence (fib₁ K)).functor.Braided := inferInstanceAs
    (fib₁ K).Braided
  letI : (Functor.asEquivalence (fib₁ K)).inverse.Monoidal :=
    (Functor.asEquivalence <| _).inverseMonoidal
  inferInstanceAs (Functor.asEquivalence (fib₁ K)).inverse.Braided

lemma fib₁_inv_multiset_count [Finite K] [DecidableEq K] (X : K → SList Unit) (k : K) :
    ((fib₁ K).inv.obj X).multiset.count k = (X k).length := by
  let e : (fib₁ K).inv.obj X ≅ fib₁.liftEssIm X :=
    (fib₁ K).inv.mapIso (fib₁.liftEssImIso X).symm ≪≫
      (fib₁ K).asEquivalence.unitIso.symm.app _
  rw [SList.multiset_eq_of_hom e.hom]
  dsimp [fib₁.liftEssIm, fib₀.liftEssIm]
  simp [multiset, List.count_flatten, List.sum_ofFn, List.count_replicate, Equiv.symm_apply_eq]

end CategoryTheory.SList

end
