/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.PathCategory.MorphismProperty
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Functor.Trifunctor
public import Mathlib.CategoryTheory.Functor.CurryingThree

/-! # Symmetric lists

In this file, we define the category of symmetric lists on a type `J`.
Symmetric lists are defined as a category by generators and relations, such
that the underlying type is equivalent to the type of lists. The morphisms
are defined inductively in a way that all constructors are naturals,
and a generating morphism `swap : x ::~ y ::~ l ⟶ y ::~ x ::~ l` is
added, subject to a symmetry and hexagon condition.

The construction of this category was
[previously carried](https://nva.sikt.no/registration/0198f1714e08-ec2b3f03-26a6-4e26-a74b-10cf6c5e4903)
in a Rocq+HoTT setting by Stefano Piceghello, also as part of an effort towards
the formalization of Mac Lane’s coherence theorem.

-/
attribute [-simp] CategoryTheory.Paths.of_obj
attribute [-simp] CategoryTheory.Paths.of_map

universe u
namespace CategoryTheory.SList

variable {C : Type u}

@[expose] public section

section SListQuiv

variable (C) in
/-- A type alias for `List C` that serves as the type for
the generating quiver of symmetric lists.

(impl. note): since `List` is an inductive type, a one-field structure
makes inductive constructions painful, so instead this type is defined
as an inductive with the same constructors as `List`. -/
inductive SListQuiv where
  /-- The empty List, seen as `SListQuiv`. -/
  | nil : SListQuiv
  /-- Construction of a list by prepending an element. -/
  | cons (head : C) (tail : SListQuiv) : SListQuiv

namespace SListQuiv
@[inherit_doc] scoped infixr:67 " ::… " => SListQuiv.cons

@[inherit_doc] scoped notation " []' " => SListQuiv.nil

/-- Reinterpret an `SListQuiv` as a `List`. -/
def toList : SListQuiv C → List C
  | []' => .nil
  | c ::… l => c :: l.toList

@[simp, grind =] lemma toList_nil :
    (SListQuiv.nil (C := C) |>.toList) = [] := rfl
@[simp, grind =] lemma toList_cons (c : C) (l : SListQuiv C) :
    (SListQuiv.cons c l |>.toList) = c :: l.toList := rfl

end SListQuiv

open scoped SListQuiv

/-- Interpret a `List` as an `SListQuiv`. -/
@[grind]
def asSListQuiv : List C → SListQuiv C
  | [] => []'
  | c::l => c ::… (asSListQuiv l)

/-- The length of a term in `SListQuiv`. -/
abbrev SListQuiv.length (i : SListQuiv C) : ℕ := (toList i).length

@[simp, grind =]
lemma SListQuiv.length_nil : (SListQuiv.nil (C := C)).length = 0 := rfl

@[simp, grind =]
lemma SListQuiv.length_cons (c : C) (l : SListQuiv C) :
    (SListQuiv.cons c l).length = l.length + 1 := rfl

namespace SListQuiv

@[simp, grind =]
lemma toList_asSListQuiv (L : SListQuiv C) : asSListQuiv L.toList = L := by induction L with grind

@[simp, grind =]
lemma asSListQuiv_toList (L : List C) : (asSListQuiv L).toList = L := by induction L with grind

@[simp, grind =] lemma asSlist₀_length (L : List C) : (asSListQuiv L).length = L.length := by
  induction L with grind

@[simp, grind =] lemma toList_length (L : SListQuiv C) : L.toList.length = L.length := by
  induction L with grind

/-- The equivalence between `List C` and `SListQuiv C`. -/
abbrev listEquiv : SListQuiv C ≃ List C where
  toFun := toList
  invFun := asSListQuiv
  left_inv := by grind
  right_inv := by grind

@[grind inj]
lemma injective_toList : Function.Injective (toList (C := C)) := listEquiv.injective

/-- An elimination principle that transforms parameters in `SListQuiv` to params in `List`. -/
@[elab_as_elim, no_expose]
def listCases {motive : SListQuiv C → Sort*}
    (h : ∀ (l : List C), motive (asSListQuiv l))
    (l : SListQuiv C) : motive l := by
  let m' := h l.toList
  convert m'
  exact listEquiv.left_inv _ |>.symm

lemma listCases_asSListQuiv
    {motive : SListQuiv C → Sort*}
    (h : ∀ (l : List C), motive (asSListQuiv l)) (l : List C) :
    listCases h (asSListQuiv l) = h l := by
  dsimp [listCases]
  grind

-- don’t want to expose this one?
/-- Given `L L' : SListQuiv C`, `Hom L L'` is the type of morphisms in the generating quiver
for symmetric lists: such a generating morphism is either a swap morphism
`a::b::L ⟶ b::a::L` or a morphism of the form `x::f` where `f` is a generating morphism. -/
inductive Hom : SListQuiv C → SListQuiv C → Type u
  /-- The swap morphism `x::y::l ⟶ y::x::l` -/
  | swap (x y : C) (l : SListQuiv C) :
      Hom (x ::… (y ::… l)) (y ::… (x ::… l))
  /-- Given a generating morphism  l ⟶ l', there is a generating morphism `x::l ⟶ x::l'` for
    all `x : C`. -/
  | cons (z : C) {l l' : SListQuiv C} :
      Hom l l' → Hom (z ::… l) (z ::… l')

@[inherit_doc] infixr:67 " ::…ₘ " => Hom.cons
@[inherit_doc] notation "β₀_ "  => Hom.swap

namespace Hom

instance : Quiver (SListQuiv C) where Hom := Hom

@[simp, grind =]
lemma SListQuiv.of_obj_length (l : SListQuiv C) :
    (CategoryTheory.Paths.of (SListQuiv C) |>.obj l).length = l.length := rfl

end Hom

lemma length_eq_of_hom {i j : SListQuiv C} (f : i ⟶ j) : i.length = j.length := by
  induction f with
  | swap x y l => rfl
  | cons z u h => grind

lemma toList_perm_of_hom {i j : SListQuiv C} (f : i ⟶ j) :
    i.toList.Perm j.toList := by
  induction f with
  | swap => exact .swap _ _ _
  | cons p q r => exact .cons _ r

@[induction_eliminator]
public lemma induction
    {motive : {l l' : SListQuiv C} → (l ⟶ l') → Prop}
    (sw : ∀ (x y : C) (l : SListQuiv C), motive (.swap x y l))
    (cons : ∀ (z : C) {l l' : SListQuiv C} (f : l ⟶ l'), motive f → motive (z ::…ₘ f))
    {l l' : SListQuiv C} (f : l ⟶ l') : motive f := by
  induction f with
  | swap x y l => exact sw _ _ _
  | cons z _ h => exact cons _ _ h

end SListQuiv

end SListQuiv

variable (C) in
/-- FreeSListQuiv is the free category on the quiver `SListQuiv`. -/
public structure FreeSListQuiv where p : Paths (SListQuiv C)
public instance : Category (FreeSListQuiv C) :=
  inferInstanceAs (Category <| InducedCategory _ FreeSListQuiv.p)

namespace FreeSListQuiv

variable (C) in
public def ι : SListQuiv C ⥤q FreeSListQuiv C where
  obj x := ⟨Paths.of _ |>.obj x⟩
  map f := InducedCategory.homMk <| (Paths.of (SListQuiv C) |>.map f)

public instance : Coe (SListQuiv C) (FreeSListQuiv C) where
  coe x := (ι C).obj x

public instance {x y : SListQuiv C} : Coe (x ⟶ y) ((ι C).obj x ⟶ (ι C).obj y) where
  coe f := (ι C).map f

public def equiv : FreeSListQuiv C ≃ SListQuiv C where
  toFun x := x.p
  invFun x := (ι C).obj x

public lemma equiv_ι_obj (x : SListQuiv C) : equiv (ι C |>.obj x) = x := equiv.right_inv _

public lemma ι_obj_equiv (x : FreeSListQuiv C) : (ι C).obj (equiv x) = x := equiv.left_inv _

@[grind inj]
lemma injective_ι_obj : Function.Injective (ι C).obj := equiv.symm.injective

public def lift {D : Type*} [Category* D]
    (obj : SListQuiv C → D)
    (map : ∀ {x y : SListQuiv C}, (x ⟶ y) → (obj x ⟶ obj y)) :
    FreeSListQuiv C ⥤ D :=
  letI L := Paths.lift { obj x := obj ↑x, map := map }
  { obj x := L.obj x.p
    map f := L.map f.hom
    map_id x := by erw [Functor.map_id]
    map_comp f g := by erw [Functor.map_comp] } -- TODO remove the Erw
  -- Paths.lift { obj x := obj ↑x, map := map }

/-- Version of Paths.induction for FreeSListQuiv. -/
@[elab_as_elim, induction_eliminator]
public lemma hom_induction
    {motive : {x y : FreeSListQuiv C} → (x ⟶ y) → Prop}
    (id : ∀ {v : SListQuiv C}, motive (𝟙 (ι _ |>.obj v)))
    (comp : ∀ {u v w : SListQuiv C}
      (p : (ι _).obj u ⟶ (ι _).obj v) (q : v ⟶ w), motive p → motive (p ≫ (ι _).map q))
    {x y : FreeSListQuiv C} (f : x ⟶ y) : motive f := by
  cases x with | _ x
  cases y with | _ y
  cases f with | _ f
  change x ⟶ y at f
  induction f using Paths.induction with
  | id => exact id
  | comp p q h => exact comp _ _ h

section

variable {D : Type*} [Category* D]
  {obj : SListQuiv C → D}
  {map : ∀ {x y : SListQuiv C}, (x ⟶ y) → (obj x ⟶ obj y)}

@[simp]
lemma lift_ι_obj (x : SListQuiv C) : (lift obj map).obj x = obj x := rfl

@[simp]
lemma lift_ι_map {x y : SListQuiv C} (f : x ⟶ y) : (lift obj map).map ((ι C).map f) = map f :=
  Paths.lift_toPath _ _

end

@[elab_as_elim, cases_eliminator]
def cases
  {motive : FreeSListQuiv C → Sort*}
  (h : (l : SListQuiv C) → motive ((ι C).obj l))
  (l : FreeSListQuiv C) : motive l := h l.p

lemma cases_of
  {motive : FreeSListQuiv C → Sort*}
  (h : (l : SListQuiv C) → motive ((ι C).obj l))
  (l : SListQuiv C) : cases h ((ι C).obj l) = h l := by rfl

open scoped SListQuiv in
public def cons (x : C) : FreeSListQuiv C ⥤ FreeSListQuiv C :=
  FreeSListQuiv.lift (x ::… ·) (x ::…ₘ ·)

notation3 x " >_" => cons x

notation3 x " ::_ " y => (x>_).obj y

notation3 x " ::_ₘ " f => (x>_).map f

notation3 "[]_" => (ι _).obj SListQuiv.nil

/-- `swap` is the swap morphism as a morphism in the path category, and should be preferred over
`Paths.of (SListQuiv C) |>.map β₀_ _ _ _`.
It is bundled as a definition so that it accepts an argument
of type `Paths (SListQuiv C)` instead of `SListQuiv C`. -/
public def swap (x y : C) (l : FreeSListQuiv C) :
    (x ::_ (y ::_ l)) ⟶ (y ::_ (x ::_ l)) :=
  (ι C).map (β₀_ x y l.p)

@[inherit_doc] scoped notation "β₁_ "  => swap

public abbrev length (l : FreeSListQuiv C) : ℕ := (equiv l).length

@[simp, grind =] public lemma nil_length : ([]_ : FreeSListQuiv C).length = 0 := rfl
@[simp, grind =] public lemma cons_length (x : C) (l : FreeSListQuiv C) :
    (x ::_ l).length = l.length + 1 := rfl

public abbrev toList (l : FreeSListQuiv C) : List C := SListQuiv.toList (l.p)

@[grind =, simp]
lemma toList_length (l : FreeSListQuiv C) : l.toList.length = l.length := rfl

@[grind inj]
public lemma injective_toList : Function.Injective (toList (C := C)) := by
  intros x y h
  apply equiv.injective
  apply SListQuiv.injective_toList
  exact h

@[simp, grind =] public lemma nil_toList : ([]_ : FreeSListQuiv C).toList = [] := rfl
@[simp, grind =] public lemma cons_toList (x : C) (l : FreeSListQuiv C) :
    (x ::_ l).toList = x::l.toList := rfl

@[simp, grind =] public lemma ι_toList (l : SListQuiv C) :
    (ι C |>.obj l).toList = l.toList := rfl

open scoped SListQuiv

public lemma cons_obj_eq (x : C) (l : SListQuiv C) :
    (ι C).obj (x ::… l) = x ::_ l := rfl

public lemma cons_map_def (x : C) {l l' : SListQuiv C} (f : l ⟶ l') :
    (ι C).map (x ::…ₘ f) = x ::_ₘ ((ι C).map f) := rfl

public lemma swap_eq (x y : C) (l : SListQuiv C) :
    (ι C).map (β₀_ x y l) =
      β₁_ x y ((ι C).obj l) := by
  rfl

section natTrans

variable {D : Type*} [Category* D]

public def liftNatTrans {F G : FreeSListQuiv C ⥤ D}
    (app : ∀ (x : SListQuiv C), F.obj x ⟶ G.obj x)
    (nat : ∀ {x y : SListQuiv C} (f : x ⟶ y),
      F.map (ι C |>.map f) ≫ app y =
      app x ≫ G.map (ι C |>.map f)) :
    F ⟶ G where
  app x := app (equiv x)
  naturality x y f := by
    induction f using hom_induction with
    | id => simp
    | @comp x y z p q h => grind [equiv_ι_obj]

@[simp, grind =]
public lemma liftNatTrans_app_ι {F G : FreeSListQuiv C ⥤ D}
    (app : ∀ (x : SListQuiv C), F.obj x ⟶ G.obj x)
    (nat : ∀ {x y : SListQuiv C} (f : x ⟶ y),
      F.map (ι C |>.map f) ≫ app y =
      app x ≫ G.map (ι C |>.map f))
    (x : SListQuiv C) : (liftNatTrans app nat).app (ι C |>.obj x) = app x := rfl

@[simps]
public def liftNatIso {F G : FreeSListQuiv C ⥤ D}
    (app : ∀ (x : SListQuiv C), F.obj x ≅ G.obj x)
    (nat : ∀ {x y : SListQuiv C} (f : x ⟶ y),
      F.map (ι C |>.map f) ≫ (app y).hom =
      (app x).hom ≫ G.map (ι C |>.map f)) :
    F ≅ G where
  hom := liftNatTrans (fun x ↦ app x |>.hom) nat
  inv := liftNatTrans (fun x ↦ app x |>.inv) fun {x y} f ↦ by
    simpa using Eq.symm <| (app x).inv ≫= nat f =≫ (app y).inv
  hom_inv_id := by
    ext x;
    cases x
    simp
  inv_hom_id := by
    ext x;
    cases x
    simp

end natTrans

end FreeSListQuiv

namespace SListQuiv

@[grind, expose]
public def append : SListQuiv C → SListQuiv C → SListQuiv C
  | .nil, bs => bs
  | .cons x as, bs => x ::… (append as bs)

public instance : Append (SListQuiv C) := ⟨SListQuiv.append⟩

@[grind, expose]
public def appendHom : ∀ (l : SListQuiv C),
    {i j : SListQuiv C} → (i ⟶ j) → (l ++ i ⟶ l ++ j)
  | .nil, _, _, f => f
  | .cons x l, _, _, f => x ::…ₘ (appendHom l f)

end SListQuiv

namespace FreeSListQuiv

/-- Do not use directly: use notations `++` on objects and `++ₘ` on morphisms instead. -/
public def append (l : FreeSListQuiv C) : FreeSListQuiv C ⥤ FreeSListQuiv C :=
  lift
    (obj := fun x ↦ (ι C).obj (equiv l ++ x))
    (map := fun f ↦ ι _ |>.map (SListQuiv.appendHom (equiv l) f))

public instance : Append (FreeSListQuiv C) where
  append l l' := (append l).obj l'

notation3 x ">>" => append x

notation3 x " ++ₘ " f => (x>>).map f

public lemma append_def (y y' : FreeSListQuiv C) :
    (append y).obj y' = y ++ y' := rfl

lemma append_nil_obj (y : FreeSListQuiv C) : ([]_ ++ y) = y := rfl

lemma append_nil_map {y z : FreeSListQuiv C} (f : y ⟶ z) :
    ([]_ ++ₘ f) = eqToHom (append_nil_obj _) ≫ f ≫ eqToHom (append_nil_obj _).symm := by
  induction f with
  | id => simp [append_def]
  | comp p q h =>
    simp only [append_def, Functor.map_comp, h]
    rfl

set_option backward.isDefEq.respectTransparency false in
public def appendNilIso : ([]_>>) ≅ 𝟭 (FreeSListQuiv C) :=
  NatIso.ofComponents (fun x ↦ .refl _) (by simp [append_nil_map])

lemma append_cons_obj (x : C) (y z : FreeSListQuiv C) :
    ((x ::_ y) ++ z) = x ::_ (y ++ z) := rfl

lemma append_cons_map (x : C) (y : FreeSListQuiv C) {z z' : FreeSListQuiv C} (f : z ⟶ z') :
    ((x ::_ y) ++ₘ f) =
    eqToHom (by simp [append_def, append_cons_obj]) ≫
      (x ::_ₘ (y ++ₘ f)) ≫ eqToHom (by simp [append_def, append_cons_obj]) := by
  induction f with
  | id => simp
  | comp p q h =>
    simp only [append_def, Functor.map_comp, h]
    rfl

set_option backward.isDefEq.respectTransparency false in
public def appendConsIso (x : C) (l : FreeSListQuiv C) : ((x::_ l)>>) ≅ (l>>) ⋙ cons x :=
  NatIso.ofComponents (fun x ↦ .refl _) (by simp [append_cons_map])

@[simp, grind =]
lemma appendPath_toList (l l' : FreeSListQuiv C) :
    ((l>>).obj l').toList = l.toList ++ l'.toList := by
  cases l with | _ l
  induction l with
  | nil => rfl
  | cons z l hr =>
    change (z ::_ _).toList = _
    simpa


variable (C) in
/-- The equivalence relation on morphism in the category freely generated by the quiver
`SListQuiv C` that defines symmetric lists. The relations are:
- Naturality of the swap
- Symmetry of the swap
- The hexagon relation
- Soundness of `consPath`. -/
public inductive HomEquiv : HomRel (FreeSListQuiv C)
  | swap_naturality (X Y : C) {l l' : SListQuiv C} (f : l ⟶ l') :
      HomEquiv
        (β₁_ X Y ((ι C).obj l) ≫
          (Y ::_ₘ (X ::_ₘ ((ι C).map f))))
        ((X ::_ₘ (Y ::_ₘ ((ι C).map f))) ≫
          (β₁_ X Y ((ι C).obj l')))
  | swap_swap (X Y : C) (l : FreeSListQuiv C) :
      HomEquiv (β₁_ X Y l ≫ β₁_ Y X l) (𝟙 _)
  | triple (X Y Z : C) (l : FreeSListQuiv C) :
      HomEquiv
        (β₁_ X Y (Z ::_ l) ≫ (Y ::_ₘ (β₁_ X Z l)) ≫ β₁_ Y Z (X ::_ l))
        ((X ::_ₘ (β₁_ Y Z l)) ≫ β₁_ X Z (Y ::_ l) ≫ Z ::_ₘ (β₁_ X Y l))
  | cons (X : C) {l l' : FreeSListQuiv C} (f f' : l ⟶ l') :
      HomEquiv f f' → HomEquiv (X ::_ₘ f) (X ::_ₘ f')

set_option backward.isDefEq.respectTransparency false in
public lemma HomEquiv.prepend (l : FreeSListQuiv C) {l' l'' : FreeSListQuiv C} (f f' : l' ⟶ l'')
    (hff' : HomEquiv C f f') : HomEquiv C (l>> |>.map f) (l>> |>.map f') := by
  cases l with | h l =>
  induction l with
  | nil => simpa [append_nil_map]
  | cons x L hr =>
    rw [cons_obj_eq]
    simpa [append_cons_map] using hr.cons _

@[simp, grind =] public lemma append_length (l l' : FreeSListQuiv C) :
    FreeSListQuiv.length (l ++ l') = l'.length + l.length := by
  cases l with | h l =>
  induction l generalizing l' with
  | nil => simp [append_nil_obj]
  | cons x l ih =>
    simp only [SListQuiv.toList_length]
    grind [append_cons_obj, cons_obj_eq]

@[simp, grind =] public lemma append_obj_length (l l' : FreeSListQuiv C) :
    (l >> |>.obj l').length = l'.length + l.length := by simp [append_def]

@[simp, grind =]
public lemma ι_length (l : SListQuiv C) : ((ι C).obj l).length = l.length := by
  have := (equiv (C := C)).right_inv l
  dsimp [equiv] at this
  grind [equiv]

public lemma length_eq_of_hom {i j : FreeSListQuiv C} (f : i ⟶ j) : i.length = j.length := by
  induction f with
  | id => rfl
  | @comp u v w p q h =>
    dsimp at *
    induction q using SListQuiv.induction generalizing u with
    | sw x y l => exact h
    | cons z f hrec =>
      have := SListQuiv.length_eq_of_hom f
      grind [ι_length]

public lemma toList_perm_of_hom {i j : FreeSListQuiv C} (f : i ⟶ j) :
    i.toList.Perm j.toList := by
  induction f with
  | id => simp
  | @comp a b c p q hr =>
    induction q using SListQuiv.induction with
    | sw => exact .trans (by grind) (.swap _ _ _)
    | @cons x y z f hr =>
      simp only [FreeSListQuiv.ι_toList, SListQuiv.toList_cons] at hr ⊢
      have : y.toList.Perm z.toList := SListQuiv.toList_perm_of_hom f
      exact hr.trans (.cons x this)

public lemma toList_perm_iff_nonempty_hom {i j : FreeSListQuiv C} :
    (i.toList.Perm j.toList) ↔ Nonempty (i ⟶ j) where
  mp h := by
    generalize hi : i.toList = i' at h
    generalize hj : j.toList = j' at h
    induction h generalizing i j with
    | nil =>
      obtain rfl : i = j := injective_toList (by grind)
      use 𝟙 _
    | @cons x l₀ l₁ l h =>
      obtain ⟨f⟩ := h (i := (ι C).obj <| asSListQuiv l₀) (j := (ι C).obj <| asSListQuiv l₁)
        (by simp) (by simp)
      obtain rfl : i = (x::_ ((ι C).obj <| asSListQuiv l₀)) := injective_toList (by grind)
      obtain rfl : j = (x::_ ((ι C).obj <| asSListQuiv l₁)) := injective_toList (by grind)
      exact ⟨x ::_ₘ f⟩
    | swap x y l =>
      obtain rfl : i = (y ::_ x ::_ ((ι C).obj <| asSListQuiv l)) := injective_toList (by grind)
      obtain rfl : j = (x ::_ y ::_ ((ι C).obj <| asSListQuiv l)) := injective_toList (by grind)
      exact ⟨β₁_ _ _ _⟩
    | @trans l₁ l₂ l₃ x y h₁ h₂ =>
      obtain ⟨f⟩ := h₁ (j := ((ι C).obj <| asSListQuiv l₂)) hi (by simp)
      obtain ⟨g⟩ := h₂ (i := ((ι C).obj <| asSListQuiv l₂)) (by simp) hj
      exact ⟨f ≫ g⟩
  mpr h := toList_perm_of_hom h.some

public lemma length_eq_zero_iff {x : FreeSListQuiv C} : x.length = 0 ↔ x = []_ where
  mp h := by
    apply injective_toList
    grind [List.length_eq_zero_iff, toList_length]
  mpr h := by
    subst h
    simp

public lemma length_eq_one_iff {x : FreeSListQuiv C} :
    x.length = 1 ↔ ∃ u : C, x = u ::_ []_  where
  mp h := by
    change x.toList.length = 1 at h
    rw [List.length_eq_one_iff] at h
    obtain ⟨a, ha⟩ := h
    use a
    apply injective_toList
    simpa
  mpr h := by
    obtain ⟨u, rfl⟩ := h
    simp

public lemma eq_id_of_hom_nil (f : ([]_ : FreeSListQuiv C) ⟶ []_) : f = 𝟙 []_ := by
  match f with
  | .mk .nil => rfl
  | .mk (.cons p q) => cases q

public lemma eq_of_hom_singleton
    {x y : C} (f : (x ::_ []_) ⟶ (y ::_ []_)) :
    x = y := by
  cases f with |_ f
  cases f with
  | nil => rfl
  | cons p q => cases q with | cons z j => cases j

public lemma eq_eqToHom_of_hom_singleton
    {x y : C} (f : (x ::_ []_) ⟶ (y ::_ []_)) :
    f = eqToHom (by rw [eq_of_hom_singleton f]) := by
  obtain rfl : x = y := eq_of_hom_singleton f
  cases f with |_ f
  cases f with
  | nil => rfl
  | cons p q => cases q with | cons z j => cases j

@[elab_as_elim]
public lemma cases_hom_singleton
    {motive : {x y : C} → ((x ::_ []_) ⟶ (y ::_ []_)) → Prop}
    (h : (x : C) → motive (𝟙 (x ::_ []_)))
    {x y : C} (f : (x ::_ []_) ⟶ (y ::_ []_)) :
    motive f := by
  obtain rfl : x = y := eq_of_hom_singleton f
  obtain rfl : f = 𝟙 _ := eq_eqToHom_of_hom_singleton f
  exact h x

end FreeSListQuiv

variable (C) in
public def _root_.CategoryTheory.SList :=
    CategoryTheory.Quotient (FreeSListQuiv.HomEquiv C)
  deriving Category

variable (C) in
public def π : FreeSListQuiv C ⥤ SList C :=
    Quotient.functor (FreeSListQuiv.HomEquiv C)

public instance : (π C).EssSurj := Quotient.essSurj_functor _

public instance : (π C).Full := Quotient.full_functor _

public lemma sound {x y : FreeSListQuiv C} {f g : x ⟶ y} (h : FreeSListQuiv.HomEquiv _ f g) :
    (π C).map f = (π C).map g := Quotient.sound _ h

-- First, construct the primitive morphisms: swap and cons.

/-- The functor cons -/
public def cons (x : C) : SList C ⥤ SList C :=
  CategoryTheory.Quotient.lift (FreeSListQuiv.HomEquiv C)
    (FreeSListQuiv.cons x ⋙ (π C))
    (fun _ _ f g hfg => by simpa using Quotient.sound _ <| FreeSListQuiv.HomEquiv.cons x f g hfg)

public def nil : SList C := (π C).obj ([]_)

public lemma nil_def : nil (C := C) = (π C).obj ([]_) := rfl

notation3 "[]~" => nil

notation3 x ">~" => cons x

notation3 x " ::~ " y => (x>~).obj y

notation3 x " ::~ₘ " f => (x>~).map f

public lemma π_obj_cons (x : C) (l : FreeSListQuiv C) :
    (π C).obj (x ::_ l) = (x>~).obj ((π C).obj l) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
public lemma π_map_cons (x : C) {l l' : FreeSListQuiv C} (f : l ⟶ l') :
    (π C).map ((x>_).map f) =
      eqToHom (by simp [π_obj_cons]) ≫
        (x>~).map ((π C).map f) ≫
        eqToHom (by simp [π_obj_cons]) := by
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

public def consπIso (x : C) : x>_ ⋙ π C ≅ π C ⋙ x>~ := .refl _

@[elab_as_elim, induction_eliminator, cases_eliminator]
lemma obj_induction
    {motive : SList C → Prop}
    (h : ∀ (x : FreeSListQuiv C), motive ((π C).obj x))
    (x : SList C) : motive x :=
  h x.as

@[elab_as_elim]
public lemma cons_induction
    {motive : SList C → Prop}
    (nil : motive []~)
    (cons : ∀ (head : C) (tail : SList C), motive tail → motive (head ::~ tail))
    (l : SList C) : motive l := by
  induction l using obj_induction with | h l =>
  rcases l with ⟨l⟩
  induction l with
  | nil => exact nil
  | cons head tail ih =>
    convert cons head ((π C).obj ⟨tail⟩) ih

@[elab_as_elim, induction_eliminator, cases_eliminator]
lemma hom_induction
    {motive : {x y : SList C} → (x ⟶ y) → Prop}
    (h : ∀ {x y : FreeSListQuiv C} (f : x ⟶ y), motive ((π C).map f))
    {x y : SList C} (f : x ⟶ y) :
    motive f := by
  cases x with | _ x =>
  cases y with | _ y =>
  have ⟨f, e⟩ := Functor.Full.map_surjective (F := π C) f
  rw [← e]
  exact h f

public def lift {D : Type*} [Category* D] (F : FreeSListQuiv C ⥤ D)
    (h : ∀ {x y : FreeSListQuiv C} {f g : x ⟶ y},
      FreeSListQuiv.HomEquiv _ f g → F.map f = F.map g) :
    SList C ⥤ D := Quotient.lift _ F @h

public lemma lift_π_obj {D : Type*} [Category* D] (F : FreeSListQuiv C ⥤ D)
    {h : ∀ {x y : FreeSListQuiv C} {f g : x ⟶ y},
      FreeSListQuiv.HomEquiv _ f g → F.map f = F.map g}
    (x : FreeSListQuiv C) :
    (lift F h).obj ((π C).obj x) = F.obj x := rfl

set_option backward.isDefEq.respectTransparency false in
public lemma lift_π_map {D : Type*} [Category* D] (F : FreeSListQuiv C ⥤ D)
    {h : ∀ {x y : FreeSListQuiv C} {f g : x ⟶ y},
      FreeSListQuiv.HomEquiv _ f g → F.map f = F.map g}
    {x y : FreeSListQuiv C} (f : x ⟶ y) :
    (lift F h).map ((π C).map f) =
    eqToHom (by simp [lift_π_obj]) ≫ F.map f ≫ eqToHom (by simp [lift_π_obj]) := by
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

public def liftπIso
    {D : Type*} [Category* D] (F : FreeSListQuiv C ⥤ D)
    (h : ∀ {x y : FreeSListQuiv C} {f g : x ⟶ y},
      FreeSListQuiv.HomEquiv _ f g → F.map f = F.map g) :
    π C ⋙ lift F h ≅ F := .refl _

/-- To construct a natural transformation of functor, it suffices to
construct one after precomposition with the quotient functor. -/
public def liftNatTrans
    {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (α : π C ⋙ F ⟶ π C ⋙ G) :
    F ⟶ G := CategoryTheory.Quotient.natTransLift _ α

@[simp, grind =]
public lemma liftNatTrans_app_π
    {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (α : π C ⋙ F ⟶ π C ⋙ G)
    (x : FreeSListQuiv C) :
    (liftNatTrans α).app ((π C).obj x) = α.app x :=
  rfl

/-- To construct a natural transformation of functor, it suffices to
construct one after precomposition with the quotient functor. -/
public def liftNatIso
    {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (α : π C ⋙ F ≅ π C ⋙ G) :
    F ≅ G := CategoryTheory.Quotient.natIsoLift _ α

@[simp, grind =]
public lemma liftNatIso_hom_app_π
    {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (α : π C ⋙ F ≅ π C ⋙ G)
    (x : FreeSListQuiv C) :
    (liftNatIso α).hom.app ((π C).obj x) = α.hom.app x :=
  rfl

@[simp, grind =]
public lemma liftNatIso_inv_app_π
    {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (α : π C ⋙ F ≅ π C ⋙ G)
    (x : FreeSListQuiv C) :
    (liftNatIso α).inv.app ((π C).obj x) = α.inv.app x :=
  rfl

-- Not an [ext] lemma because we don’t necessarily want to apply it in all situations
public lemma natTrans_ext_π
    {D : Type*} [Category* D] {F G : SList C ⥤ D} {α β : F ⟶ G}
    (h : Functor.whiskerLeft (π C) α = Functor.whiskerLeft (π C) β) :
    α = β := by
  ext x
  cases x with | _ x
  exact congr_app h x

open scoped FreeSListQuiv in
public def swap (x y : C) (l : SList C) :
      (x ::~ (y ::~ l)) ⟶ (y ::~ (x ::~ l)) :=
    (π C).map (β₁_ x y l.as)

scoped notation "β~" => swap

set_option backward.isDefEq.respectTransparency false in
open scoped FreeSListQuiv in
public lemma swap_π_def (x y : C) (l : FreeSListQuiv C) :
    (π C).map (β₁_ x y l) =
    eqToHom (by simp [π_obj_cons]) ≫
      β~ x y ((π C).obj l) ≫
      eqToHom (by simp [π_obj_cons]) := by
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

@[reassoc (attr := simp), grind =]
public lemma swap_swap (x y : C) (l : SList C) :
    β~ x y l ≫ β~ y x l = 𝟙 (x ::~ y ::~ l) :=
  Quotient.sound _ (.swap_swap _ _ _)

/-- Bundling `swap` as a natural transformation. -/
public def swapNatTrans (x y : C) :
    (y>~) ⋙ (x>~) ⟶ (x>~) ⋙ (y>~) :=
  liftNatTrans (FreeSListQuiv.liftNatTrans
    (fun _ ↦ β~ _ _ _) (fun {z t} f ↦ by
      simpa [swap_π_def] using sound (.swap_naturality x y f) |>.symm))

@[simp]
public lemma swapNatTrans_app (x y : C) (l : SList C) :
    (swapNatTrans x y).app l = swap x y l := rfl

/-- Bundling `swap` as an isomorphism. -/
@[expose] public abbrev swapIso (x y : C) (l : SList C) :
    (x ::~ (y ::~ l)) ≅ (y ::~ (x ::~ l)) where
  hom := β~ _ _ _
  inv := β~ _ _ _

/-- Bundling `swap` as a natural transformation. -/
@[expose] public abbrev swapNatIso (x y : C) :
    (y>~) ⋙ (x>~) ≅ (x>~) ⋙ (y>~) where
  hom := swapNatTrans _ _
  inv := swapNatTrans _ _

public lemma swap_natural (X Y : C) {l l' : SList C} (f : l ⟶ l') :
    β~ X Y l ≫ (Y>~).map ((X>~).map f) =
    (X>~).map ((Y>~).map f) ≫ β~ X Y l' := by
  simpa using (swapNatTrans X Y).naturality f|>.symm

@[grind _=_]
public lemma swap_hexagon (x y z : C) (l : SList C) :
    β~ x y (z ::~ l) ≫ (y ::~ₘ β~ x z l) ≫ β~ y z (x ::~ l) =
    (x ::~ₘ β~ y z l) ≫ β~ x z (y ::~ l) ≫ z ::~ₘ β~ x y l:=
  Quotient.sound _ (.triple x y z l.as)

set_option backward.isDefEq.respectTransparency false in
public lemma prepend_congr {i j : FreeSListQuiv C} (f g : i ⟶ j) (p : FreeSListQuiv C)
    (h : (π C).map f = (π C).map g) :
    (π C).map (p ++ₘ f) = (π C).map (p ++ₘ g) := by
  cases p with | h p =>
  induction p with
  | nil => simpa [FreeSListQuiv.append_nil_map] using h
  | cons x p hrec =>
    simp [FreeSListQuiv.append_cons_map, FreeSListQuiv.cons_obj_eq,
      π_map_cons, hrec]

set_option backward.isDefEq.respectTransparency false in
public instance : IsGroupoid (SList C) where
  all_isIso {x y} f := by
    have : ∀ {x y : SListQuiv C} (f : x ⟶ y), IsIso ((π C).map <| (FreeSListQuiv.ι C).map f) := by
      clear x y f
      intro x y f
      induction f using SListQuiv.induction with
      | sw x y l =>
        exact ⟨(β~ y x ((π C).obj ((FreeSListQuiv.ι C).obj l))), by
          simp only [FreeSListQuiv.swap_eq, swap_π_def, eqToHom_refl, Category.comp_id,
            Category.id_comp, swap_swap]; tauto⟩
      | cons z f Hr =>
        exact ⟨z>~.map (inv <| (π C).map <| (FreeSListQuiv.ι C).map f), by
          simp [FreeSListQuiv.cons_map_def, π_map_cons]⟩
    induction f with | @h x y f
    induction f using FreeSListQuiv.hom_induction with
    | id => simp only [Functor.map_id]; infer_instance
    | @comp u v w p q H =>
      simp only [Functor.map_comp, isIso_comp_left_iff]
      infer_instance

/-- A direct induction principle for morphisms in SList C. -/
lemma hom_induction' {motive : {x y : SList C} → (x ⟶ y) → Prop}
    (comp : ∀ {x y z : SList C} (f : x ⟶ y) (g : y ⟶ z),
      motive f → motive g → motive (f ≫ g))
    (id : ∀ (x : SList C), motive (𝟙 x))
    (cons : ∀ (head : C) {x y : SList C} (f : x ⟶ y),
      motive f → motive ((head>~).map f))
    (swap : ∀ (x y : C) (l : SList C), motive (β~ x y l))
    {x y : SList C} (f : x ⟶ y) : motive f := by
  have mot_free {u v : SListQuiv C} (f : u ⟶ v) :
    motive ((π C).map ((FreeSListQuiv.ι C).map f)) := by
      induction f using SListQuiv.induction with
      | sw x y l =>
        simpa [Functor.map_comp, FreeSListQuiv.swap_eq, swap_π_def] using (swap _ _ _)
      | cons z f hr =>
        simpa [FreeSListQuiv.cons_map_def, π_map_cons] using (cons _ _ hr)
  cases f using SList.hom_induction with | @h x y f
  induction f using FreeSListQuiv.hom_induction with
  | id => exact id _
  | comp p q r =>
    induction q using SListQuiv.induction with
    | sw x y l =>
      simpa [Functor.map_comp, FreeSListQuiv.swap_eq, swap_π_def] using
        comp _ _ r (swap _ _ _)
    | cons z f hr =>
      simpa [FreeSListQuiv.cons_map_def, π_map_cons] using
        comp _ _ r (cons _ _ (mot_free f))

/-- Probably not the most straightforward here: this doesn’t let me do the things recursively? -/
@[no_expose] public def mkNatTrans
    {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (α_nil : F.obj []~ ⟶ G.obj []~)
    (α_cons : ∀ (c : C) (l : SList C), F.obj (c ::~ l) ⟶ G.obj (c ::~ l))
    (nat_swap : ∀ (x y : C) (l : SList C),
      F.map (β~ x y l) ≫ α_cons y (x ::~ l) = α_cons x (y ::~ l) ≫ G.map (β~ x y l))
    (nat_cons : ∀ (c : C) {l l' : SList C} (f : l ⟶ l'),
      F.map (c ::~ₘ f) ≫ α_cons c l' = α_cons c l ≫ G.map (c ::~ₘ f)) : F ⟶ G :=
  liftNatTrans <| FreeSListQuiv.liftNatTrans
    fun
      | .nil => α_nil
      | .cons c l => α_cons c (π C |>.obj <| (FreeSListQuiv.ι _).obj l)
    fun {x y} f ↦ by
      induction f using SListQuiv.induction with
      | sw x y l =>
        change
          F.map (β~ x y (π C |>.obj <| (FreeSListQuiv.ι C).obj l)) ≫
            α_cons y (x ::~ (π C).obj ((FreeSListQuiv.ι C).obj l)) =
          α_cons x (y ::~ (π C).obj ((FreeSListQuiv.ι C).obj l)) ≫
            G.map (β~ x y (π C |>.obj <| (FreeSListQuiv.ι C).obj l))
        simpa using nat_swap _ _ _
      | @cons c x y f hr =>
        change
          F.map (c ::~ₘ (π C).map ((FreeSListQuiv.ι C).map f)) ≫
            α_cons c ((π C).obj ((FreeSListQuiv.ι C).obj y)) =
          α_cons c ((π C).obj ((FreeSListQuiv.ι C).obj x)) ≫
            G.map ((π C).map ((FreeSListQuiv.ι C).map (c ::…ₘ f)))
        simpa using nat_cons _ _

@[simp, grind =]
public lemma mkNatTrans_app_nil {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (α_nil : F.obj []~ ⟶ G.obj []~)
    (α_cons : ∀ (c : C) (l : SList C), F.obj (c ::~ l) ⟶ G.obj (c ::~ l))
    (nat_swap : ∀ (x y : C) (l : SList C),
      F.map (β~ x y l) ≫ α_cons y (x ::~ l) = α_cons x (y ::~ l) ≫ G.map (β~ x y l))
    (nat_cons : ∀ (c : C) {l l' : SList C} (f : l ⟶ l'),
      F.map (c ::~ₘ f) ≫ α_cons c l' = α_cons c l ≫ G.map (c ::~ₘ f)) :
    (mkNatTrans α_nil α_cons nat_swap nat_cons).app []~ = α_nil :=
  (rfl)

@[simp, grind =]
public lemma mkNatTrans_app_cons {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (α_nil : F.obj []~ ⟶ G.obj []~)
    (α_cons : ∀ (c : C) (l : SList C), F.obj (c ::~ l) ⟶ G.obj (c ::~ l))
    (nat_swap : ∀ (x y : C) (l : SList C),
      F.map (β~ x y l) ≫ α_cons y (x ::~ l) = α_cons x (y ::~ l) ≫ G.map (β~ x y l))
    (nat_cons : ∀ (c : C) {l l' : SList C} (f : l ⟶ l'),
      F.map (c ::~ₘ f) ≫ α_cons c l' = α_cons c l ≫ G.map (c ::~ₘ f))
    (c : C) (l : SList C) :
    (mkNatTrans α_nil α_cons nat_swap nat_cons).app (c ::~ l) = α_cons c l :=
  (rfl)

end

/-- Auxiliary construction for recNatTrans -/
private def recNatTransAux {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (nil : F.obj []~ ⟶ G.obj []~)
    (cons : ∀ (c : C) (l : SList C), (F.obj l ⟶ G.obj l) → (F.obj (c ::~ l) ⟶ G.obj (c ::~ l))) :
    (x : SListQuiv C) →
      (π C ⋙ F).obj ((FreeSListQuiv.ι C).obj x) ⟶ (π C ⋙ G).obj ((FreeSListQuiv.ι C).obj x)
  | .nil => nil
  | .cons c l => cons c (π C |>.obj <| (FreeSListQuiv.ι _).obj l) (recNatTransAux nil cons l)

/-- A recursive natural transformation constructor. -/
@[no_expose] public def recNatTrans {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (nil : F.obj []~ ⟶ G.obj []~)
    (cons : ∀ (c : C) (l : SList C), (F.obj l ⟶ G.obj l) → (F.obj (c ::~ l) ⟶ G.obj (c ::~ l)))
    (nat_swap : ∀ (x y : C) (l : SList C) (prev : F.obj l ⟶ G.obj l),
      F.map (β~ x y l) ≫ cons y (x ::~ l) (cons x l prev) =
      cons x (y ::~ l) (cons y l prev) ≫ G.map (β~ x y l))
    (nat_cons : ∀ (c : C) {l l' : SList C} (f : l ⟶ l')
      (h : F.obj l ⟶ G.obj l) (h' : F.obj l' ⟶ G.obj l'),
      (F.map f ≫ h' = h ≫ G.map f) →
      (F.map (c ::~ₘ f) ≫ cons c l' h' = cons c l h ≫ G.map (c ::~ₘ f))) : F ⟶ G :=
  liftNatTrans <| FreeSListQuiv.liftNatTrans
    (recNatTransAux nil cons)
    fun {x y} f ↦ by
      induction f using SListQuiv.induction with
      | sw x y l =>
        change
          F.map (β~ x y (π C |>.obj <| (FreeSListQuiv.ι C).obj l)) ≫
            cons y (x ::~ (π C).obj ((FreeSListQuiv.ι C).obj l)) _ =
          cons x (y ::~ (π C).obj ((FreeSListQuiv.ι C).obj l)) _ ≫
            G.map (β~ x y (π C |>.obj <| (FreeSListQuiv.ι C).obj l))
        simpa using nat_swap _ _ _ _
      | @cons c x y f hr =>
        change
          F.map (c ::~ₘ (π C).map ((FreeSListQuiv.ι C).map f)) ≫
            cons c ((π C).obj ((FreeSListQuiv.ι C).obj y)) _ =
          cons c ((π C).obj ((FreeSListQuiv.ι C).obj x)) _ ≫
            G.map ((π C).map ((FreeSListQuiv.ι C).map (c ::…ₘ f)))
        simpa using nat_cons _ _ _ _ hr

@[simp, grind =]
public lemma recNatTrans_app_nil {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (nil : F.obj []~ ⟶ G.obj []~)
    (cons : ∀ (c : C) (l : SList C), (F.obj l ⟶ G.obj l) → (F.obj (c ::~ l) ⟶ G.obj (c ::~ l)))
    (nat_swap : ∀ (x y : C) (l : SList C) (prev : F.obj l ⟶ G.obj l),
      F.map (β~ x y l) ≫ (cons y (x ::~ l) (cons x l prev)) =
      (cons x (y ::~ l) (cons y l prev)) ≫ G.map (β~ x y l))
    (nat_cons : ∀ (c : C) {l l' : SList C} (f : l ⟶ l')
      (h : F.obj l ⟶ G.obj l) (h' : F.obj l' ⟶ G.obj l'),
      (F.map f ≫ h' = h ≫ G.map f) →
      (F.map (c ::~ₘ f) ≫ cons c l' h' = cons c l h ≫ G.map (c ::~ₘ f))) :
    (recNatTrans nil cons nat_swap nat_cons).app []~ = nil :=
  (rfl)

@[simp, grind =]
public lemma recNatTrans_app_cons {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (nil : F.obj []~ ⟶ G.obj []~)
    (cons : ∀ (c : C) (l : SList C), (F.obj l ⟶ G.obj l) → (F.obj (c ::~ l) ⟶ G.obj (c ::~ l)))
    (nat_swap : ∀ (x y : C) (l : SList C) (prev : F.obj l ⟶ G.obj l),
      F.map (β~ x y l) ≫ (cons y (x ::~ l) (cons x l prev)) =
      (cons x (y ::~ l) (cons y l prev)) ≫ G.map (β~ x y l))
    (nat_cons : ∀ (c : C) {l l' : SList C} (f : l ⟶ l')
      (h : F.obj l ⟶ G.obj l) (h' : F.obj l' ⟶ G.obj l'),
      (F.map f ≫ h' = h ≫ G.map f) →
      (F.map (c ::~ₘ f) ≫ cons c l' h' = cons c l h ≫ G.map (c ::~ₘ f)))
    (c : C) (l : SList C) :
    (recNatTrans nil cons nat_swap nat_cons).app (c ::~ l) =
    cons c l ((recNatTrans nil cons nat_swap nat_cons).app l) :=
  (rfl)

/-- Auxiliary construction for recNatIso -/
private def recNatIsoAux {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (nil : F.obj []~ ≅ G.obj []~)
    (cons : ∀ (c : C) (l : SList C), (F.obj l ≅ G.obj l) → (F.obj (c ::~ l) ≅ G.obj (c ::~ l))) :
    (x : SListQuiv C) →
      (π C ⋙ F).obj ((FreeSListQuiv.ι C).obj x) ≅ (π C ⋙ G).obj ((FreeSListQuiv.ι C).obj x)
  | .nil => nil
  | .cons c l => cons c (π C |>.obj <| (FreeSListQuiv.ι _).obj l) (recNatIsoAux nil cons l)

-- We can’t really define recNatIso with hom and inv defined as
-- some recNatTrans because the inductive constructors require to construct isomorphisms.
/-- A recursive natural transformation isomorphisms. -/
@[no_expose] public def recNatIso {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (nil : F.obj []~ ≅ G.obj []~)
    (cons : ∀ (c : C) (l : SList C), (F.obj l ≅ G.obj l) → (F.obj (c ::~ l) ≅ G.obj (c ::~ l)))
    (nat_swap : ∀ (x y : C) (l : SList C) (prev : F.obj l ≅ G.obj l),
      F.map (β~ x y (l)) ≫ (cons y (x ::~ l) (cons x l prev)).hom =
      (cons x (y ::~ l) (cons y l prev)).hom ≫ G.map (β~ x y (l)))
    (nat_cons : ∀ (c : C) {l l' : SList C} (f : l ⟶ l')
      (h : F.obj l ≅ G.obj l) (h' : F.obj l' ≅ G.obj l'),
      (F.map f ≫ h'.hom = h.hom ≫ G.map f) →
      (F.map (c ::~ₘ f) ≫ (cons c l' h').hom = (cons c l h).hom ≫ G.map (c ::~ₘ f))) :
    F ≅ G :=
  liftNatIso <| FreeSListQuiv.liftNatIso
    (recNatIsoAux nil cons)
    fun {x y} f ↦ by
      induction f using SListQuiv.induction with
      | sw x y l =>
        change
          F.map (β~ x y (π C |>.obj <| (FreeSListQuiv.ι C).obj l)) ≫
            (cons y (x ::~ (π C).obj ((FreeSListQuiv.ι C).obj l)) _).hom =
          (cons x (y ::~ (π C).obj ((FreeSListQuiv.ι C).obj l)) _).hom ≫
            G.map (β~ x y (π C |>.obj <| (FreeSListQuiv.ι C).obj l))
        simpa using nat_swap _ _ _ _
      | @cons c x y f hr =>
        change
          F.map (c ::~ₘ (π C).map ((FreeSListQuiv.ι C).map f)) ≫
            (cons c ((π C).obj ((FreeSListQuiv.ι C).obj y)) _).hom =
          (cons c ((π C).obj ((FreeSListQuiv.ι C).obj x)) _).hom ≫
            G.map ((π C).map ((FreeSListQuiv.ι C).map (c ::…ₘ f)))
        simpa using nat_cons _ _ _ _ hr

section

variable {D : Type*} [Category* D] {F G : SList C ⥤ D}
    (nil : F.obj []~ ≅ G.obj []~)
    (cons : ∀ (c : C) (l : SList C), (F.obj l ≅ G.obj l) → (F.obj (c ::~ l) ≅ G.obj (c ::~ l)))
    (nat_swap : ∀ (x y : C) (l : SList C) (prev : F.obj l ≅ G.obj l),
      F.map (β~ x y l) ≫ (cons y (x ::~ l) (cons x l prev)).hom =
      (cons x (y ::~ l) (cons y l prev)).hom ≫ G.map (β~ x y l))
    (nat_cons : ∀ (c : C) {l l' : SList C} (f : l ⟶ l')
      (h : F.obj l ≅ G.obj l) (h' : F.obj l' ≅ G.obj l'),
      (F.map f ≫ h'.hom = h.hom ≫ G.map f) →
      (F.map (c ::~ₘ f) ≫ (cons c l' h').hom = (cons c l h).hom ≫ G.map (c ::~ₘ f)))

@[simp, grind =]
public lemma recNatIso_hom_app_nil :
    (recNatIso nil cons nat_swap nat_cons).hom.app []~ = nil.hom :=
  (rfl)

@[simp, grind =]
public lemma recNatIso_hom_app_cons (c : C) (l : SList C) :
    (recNatIso nil cons nat_swap nat_cons).hom.app (c ::~ l) =
    (cons c l ((recNatIso nil cons nat_swap nat_cons).app l)).hom :=
  (rfl)

end

section toList

/-- The underlying list of a symmetric list. -/
public def toList (L : SList C) : List C := L.as.toList

@[simp, grind =]
public lemma nil_toList : ([]~ : SList C).toList = [] := (rfl)

@[simp, grind =]
public lemma cons_toList (x : C) (l : SList C) : ((x>~).obj l).toList = x :: l.toList := (rfl)

@[grind inj]
public lemma injective_toList : Function.Injective (SList.toList (C := C)) := by
  intro x y h
  cases x with |_ x
  cases y with |_ y
  obtain rfl : x = y := FreeSListQuiv.injective_toList h
  rfl

@[simp]
public lemma π_obj_toList (L : FreeSListQuiv C) : ((π C).obj L).toList = L.toList := (rfl)

end toList

section ofList

/-- Construct a symmetric list from an ordinary list. -/
public def ofList (L : List C) : SList C :=
  (π C).obj <| (FreeSListQuiv.ι C).obj (SListQuiv.listEquiv.symm L)

@[simp, grind =]
public lemma nil_ofList : ofList ([] : List C) = []~ := (rfl)

@[simp, grind =]
public lemma cons_ofList (x : C) (l : List C) : ofList (x :: l) = x ::~ (ofList l) := (rfl)

@[grind inj]
public lemma injective_ofList : Function.Injective (SList.ofList (C := C)) := by
  intro x y h
  exact SListQuiv.listEquiv.symm.injective <| FreeSListQuiv.injective_ι_obj congr(($h).as)

/-- The underlying type of the category of symmetric lists is
equivalent to the usual type of lists -/
public abbrev listEquiv : SList C ≃ List C where
  toFun := toList
  invFun := ofList
  left_inv := by
    intro x
    induction x using cons_induction with grind
  right_inv := by
    intro x
    induction x with grind

@[simp, grind =]
public lemma ofList_toList (L : List C) : (ofList L).toList = L := listEquiv.right_inv _

@[simp, grind =]
public lemma toList_ofList (L : SList C) : ofList L.toList = L := listEquiv.left_inv _

public lemma ofList_singleton (c : C) : ofList [c] = c ::~ []~ := (rfl)

/-- The canonical isomorphism (in fact equality) (ofList [c]) ≅ (c ::~ []~) -/
@[expose] public def ofListSingletonIso (c : C) : ofList [c] ≅ c::~ []~ :=
  eqToIso (ofList_singleton c)

end ofList

variable (C) in
/-- `RecursiveFunctorData` defines the necessary structure in a target category `D`
to recursively build a functor from `SList C`, with prescribed value on []~, and prescribed
action on `x ::~ -`.
-/
public structure RecursiveFunctorData (D : Type*) [Category* D] where
  /-- The object in `D` corresponding to the empty list `[]~`. -/
  nilObj : D
  /-- For each `c : C`, a functor `D ⥤ D` representing pre-composition with `c` (like `c ::~ -`). -/
  consF (c : C) : D ⥤ D
  /-- For each `x y : C`, a natural isomorphism representing the swap operation. -/
  swapIso (x y : C) : consF y ⋙ consF x ≅ consF x ⋙ consF y
  /-- The swap is involutive: `swap x y ≫ swap y x = id`. -/
  swap_inv (x y : C) (d : D) :
    (swapIso x y).hom.app d ≫ (swapIso y x).hom.app d = 𝟙 _
  /-- The hexagon identity for swaps. -/
  hexagon (x y z : C) (d : D) :
    (swapIso x y).hom.app ((consF z).obj d) ≫
      ((consF y).map ((swapIso x z).hom.app d)) ≫
      (swapIso y z).hom.app ((consF x).obj d) =
    ((consF x).map ((swapIso y z).hom.app d)) ≫
      (swapIso x z).hom.app ((consF y).obj d) ≫
      ((consF z).map ((swapIso x y).hom.app d))

namespace RecursiveFunctorData

variable {D : Type*} [Category* D] (data : RecursiveFunctorData C D)

/-- The raw object map for the bundle functor on the generating quiver.
    It maps a list `l` to the tuple `(l, F(l))`. -/
def rawObj : SListQuiv C → D
  | .nil => data.nilObj
  | .cons c l => (data.consF c).obj (rawObj l)

/-- The raw morphism map for the bundle functor on the generating quiver. -/
def rawMap : {l l' : SListQuiv C} → (l ⟶ l') → (data.rawObj l ⟶ data.rawObj l')
  | _, _, .swap x y l =>
        -- (β~ x y (data.rawObj l).1)
        ((data.swapIso x y).hom.app (data.rawObj l))
  | _, _, .cons z f =>
        ((data.consF z).map (rawMap f))

open FreeSListQuiv

/-- The lifted functor from the free category on the quiver to the product category. -/
def freeFunctor : FreeSListQuiv C ⥤ D :=
  FreeSListQuiv.lift data.rawObj data.rawMap

@[simp]
lemma freeFunctor_map_ι_map {x y : SListQuiv C} (f : x ⟶ y) :
    data.freeFunctor.map ((FreeSListQuiv.ι C).map f) = data.rawMap f := by
  simp [freeFunctor]

set_option backward.isDefEq.respectTransparency false in
@[local simp]
lemma freeFunctor_map_swap' {x y : C} (l : SListQuiv C) :
    (data.freeFunctor.map (β₁_ x y ((ι C).obj l))) =
   (data.swapIso x y).hom.app (data.rawObj l) := by
  simp [← FreeSListQuiv.swap_eq, rawMap]

@[local simp]
lemma freeFunctor_map_swap {c c' : C} (l : FreeSListQuiv C) :
    data.freeFunctor.map (β₁_ c c' l) =
      ((data.swapIso c c').hom.app _) := by
  cases l
  simp only [freeFunctor_map_swap']
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma freeFunctor_map_ι (z : C) {l l' : SListQuiv C} (f : l ⟶ l') :
    data.freeFunctor.map (z ::_ₘ ((ι C).map f)) =
      ((data.consF z).map (data.freeFunctor.map f)) := by
  change data.freeFunctor.map ((ι C).map (z ::…ₘ f)) = _
  simp [rawMap]

set_option backward.isDefEq.respectTransparency false in
lemma freeFunctor_map_cons (z : C) {l l' : FreeSListQuiv C} (f : l ⟶ l') :
    data.freeFunctor.map (z ::_ₘ f) =
      ((data.consF z).map (data.freeFunctor.map f)) := by
  induction f using FreeSListQuiv.hom_induction with
  | id =>
    simp only [freeFunctor, Functor.map_id, lift_ι_obj]
    rfl
  | comp p q ih =>
    simp only [Functor.map_comp, freeFunctor_map_ι] at ih ⊢
    simp [ih]

set_option backward.isDefEq.respectTransparency false in
/-- The recursive functor constructed from the data. -/
public def functor : SList C ⥤ D :=
  SList.lift data.freeFunctor <| by
    intros x y f g h
    induction h with
    | @swap_naturality X Y l l' f =>
      simp only [Functor.map_comp, freeFunctor_map_swap, freeFunctor_map_cons,
        freeFunctor_map_ι_map]
      have := (data.swapIso X Y).hom.naturality (data.rawMap f)
      simp only [Functor.comp_obj, Functor.comp_map] at this
      exact this.symm
    | swap_swap X Y l =>
      simp only [Functor.map_comp, freeFunctor_map_swap, Functor.comp_obj,
        swap_inv, Functor.map_id]
      rfl
    | triple X Y Z l =>
      simp only [Functor.map_comp, freeFunctor_map_swap, freeFunctor_map_cons]
      simpa using data.hexagon _ _ _ _
    | @cons X l l' f f' h ih => simp [freeFunctor_map_cons, ih]

public lemma functor_obj_nil : data.functor.obj nil = data.nilObj := (rfl)

public lemma functor_obj_cons (c : C) (l : SList C) :
    data.functor.obj (c ::~ l) = (data.consF c).obj (data.functor.obj l) := (rfl)

@[expose] public def functorObjNilIso : data.functor.obj []~ ≅ data.nilObj :=
    eqToIso data.functor_obj_nil

@[expose] public def functorObjConsIso (c : C) (l : SList C) :
    data.functor.obj (c ::~ l) ≅ (data.consF c).obj (data.functor.obj l) :=
  eqToIso <| data.functor_obj_cons c l

@[simp]
public lemma functor_map_cons_map (c : C) {l l' : SList C} (f : l ⟶ l') :
    data.functor.map (c ::~ₘ f) =
    (data.functorObjConsIso _ _).hom ≫
      (data.consF c).map (data.functor.map f) ≫
      (data.functorObjConsIso _ _).inv := by
  simp only [functorObjConsIso]
  induction f with | h f =>
  simp only [functor]
  generalize_proofs h
  change
    ((lift data.freeFunctor h).map ((π C).map _)) = _
  simp only [lift_π_map, freeFunctor_map_cons]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
public lemma functor_map_swap (c c' : C) (l : SList C) :
    data.functor.map (β~ c c' l) =
    (data.functorObjConsIso _ _).hom ≫
      (data.consF c).map (data.functorObjConsIso _ _).hom ≫
      (data.swapIso c c').hom.app (data.functor.obj l) ≫
      (data.consF c').map (data.functorObjConsIso _ _).inv ≫
      (data.functorObjConsIso _ _).inv := by
  simp only [functorObjConsIso, eqToIso_refl, Iso.refl_hom, Functor.map_id, Functor.comp_obj,
    Iso.refl_inv, Category.id_comp]
  cases l with | h l =>
  change data.functor.map (π C |>.map <| β₁_ c c' l) = _
  simp only [functor]
  generalize_proofs h
  rw [SList.lift_π_map (h := h)]
  simp only [eqToHom_refl, freeFunctor_map_swap, Category.comp_id, Category.id_comp]
  erw [Functor.map_id, Category.comp_id] -- TODO clear this erw
  simp only [Category.comp_id]
  rfl

end RecursiveFunctorData

section length

public abbrev length (x : SList C) : ℕ := x.toList.length

@[simp, grind =] public lemma length_nil : ([]~ : SList C).length = 0 := (rfl)

@[simp, grind =] public lemma length_cons (x : C) (l : SList C) :
    ((x>~).obj l).length = l.length + 1 := (rfl)

public lemma length_eq_of_hom {x y : SList C} (f : x ⟶ y) : x.length = y.length := by
  cases f with | h f
  exact FreeSListQuiv.length_eq_of_hom f

@[simp, grind =]
public lemma π_obj_length {x : FreeSListQuiv C} : ((π C).obj x).length = x.length := (rfl)

public lemma length_eq_zero_iff {x : SList C} : x.length = 0 ↔ x = []~ where
  mp h := by
    apply injective_toList
    grind [List.length_eq_zero_iff]
  mpr h := by
    subst h
    simp

public lemma length_eq_one_iff {x : SList C} :
    x.length = 1 ↔ ∃ u : C, x = u ::~ []~  where
  mp h := by
    change x.toList.length = 1 at h
    rw [List.length_eq_one_iff] at h
    obtain ⟨a, ha⟩ := h
    use a
    apply injective_toList
    simpa
  mpr h := by
    obtain ⟨u, rfl⟩ := h
    simp

public lemma eq_id_of_hom_nil (f : ([]~ : SList C) ⟶ []~) : f = 𝟙 []~ := by
  cases f with | _ f
  obtain rfl := FreeSListQuiv.eq_id_of_hom_nil f
  simp [nil_def]

@[elab_as_elim]
public lemma cases_hom_singleton
    {motive : {x y : C} → ((x ::~ []~) ⟶ (y ::~ []~)) → Prop}
    (h : (x : C) → motive (𝟙 (x ::~ []~)))
    {x y : C} (f : (x ::~ []~) ⟶ (y ::~ []~)) :
    motive f := by
  cases f with |_ f
  simp only [nil_def, π, Quotient.functor] at f
  obtain rfl : x = y := FreeSListQuiv.eq_of_hom_singleton f
  have u := FreeSListQuiv.eq_eqToHom_of_hom_singleton f
  rw [u]
  simpa using h x

@[simp, grind =]
public lemma lenth_ofList (L : List C) : (ofList L).length = L.length := by simp [ofList]

end length

public lemma toList_perm_iff_nonempty_hom (i j : SList C) :
    (i.toList.Perm j.toList) ↔ Nonempty (i ⟶ j) where
  mp h := by
    induction i
    induction j
    simp only [π_obj_toList] at h
    obtain ⟨f⟩ := FreeSListQuiv.toList_perm_iff_nonempty_hom.mp h
    exact ⟨π C|>.map f⟩
  mpr h := by
    induction i with | _ i
    induction j with | _ j
    obtain ⟨f⟩ := h
    cases f with | _ f
    simpa only [π_obj_toList] using FreeSListQuiv.toList_perm_of_hom f

public lemma toList_perm_iff_nonempty_iso {i j : SList C} :
    (i.toList.Perm j.toList) ↔ Nonempty (i ≅ j) := by
  letI : Groupoid (SList C) := Groupoid.ofIsGroupoid
  have : Nonempty (i ≅ j) ↔ Nonempty (i ⟶ j) := Nonempty.congr (·.hom)
    (Groupoid.isoEquivHom i j).invFun
  simpa [this] using toList_perm_iff_nonempty_hom i j

public instance : IsEmpty (Fin ([]~ : SList C).length) :=
  inferInstanceAs <| IsEmpty <| Fin 0

@[no_expose] public instance (c : C) : Unique (Fin (c::~[]~).length) :=
  inferInstanceAs <| Unique <| Fin 1

end SList

end CategoryTheory
