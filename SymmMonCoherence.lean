import SymmMonCoherence.SList.ToPseudofunctor.Specs
import SymmMonCoherence.SList.ToPseudofunctor.LaxNatTrans

open CategoryTheory

variable (J C : Type*) [Category* C] [MonoidalCategory C] [SymmetricCategory C]

/-! Given a type J, there is a category `SList J` of "symmetric lists" of elements of `J`
that is symmetric monoidal -/

/-- info: SList.instSymmetricCategory -/
#guard_msgs in
#synth SymmetricCategory (SList J)

/-! The category of symmetric lists in J is equivalent to
the free symmetric monoidal category on a type, and the equivalence
is itself symmetric monoidal. -/

/--
info: CategoryTheory.SList.equivalence.{u_1} (C : Type u_1) : SList C ≌ FreeSymmetricMonoidalCategory C
-/
#guard_msgs in
#check SList.equivalence

/-- info: SList.instBraidedFreeSymmetricMonoidalCategoryFunctorEquivalence J -/
#guard_msgs in
#synth (SList.equivalence J).functor.Braided

/-- info: SList.instBraidedFreeSymmetricMonoidalCategoryInverseEquivalence J -/
#guard_msgs in
#synth (SList.equivalence J).inverse.Braided

/-- info: SList.instIsMonoidalFreeSymmetricMonoidalCategoryEquivalence J -/
#guard_msgs in
#synth (SList.equivalence J).IsMonoidal

/-! Hence, symmetric lists have a universal property -/

/--
info: CategoryTheory.SList.monoidalLift.{u_1, v_1, u_2} {C : Type u_1} {D : Type u_2} [Category.{v_1, u_2} D]
  [MonoidalCategory D] [SymmetricCategory D] (p : C → D) : SList C ⥤ D
-/
#guard_msgs in
#check SList.monoidalLift

variable (f : J → C) in
/-- info: SList.instBraidedMonoidalLift f -/
#guard_msgs in
#synth (SList.monoidalLift f).Braided

/--
info: CategoryTheory.SList.monoidalLiftNatTrans.{u_1, v_1, u_2} {C : Type u_1} {D : Type u_2} [Category.{v_1, u_2} D]
  [MonoidalCategory D] [SymmetricCategory D] {F G : SList C ⥤ D} [F.Braided] [G.LaxBraided]
  (φ : (c : C) → F.obj [c]~ ⟶ G.obj [c]~) : F ⟶ G
-/
#guard_msgs in
#check SList.monoidalLiftNatTrans

/--
info: CategoryTheory.SList.monoidalNatTrans_ext_app_singleton.{u_1, v_1, u_2} {C : Type u_1} {D : Type u_2}
  [Category.{v_1, u_2} D] [MonoidalCategory D] [SymmetricCategory D] {F G : SList C ⥤ D} [F.Braided] [G.LaxBraided]
  {α β : F ⟶ G} [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β] (h : ∀ (c : C), α.app [c]~ = β.app [c]~) : α = β
-/
#guard_msgs in
#check SList.monoidalNatTrans_ext_app_singleton

/-! Morphisms in symmetric lists are tied to permutations:
Any morphism `f : L ⟶ L'` of symmetric lists
induces a permutation `(toEquiv f) : Fin L'.length → Fin L.length`.
The permutation can be interpreted as exactly the action on the indices of
the lists. -/

/-- info: CategoryTheory.SList.toList.{u} {C : Type u} (L : SList C) : List C -/
#guard_msgs in
#check SList.toList

/--
info: CategoryTheory.SList.getElem_toList_toEquiv.{u} {C : Type u} {x y : SList C} (f : x ⟶ y) (i : Fin y.length) :
  y.toList[i] = x.toList[(SList.toEquiv f) i]
-/
#guard_msgs in
#check SList.getElem_toList_toEquiv

/-! The permutation attached to a morphism fully characterizes it -/

/--
info: CategoryTheory.SList.hom_eq_iff_toEquiv_eq.{u} {C : Type u} {x y : SList C} (f g : x ⟶ y) :
  f = g ↔ SList.toEquiv f = SList.toEquiv g
-/
#guard_msgs in
#check SList.hom_eq_iff_toEquiv_eq

/-! Any suitable permutation of the set of indices of the list can be lifted,
as long as it is compatible with the values in the list -/

/--
info: CategoryTheory.SList.liftEquiv.{u} {C : Type u} {x y : SList C} (φ : Fin y.length ≃ Fin x.length)
  (hφ : ∀ (i : Fin y.length), y.toList[i] = x.toList[φ i]) : x ⟶ y
-/
#guard_msgs in
#check SList.liftEquiv

/-! The main ingredient for this characterization of morphisms is to link
relations of morphisms in symmetric list with the Coxeter group of type `A∞`,
and then link this group to permutations of `ℕ`. This essentially boils
down to the fact that permutations of `Fin n` form a Coxeter group of type `Aₙ`. -/

/-- info: Ainf : CoxeterMatrix ℕ -/
#guard_msgs in
#check Ainf

/--
info: Ainf_M : Ainf.M = Matrix.of fun i j ↦ if i = j then 1 else if j + 1 = i ∨ i + 1 = j then 3 else 2
-/
#guard_msgs in
#check Ainf_M

/--
info: AinfToPerm_simple (i : ℕ) : AinfToPerm (Ainf.toCoxeterSystem.simple i) = Equiv.swap i (i + 1)
-/
#guard_msgs in
#check AinfToPerm_simple

/-- info: AinfToPerm : Ainf.Group →* Equiv.Perm ℕ -/
#guard_msgs in
#check AinfToPerm

/-- info: hom1MulEquiv (n : ℕ) : (CoxeterMatrix.Aₙ n).Group ≃* Equiv.Perm (Fin (n + 1)) -/
#guard_msgs in
#check hom1MulEquiv -- This one has a suboptimal name

/-- info: AnToAinf (n : ℕ) : (CoxeterMatrix.Aₙ n).Group →* Ainf.Group -/
#guard_msgs in
#check AnToAinf

/-- info: injective_AnToAinf (n : ℕ) : Function.Injective ⇑(AnToAinf n) -/
#guard_msgs in
#check injective_AnToAinf

/-- info: Ainf.exists_lift_to_Aₙ (x : Ainf.Group) : ∃ n x', x = (AnToAinf n) x' -/
#guard_msgs in
#check Ainf.exists_lift_to_Aₙ

/-- info: injective_AinfToPerm : Function.Injective ⇑AinfToPerm -/
#guard_msgs in
#check injective_AinfToPerm

/-! From this, we can define a symmetric monoidal equivalence between
symmetric lists on a unit type and the groupoid of finite types and permutations
(equipped with the coproduct monoidal structure). -/

example : FintypeGrpd ≌ Core (FintypeCat) := .refl

/-- info: CategoryTheory.SList.unitEquivalence.{v, u} : SList PUnit.{v + 1} ≌ FintypeGrpd -/
#guard_msgs in
#check SList.unitEquivalence

/-- info: SList.instBraidedPUnitFintypeGrpdToFintypeGrpdFunctor -/
#guard_msgs in
#synth SList.unitEquivalence.functor.Braided

/-- info: SList.instBraidedFintypeGrpdPUnitOfFintypeGrpdFunctor -/
#guard_msgs in
#synth SList.unitEquivalence.inverse.Braided

/-- info: SList.instIsMonoidalPUnitHomFunctorUnitIso -/
#guard_msgs in
#synth SList.unitEquivalence.unit.IsMonoidal

/-- info: SList.instIsMonoidalFintypeGrpdHomFunctorCounitIso -/
#guard_msgs in
#synth SList.unitEquivalence.counit.IsMonoidal

/-! The equivalence can be upgraded to many-objects: for every finite type
`K`, there is a symmetric monoidal equivalence of categories between `SList K` and
`K → SList Unit`, by sending each `k` to the list corresponding to the "fiber" of
the list at `k`. -/

/-- info: CategoryTheory.SList.fib₁.{u_1} (K : Type u_1) : SList K ⥤ (K → SList Unit) -/
#guard_msgs in
#check SList.fib₁

/-- info: SList.instBraidedForallUnitFib₁ K -/
#guard_msgs in
variable (K) [Finite K] in
#synth (SList.fib₁ K).Braided

/-- info: SList.instIsEquivalenceForallUnitFib₁OfFinite -/
#guard_msgs in
variable (K) [Finite K] in
#synth (SList.fib₁ K).IsEquivalence

/-! To bundle a symmetric monoidal category as a pseudofunctor out of the (2,1)-category of spans,
one must first define said bicategory.
We define first general bicategories of spans with left/right morphisms
satisfying a given `MorphismProperty`. -/

/--
info: CategoryTheory.Spans.{v_1, u_1} (C : Type u_1) [Category.{v_1, u_1} C] (Wₗ Wᵣ : MorphismProperty C) : Type u_1
-/
#guard_msgs in
#check Spans

/-- info: Spans.instBicategory -/
#guard_msgs in
variable {C : Type*} [Category* C]
    (Wₗ : MorphismProperty C)
    (Wᵣ : MorphismProperty C)
    [Wₗ.ContainsIdentities] [Wᵣ.ContainsIdentities] [Wₗ.HasPullbacksAgainst Wᵣ]
    [Wₗ.IsStableUnderBaseChangeAgainst Wᵣ] [Wᵣ.IsStableUnderBaseChangeAgainst Wₗ]
    [Wₗ.IsStableUnderComposition] [Wᵣ.IsStableUnderComposition] in
#synth Bicategory (Spans C Wₗ Wᵣ)

/-! The "effective Burnside (2,1)-category" of a category with pullback is defined to be
`Pith (Spans C ⊤ ⊤)`. -/

/--
info: @[reducible] def CategoryTheory.EffBurnside.{v_1, u_1} : (C : Type u_1) →
  [inst : Category.{v_1, u_1} C] → [Limits.HasPullbacks C] → Type u_1 :=
fun C [Category.{v_1, u_1} C] [Limits.HasPullbacks C] ↦ Bicategory.Pith (Spans C ⊤ ⊤)
-/
#guard_msgs in
#print EffBurnside

/--
info: @[reducible] def CategoryTheory.EffBurnsideFintype.{u} : Type (u + 1) :=
EffBurnside FintypeCat
-/
#guard_msgs in
#print EffBurnsideFintype

/-! The data of a pseudofunctor out of an effective Burnside bicategory corresponds to
a pair of pseudofunctors, along with base change isomorphisms. This is a rather
technical result involving heavy bicategory computations. -/

/--
info: CategoryTheory.EffBurnside.PseudofunctorCore.{w₁, v₁, v₂, u₁, u₂} (C : Type u₁) [Category.{v₁, u₁} C] (B : Type u₂)
  [Bicategory B] : Type (max (max (max (max u₁ u₂) v₁) v₂) w₁)
-/
#guard_msgs in
#check EffBurnside.PseudofunctorCore

/--
info: CategoryTheory.EffBurnside.PseudofunctorCore.u.{w₁, v₁, v₂, u₁, u₂} {C : Type u₁} [Category.{v₁, u₁} C] {B : Type u₂}
  [Bicategory B] (self : EffBurnside.PseudofunctorCore C B) {x y : C} : (x ⟶ y) → (self.obj x ⟶ self.obj y)
-/
#guard_msgs in
#check EffBurnside.PseudofunctorCore.u

/--
info: CategoryTheory.EffBurnside.PseudofunctorCore.v.{w₁, v₁, v₂, u₁, u₂} {C : Type u₁} [Category.{v₁, u₁} C] {B : Type u₂}
  [Bicategory B] (self : EffBurnside.PseudofunctorCore C B) {x y : C} : (x ⟶ y) → (self.obj y ⟶ self.obj x)
-/
#guard_msgs in
#check EffBurnside.PseudofunctorCore.v

/--
info: CategoryTheory.EffBurnside.PseudofunctorCore.baseChangeIso.{w₁, v₁, v₂, u₁, u₂} {C : Type u₁} [Category.{v₁, u₁} C]
  {B : Type u₂} [Bicategory B] (self : EffBurnside.PseudofunctorCore C B) {c₀ c₁ c₂ c₃ : C} (t : c₀ ⟶ c₁) (l : c₀ ⟶ c₂)
  (r : c₁ ⟶ c₃) (b : c₂ ⟶ c₃) (S : IsPullback t l r b) : self.u r ≫ self.v b ≅ self.v t ≫ self.u l
-/
#guard_msgs in
#check EffBurnside.PseudofunctorCore.baseChangeIso

/--
info: CategoryTheory.EffBurnside.PseudofunctorCore.toPseudofunctor.{w₁, v₁, v₂, u₁, u₂} {C : Type v₁} [Category.{u₁, v₁} C]
  {B : Type u₂} [Bicategory B] (P : EffBurnside.PseudofunctorCore C B) [Limits.HasPullbacks C] :
  Pseudofunctor (EffBurnside C) B
-/
#guard_msgs in
#check EffBurnside.PseudofunctorCore.toPseudofunctor

/-! To bundle a symmetric monoidal category as a pseudofunctor out of `BurnsideFintypecat`,
it is good to make the distinction of the computations that happen "formally" and
their realisations in actual monoidal categories. This distinction is encoded by the
Kleisli bicategory for the relative pseudomonad defined by `SList`. -/

/-- info: CategoryTheory.SList.Kleisli.{u} : Type (u + 1) -/
#guard_msgs in
#check SList.Kleisli

/-- info: SList.Kleisli.instBicategory -/
#guard_msgs in
#synth Bicategory SList.Kleisli

/--
info: structure CategoryTheory.SList.Kleisli.Hom.{u} (X Y : SList.Kleisli.{u}) : Type u
number of parameters: 2
fields:
  CategoryTheory.SList.Kleisli.Hom.of : Y.of → SList X.of
constructor:
  CategoryTheory.SList.Kleisli.Hom.mk.{u} {X Y : SList.Kleisli.{u}} (of : Y.of → SList X.of) : X.Hom Y
-/
#guard_msgs in
#print SList.Kleisli.Hom

/--
info: @[defeq] theorem CategoryTheory.SList.Kleisli.comp_of.{u} : ∀ {X Y Z : SList.Kleisli.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
  (f ≫ g).of = (Pi.precompFunctor' (SList X.of) g.of).obj (SList.monoidalLift f.of) :=
fun {X Y Z} f g ↦ Eq.refl (f ≫ g).of
-/
#guard_msgs in
#print SList.Kleisli.comp_of

/-! A symmetric monoidal category defines a pseudofunctor out of the Kleisli bicategory to
`Cat` "via Yoneda". -/

/--
info: CategoryTheory.SList.Kleisli.pseudoOfSymmMonCat.{v', u'} (C : Type u') [Category.{v', u'} C] [MonoidalCategory C]
  [SymmetricCategory C] : Pseudofunctor SList.Kleisli.{0} Cat
-/
#guard_msgs in
#check SList.Kleisli.pseudoOfSymmMonCat

example (J : Type) : (SList.Kleisli.pseudoOfSymmMonCat C).obj (.mk <| J) ≌ (J → C) := .refl

/-! A lax symmetric monoidal functor defines a lax natural transformation between the
pseudofunctors on the Kleisli bicategories. -/

/--
info: CategoryTheory.SList.Kleisli.natTransOfLaxBraided.{v, u} {C D : Type u} [Category.{v, u} C] [Category.{v, u} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D] (F : C ⥤ D) [F.LaxBraided] :
  Lax.LaxTrans (SList.Kleisli.pseudoOfSymmMonCat C).toLax (SList.Kleisli.pseudoOfSymmMonCat D).toLax
-/
#guard_msgs in
#check SList.Kleisli.natTransOfLaxBraided

/--
info: CategoryTheory.SList.Kleisli.natTransOfLaxBraided_app_toFunctor_obj.{v, u} {C D : Type u} [Category.{v, u} C]
  [Category.{v, u} D] [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D] (F : C ⥤ D)
  [F.LaxBraided] (J : SList.Kleisli.{0}) (f : (i : J.of) → (fun a ↦ C) i) (i : J.of) :
  ((SList.Kleisli.natTransOfLaxBraided F).app J).toFunctor.obj f i = F.obj (f i)
-/
#guard_msgs in
#check SList.Kleisli.natTransOfLaxBraided_app_toFunctor_obj

/-! Finally, we build a pseudofunctor from EffBurnsideFintype to `Kleisli` using the previous
constructor. -/

/--
info: CategoryTheory.SList.EffBurnside.pseudoFunctorCore : EffBurnside.PseudofunctorCore FintypeCat SList.Kleisli.{0}
-/
#guard_msgs in
#check SList.EffBurnside.pseudoFunctorCore

open Bicategory in
/--
info: def CategoryTheory.SList.EffBurnside.pseudoOfSymmMonCat.{v', u'} : (C : Type u') →
  [inst : Category.{v', u'} C] → [inst_1 : MonoidalCategory C] → [SymmetricCategory C] → EffBurnsideFintype ⥤ᵖ Cat :=
fun C [Category.{v', u'} C] [MonoidalCategory C] [SymmetricCategory C] ↦
  SList.EffBurnside.pseudoFunctorCore.toPseudofunctor.comp (SList.Kleisli.pseudoOfSymmMonCat C)
-/
#guard_msgs in
#print SList.EffBurnside.pseudoOfSymmMonCat

/--
info: 'CategoryTheory.SList.EffBurnside.pseudoOfSymmMonCat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SList.EffBurnside.pseudoOfSymmMonCat
