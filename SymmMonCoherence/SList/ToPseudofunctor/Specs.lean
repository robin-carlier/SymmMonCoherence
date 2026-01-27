/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.ToPseudofunctor.Defs

/-! # Spans of finite types and the Kleisli bicateory of
symmetric lists.

In this file, we use the results from the file
`SymmMonCoherence.Spans.PseudoFromBurnside.Pseudofunctor` to construct a pseudofunctor
from `Bursnide (FintypeCat)` to the bicategory `SList.Kleisli`.-/

universe v' u'

@[expose] public section

namespace CategoryTheory.SList

variable (C : Type u') [Category.{v'} C] [MonoidalCategory C] [SymmetricCategory C]
section
open Bicategory

instance (J : BurnsideFintype.{0}) :
    MonoidalCategory ((Burnside.pseudoOfSymmMonCat C).obj J) :=
  inferInstanceAs <| MonoidalCategory (J.as.of → C)

instance (J : BurnsideFintype.{0}) :
    SymmetricCategory ((Burnside.pseudoOfSymmMonCat C).obj J) :=
  inferInstanceAs <| SymmetricCategory (J.as.of → C)

noncomputable instance {J K : BurnsideFintype.{0}} (f : J ⟶ K) :
    Functor.Braided ((Burnside.pseudoOfSymmMonCat C).map f).toFunctor := by
  dsimp [Burnside.pseudoOfSymmMonCat, Kleisli.pseudoOfSymmMonCat]
  infer_instance

instance {J K : BurnsideFintype.{0}} {f g : J ⟶ K} (η : f ⟶ g) :
    NatTrans.IsMonoidal ((Burnside.pseudoOfSymmMonCat C).map₂ η).toNatTrans := by
  dsimp [Burnside.pseudoOfSymmMonCat, Kleisli.pseudoOfSymmMonCat]
  infer_instance

noncomputable def pseudoOfSymmMonCat.unitEquivalence :
    (BurnsideFintype.unit.as.of → C) ≌ C where
  functor := Pi.eval _ ()
  inverse := Functor.pi' (fun _ ↦ 𝟭 C)
  -- Slight defeq abuse of Functor.pi' (fun _ ↦ X) ⋙ eval i = X i
  unitIso := .refl _
  counitIso := .refl _

instance : (pseudoOfSymmMonCat.unitEquivalence C).functor.Braided :=
  inferInstanceAs (Functor.Braided <| Pi.eval _ ())

instance : (pseudoOfSymmMonCat.unitEquivalence C).inverse.Braided :=
  inferInstanceAs (Functor.Braided <| Functor.pi' (fun _ ↦ 𝟭 C))

instance : (pseudoOfSymmMonCat.unitEquivalence C).unitIso.hom.IsMonoidal := by
  unfold pseudoOfSymmMonCat.unitEquivalence
  dsimp only [Iso.refl_hom]
  convert NatTrans.IsMonoidal.id
    (F₁ := 𝟭 (((Burnside.pseudoOfSymmMonCat C).obj BurnsideFintype.unit)))
  ext
  · simp only [Functor.comp_obj, Pi.eval_obj, Functor.LaxMonoidal.ε,
      Functor.map_id, Category.comp_id]
    rfl
  · simp only [Functor.comp_obj, Pi.eval_obj, Functor.LaxMonoidal.μ,
      Functor.map_id, Category.comp_id]
    rfl

instance : (pseudoOfSymmMonCat.unitEquivalence C).counitIso.hom.IsMonoidal := by
  unfold pseudoOfSymmMonCat.unitEquivalence
  dsimp only [Iso.refl_hom]
  convert NatTrans.IsMonoidal.id
    (F₁ := (Functor.pi' fun x ↦ 𝟭 C) ⋙ Pi.eval (fun a ↦ C) ())
  ext
  · simp [Functor.LaxMonoidal.ε]
  · simp [Functor.LaxMonoidal.μ]

noncomputable def pseudoOfSymmMonCat.objEquivalence (J : BurnsideFintype.{0}) :
    ((Burnside.pseudoOfSymmMonCat C).obj J) ≌ (J.as.of → C) :=
  Equivalence.refl

section

variable (J : BurnsideFintype.{0})

noncomputable instance : (pseudoOfSymmMonCat.objEquivalence C J).functor.Braided :=
  inferInstanceAs (Functor.Braided <| 𝟭 _)

noncomputable instance : (pseudoOfSymmMonCat.objEquivalence C J).inverse.Braided :=
  inferInstanceAs (Functor.Braided <| 𝟭 _)

instance : (pseudoOfSymmMonCat.objEquivalence C J).unitIso.hom.IsMonoidal := by
  unfold pseudoOfSymmMonCat.objEquivalence
  convert NatTrans.IsMonoidal.id
  ext <;> simp [Functor.LaxMonoidal.ε, Functor.LaxMonoidal.μ, Burnside.pseudoOfSymmMonCat,
    Burnside.pseudoFunctorCore]

instance : (pseudoOfSymmMonCat.objEquivalence C J).counitIso.hom.IsMonoidal := by
  unfold pseudoOfSymmMonCat.objEquivalence
  convert NatTrans.IsMonoidal.id
  ext <;> simp [Functor.LaxMonoidal.ε, Functor.LaxMonoidal.μ, Burnside.pseudoOfSymmMonCat,
    Burnside.pseudoFunctorCore]

end

section
-- identifying the action of the pseudofunctor with the tensor product

noncomputable abbrev univFin₂Span :
    (.mk <| .mk <| .of (Fin 2)) ⟶ (BurnsideFintype.unit) := (Burnside.inl (FintypeCat.{0})).map <|
  (FintypeCat.homMk <| (fun _ ↦ .unit) : (FintypeCat.of <| Fin 2) ⟶ (FintypeCat.of Unit)).toLoc
end

-- Note that because of linearity, the isomorphism is necessarily unique
open MonoidalCategory
noncomputable def univFin₂SpanPushforwardIso :
    (Burnside.pushforwardAux univFin₂Span.of.r () : SList (Fin 2)) ≅ [0]~ ⊗ [1]~ :=
  SList.isoOfMultisetEq _ _ <| by
    simp only [Burnside.pushforwardAux, duality_obj_multiset, multiset_singleton,
      Multiset.nodup_singleton, Multiset.mem_singleton, Multiset.count_eq_one_of_mem,
      Multiset.replicate_succ, Multiset.replicate_zero, Multiset.cons_zero,
      Finset.sum_multiset_singleton, Fin.isValue, multiset_tensor, Multiset.singleton_add]
    rfl

/- Via a symmetric monoidal equivalence (Fin 2 → C) ≌ C × C, we could make the following assignment
natural, monoidal etc. Really, the thing should be broken down into the part relevant from Kleisli,
and the part coming from BurnsideFintype. -/
noncomputable example (X : Fin 2 → C) : ((pseudoOfSymmMonCat.objEquivalence ..).inverse ⋙
    ((Burnside.pseudoOfSymmMonCat C).map univFin₂Span).toFunctor ⋙
    (pseudoOfSymmMonCat.objEquivalence ..).functor ⋙
    (pseudoOfSymmMonCat.unitEquivalence ..).functor).obj X ≅
    X 0 ⊗ X 1 := by
  let e₀ :=
    (monoidalLift X).mapIso ((monoidalLift (RelativePseudomonad.ι (Fin 2))).mapIso
      univFin₂SpanPushforwardIso)
  refine e₀ ≪≫ ?_
  refine (Functor.Monoidal.μIso
    (monoidalLift (RelativePseudomonad.ι (Fin 2)) ⋙
      (monoidalLift X)) _ _).symm ≪≫ ?_
  let e (i : Fin 2) :
      (monoidalLift (RelativePseudomonad.ι (Fin 2)) ⋙ monoidalLift X).obj [i]~ ≅ X i :=
    (monoidalLift X).mapIso (monoidalLiftConsNilIso _ i) ≪≫ monoidalLiftConsNilIso X i
  exact tensorIso (e 0) (e 1)

end

end CategoryTheory.SList

end
