/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Pi.Basic
universe w₀ w₁ w₂ v₁ v₂ v₃ u₁ u₂ u₃

public section

namespace CategoryTheory.Pi

variable {I : Type w₀} {J : Type w₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)] {A : Type u₃} [Category.{v₃} A]

instance (F : ∀ i, C i ⥤ D i) [∀ i, (F i).EssSurj] :
    (Functor.pi F).EssSurj where
  mem_essImage X := by
    let (i : I) := (Functor.EssSurj.mem_essImage (F := F i) (X i)).witness
    use this
    exact ⟨Pi.isoMk (fun i ↦ (Functor.EssSurj.mem_essImage (F := F i) (X i)).getIso)⟩

instance (F : ∀ i, C i ⥤ D i) [∀ i, (F i).Full] :
    (Functor.pi F).Full where
   map_surjective {X Y} f := by
     let (i : I) := (Functor.Full.map_surjective (F := F i) (f i)).choose
     use this
     ext i
     simpa [this] using (Functor.Full.map_surjective (F := F i) (f i)).choose_spec

instance (F : ∀ i, C i ⥤ D i) [∀ i, (F i).Faithful] :
    (Functor.pi F).Faithful where
   map_injective {X Y} f g hfg := by
     ext i
     have (i : I) := (Functor.Faithful.map_injective (F := F i) (congr($hfg i)))
     exact this i

end CategoryTheory.Pi
