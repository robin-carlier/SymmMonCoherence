/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.Tactic.CategoryTheory.CancelIso

public meta section
namespace Mathlib.Tactic.CategoryTheory.invPercent

open Lean Elab Term Meta Mathlib.Tactic.Push _root_.CategoryTheory
/--
Syntax for the `inv%` elaborator.
Usage: `inv% head expr` -/
elab (name := invPercentElaborator) "inv%" t:term : term => do
  mapForallTelescope (fun e => do
    match_expr ← inferType e with
    | Eq T f g =>
      let_expr Quiver.Hom C _ x y := T | throwError "inv%: invalid term"
      let e₀ ← mkAppOptM ``CategoryTheory.IsIso.inv_eq_inv #[C, none, x, y, f, g, none, none]
      let e₁ ← mkAppOptM ``Iff.mpr #[none, none, e₀, e]
      /- push_inv (f ≫ g ≫ h) tends to left-associate things, so we add a small
      `simp only [Category.assoc]` pass. -/
      let e₂ ← Mathlib.Tactic.Push.pushCore (.const ``CategoryTheory.inv) {} none (← inferType e₁)
      let e' ← e₂.mkEqMP e₁
      let e₃ ←
        simpEq (fun e => simpOnlyNames [``Category.assoc, ``Category.id_comp, ``Category.comp_id] e
          (config := { decide := false })) (← inferType e') e'
      return e₃.2
    | Quiver.Hom C _ x y =>
      let e_inv ← mkAppOptM ``CategoryTheory.inv #[C, none, x, y, e, none]
      let p := (← Mathlib.Tactic.Push.pushCore (.const ``CategoryTheory.inv) {} none e_inv).expr
      let p' ← simpOnlyNames [``Category.assoc, ``Category.id_comp, ``Category.comp_id] p
        (config := { decide := false })
      return p'.1
    | _ => throwError "inv%: invalid term") (← elabTerm t none)

end Mathlib.Tactic.CategoryTheory.invPercent

end
