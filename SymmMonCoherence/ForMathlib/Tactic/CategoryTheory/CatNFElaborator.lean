/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.ForMathlib.Tactic.CategoryTheory.CancelIso
public import SymmMonCoherence.ForMathlib.Tactic.CategoryTheory.CatNFAttr
public import Mathlib.CategoryTheory.NatTrans

public meta section

namespace Mathlib.Tactic.CategoryTheory.CatNF

open Lean Elab Term Meta Mathlib.Tactic.Push _root_.CategoryTheory

-- TODO add more lemmas to this.
attribute [cat_nf]
  Category.assoc Functor.map_comp Category.comp_id Category.id_comp
  Functor.comp_obj Functor.comp_map IsIso.inv_comp

def catNormalize (e : Expr) : MetaM Simp.Result := do
  let some cat_nf_ext ← getSimpExtension? `cat_nf | throwError "cat_nf has not been initialized"
  -- Adding the builtin theorems to replicate what `simpOnlyNames` is doing
  let builtins : SimpTheorems ← Tactic.simpOnlyBuiltins.foldlM (SimpTheorems.addConst · ·) {}
  let ctx : Simp.Context ←
    Simp.mkContext { decide := false }
      (simpTheorems := #[ builtins, ← cat_nf_ext.getTheorems ])
      (congrTheorems := ← Lean.Meta.getSimpCongrTheorems)
  (·.1) <$> Lean.Meta.simp e ctx
    (simprocs := ← (Simp.SimprocsArray.add #[] `cancelIso true))

/-- Syntax for the `cat_nf%` elaborator.
Simplify a morphism or an equality of morphisms according to basic category theory simp normal
forms. The simp lemmas used are the ones in the `cat_nf` simp set. -/
elab (name := invPercent) "cat_nf%" t:term : term => do
  mapForallTelescope (fun e => do
    match_expr ← inferType e with
    | Eq _ _ _ => return (← simpEq (fun e => catNormalize e) (← inferType e) e).2
    | Quiver.Hom _ _ _ _ => return (← catNormalize e).1
    | _ => throwError "cat_nf%: invalid term") (← elabTerm t none)

end Mathlib.Tactic.CategoryTheory.CatNF

end
