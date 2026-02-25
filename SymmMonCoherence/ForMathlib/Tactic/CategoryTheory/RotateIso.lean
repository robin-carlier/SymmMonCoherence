/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public meta import SymmMonCoherence.ForMathlib.Tactic.CategoryTheory.CancelIso

public meta section

/-!
# The `rotate_isos` tactic

Given a term of the form `e : α₁ ≫ ⋯ ≫ αₖ = β₁ ≫ ⋯ ≫ βₗ`,
the `rotate_isos` tactic moves specified numbers
of isomorphisms from the left-hand side of the equality to the right-hand side,
or from the RHS to the LHS if the flag ← is specified.

Depending on a flag given to the tactic, the isomorphisms are moved from the lhs starting from
the leftmost morphism or from the rightmost morphism.

```lean
variable {C : Type*} [Category C]

example (a b c d e : C) (g : b ≅ c) (h : d ≅ c) (i : d ⟶ e) (k : a ⟶ e)
    (hyp : ∀ (f : a ≅ b), f.hom ≫ g.hom ≫ h.inv ≫ i = k) :
    ∀ (f : a ≅ b), i = h.hom ≫ g.inv ≫ f.inv ≫ k := by
  rotate_isos ← 0 3 using hyp

```
This file also provides two terms elaborators: `rotate_isos%` and `rotate_isos_iff%`, that
are used to apply the tactic at a term and use it e.g. as a rewrite rule or as simp lemmas. -/

open Lean Parser.Tactic Elab Command Elab.Tactic Meta _root_.CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.RotateIsos

initialize registerTraceClass `rotate_isos

/-- Given an `Expr e` assumed to be representing a sequence of
composition of morphisms in a category,
traverse `e` and build an array of the morphisms that appear in `e`.
The source and target of morphisms are also part of the array. -/
partial def getMorphisms (e : Expr) :
    MetaM (Array ((Expr × Expr) × Expr)) := do
  return (← go e).reverse where
  go (e : Expr) : MetaM (Array ((Expr × Expr) × Expr)) := do
    let_expr CategoryStruct.comp _ _ x y _ f g := e |
      -- terminals
      let_expr Quiver.Hom _ _ x y := ← inferType e | throwError "getMorphism: not a morphism"
      return #[((x, y), e)]
    return (← go g) |>.push ((x, y), f)

/-- Given `morphisms : Array Expr` and `k : ℕ`,
construct an expression for the composition of the first or last `k` morphisms of `morphisms`.
The `d` parameter is supposed to be an expression for the source or target object
used as the identity when composing 0 morphisms.
The `rev` flag controls whether we compose the first `k` or last `k` morphisms. -/
def compose (rev : Bool) (d : Expr)
    (morphisms : Array Expr) (k : ℕ) : MetaM Expr := do
  if k == 0 then return d -- early return
  let (start, stop) := if rev then (morphisms.size - 1, morphisms.size - k) else (k - 1, 0)
  morphisms.foldrM (start := start) (stop := stop)
    (fun e r ↦ mkAppM ``CategoryStruct.comp #[e, r]) (morphisms.getD start d)

/-- Given an expression for a term equality `e` that is assumed to be a composition
of morphisms in a category, run what is essentially
`simp only [Category.assoc, cancelIso, Category.id_comp, Category.comp_id]` on `e`. -/
def cancelIsoAssoc (e : Expr) : MetaM Simp.Result := do
  let ctx : Simp.Context ←
    Simp.Context.ofNames
      [``Category.assoc, ``Category.id_comp, ``Category.comp_id,
        ``CategoryTheory.IsIso.inv_comp, ``CategoryTheory.IsIso.inv_id]
      true { decide := false }
  (·.1) <$> Lean.Meta.simp e ctx
    (simprocs := ← (Simp.SimprocsArray.add #[] `cancelIso true))

def rotateIsosCore (e : Expr) (a b : ℕ) (rev : Bool) : MetaM (Expr × Expr) := do
  -- let e' ← whnfR e
  -- We start by right-associating everything in the expression
  -- We are not using simpEq because we want to carry around an iff proof.
  let some (T, lhs₀, rhs₀) := (← whnfR e).eq? | throwError "unreachable, expecting equality"
  let simp_lhs₀ ← simpOnlyNames [``Category.assoc] lhs₀ (config := { decide := false })
  let simp_rhs₀ ← simpOnlyNames [``Category.assoc] rhs₀ (config := { decide := false })
  /- Now we build the proof that `(simp_lhs₀ = simp_rhs₀) ↔ e -/
  let iff₁ ← mkAppOptM ``Eq.congr #[T, simp_lhs₀.expr, lhs₀, simp_rhs₀.expr, rhs₀,
    ← mkEqSymm (← simp_lhs₀.getProof), ← mkEqSymm (← simp_rhs₀.getProof)]
  let (lhs, rhs) := (simp_lhs₀.expr, simp_rhs₀.expr)
  trace[rotate_isos] "type is {T}"
  -- First we build a bit of context
  let_expr Quiver.Hom C _ x y := ← whnfR T
    | throwError "rotate_isos can only be used on equalities of morphisms in categories"
  let (mor_lhs, mor_rhs) := (← getMorphisms lhs, ← getMorphisms rhs)
  -- Then, we compute the morphisms that will be appended to the left and to the right.
  let left_to_append ←
    if rev then
      compose false (← mkAppM ``CategoryStruct.id #[x]) (mor_rhs.map (·.2)) a
    else
      compose false (← mkAppM ``CategoryStruct.id #[x]) (mor_lhs.map (·.2)) a
  let right_to_append ←
    if rev then
      compose true (← mkAppM ``CategoryStruct.id #[y]) (mor_lhs.map (·.2)) b
    else
      compose true (← mkAppM ``CategoryStruct.id #[y]) (mor_rhs.map (·.2)) b
  /- Then, we construct the inverses of the morphisms.
  we need to use mkAppOptM otherwise the `IsIso` instance is left pending.
  If the IsIso instance can’t be found, this will throw an error, which is what we
  want as the error message if some morphism in the composition is not an isomorphism. -/
  let inv_left_to_append ←
    Push.pushCore (.const ``CategoryTheory.inv) {} none <|
      ← mkAppOptM ``CategoryTheory.inv #[C, none, none, none, left_to_append, none]
  let inv_right_to_append ←
    Push.pushCore (.const ``CategoryTheory.inv) {} none <|
      ← mkAppOptM ``CategoryTheory.inv #[C, none, none, none, right_to_append, none]
  -- compose them on the left and right of the equality:
  let new_lhs₀ ← mkAppM ``CategoryStruct.comp #[lhs, inv_right_to_append.expr]
  let new_rhs₀ ← mkAppM ``CategoryStruct.comp #[rhs, inv_right_to_append.expr]
  let new_lhs ← mkAppM ``CategoryStruct.comp #[inv_left_to_append.expr, new_lhs₀]
  let new_rhs ← mkAppM ``CategoryStruct.comp #[inv_left_to_append.expr, new_rhs₀]
  let new_eq ← mkEq new_lhs new_rhs
  let iff_proof₀ ← mkAppOptM ``CategoryTheory.cancel_mono
    #[C, none, none, none, none, inv_right_to_append.expr, none, lhs, rhs]
  let iff_proof₁ ← mkAppOptM ``CategoryTheory.cancel_epi
    #[C, none, none, none, none, inv_left_to_append.expr, none, new_lhs₀, new_rhs₀]
  let iff_proof ← mkAppOptM ``Iff.trans #[new_eq, none, none, iff_proof₁, iff_proof₀]
  let iff₂ ← mkAppOptM ``Iff.trans #[new_eq, none, none, iff_proof, iff₁]
  let final_lhs ← cancelIsoAssoc new_lhs
  let final_rhs ← cancelIsoAssoc new_rhs
  let iff₃ ← mkAppOptM ``Eq.congr #[none, final_lhs.expr, new_lhs, final_rhs.expr, new_rhs,
    ← mkEqSymm (← final_lhs.getProof), ← mkEqSymm (← final_rhs.getProof)]
  let iff_final ← mkAppOptM ``Iff.trans #[none, none, none, iff₃, iff₂]
  trace[rotate_isos] "iff_final type : {← inferType <| iff_final}"
  return (← mkEq final_lhs.expr final_rhs.expr, iff_final)

/-- Wrapper to apply `rotateIsosCore` for expressions in binders. -/
def rotateIsosForallTelescope (e : Expr) (a b : ℕ) (rev : Bool) : MetaM Expr := do
  mapForallTelescope (fun e => do
    mkAppM ``Iff.mpr #[(← rotateIsosCore (← inferType e) a b rev).2, e]) e

/-- Wrapper to apply `rotateIsosCore` for expressions in binders. -/
def rotateIsosForallTelescopeIff (e : Expr) (a b : ℕ) (rev : Bool) : MetaM Expr := do
  mapForallTelescope (fun e => do
    return ← mkAppM ``Iff.symm #[(← rotateIsosCore (← inferType e) a b rev).2]) e

open Term in
/-- A term elaborator to produce the result of `rotate_isos` at a term. -/
elab "rotate_isos% " p:patternIgnore("←" <|> "<-")? ppSpace n:num ppSpace m:num ppSpace t:term :
    term => do rotateIsosForallTelescope (← elabTerm t none) n.getNat m.getNat p.isSome

open Term in
/-- A term elaborator to produce the iff statement between the given term and the result of
running `rotate_isos` at that term. -/
elab "rotate_isos_iff% " p:patternIgnore("←" <|> "<-")? ppSpace n:num ppSpace m:num ppSpace t:term :
    term => do rotateIsosForallTelescopeIff (← elabTerm t none) n.getNat m.getNat p.isSome

/-- Wrapper to run `rotateIsosForallTelescope` at a hypothesis in the local context. -/
def rotateIsosAtHyp (a b : ℕ) (rev : Bool) (h : FVarId) (g : MVarId) :
    TacticM MVarId := do
  let d ← h.getDecl
  let new_h ← rotateIsosForallTelescope (← instantiateMVars <| .fvar h) a b rev
  let g ← g.clear h
  let (_, g) ← g.note d.userName new_h
  return g

/-- Wrapper to run `rotateIsosForallTelescope` at the current goal. -/
def rotateIsosAtGoal (a b : ℕ) (rev : Bool) (g : MVarId) : TacticM MVarId := withMainContext do
  let gty ← whnfR <| ← instantiateMVars <| ← g.getType
  let forall_iff ← rotateIsosForallTelescopeIff (.mvar g) a b rev
  let target_type ← forallTelescope (← inferType forall_iff)
    (fun xs t => do mkForallFVars xs t.appArg!)
  let (args, _, _) ← forallMetaTelescope <| gty
  -- g' is for the new goal
  let g' ← mkFreshExprSyntheticOpaqueMVar (target_type) (← g.getTag)
  let e₂ ← mkLambdaFVars args <|
    ← mkAppM'
      (← mkAppM ``Iff.mpr #[← mkAppOptM' forall_iff (args.map pure)])
      #[← mkAppOptM' g' (args.map pure)]
  -- The metavariable `g` might be a syntheticOpaque MVar so IsDefeq can’t assign it.
  let _ ← isDefEq (← g.getType) (← instantiateMVars <| ← inferType e₂)
  let _ ← isDefEq (.mvar g) (← instantiateMVars e₂)
  g.assign e₂
  return (← instantiateMVars g').mvarId!

syntax (name := rotate_isos) "rotate_isos "
    ("←" <|> "<-")? ppSpace num ppSpace num ppSpace ("using " term)? (location)? : tactic

elab_rules : tactic |
    `(tactic| rotate_isos $[$rev]? $a:num $b:num $[using $use]? $[$loc]?) => do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    (atLocal := fun h => do
      if use.isSome then throwUnsupportedSyntax
      replaceMainGoal [← rotateIsosAtHyp a.getNat b.getNat rev.isSome h <| ← getMainGoal])
    (atTarget := withMainContext do
      replaceMainGoal [← rotateIsosAtGoal a.getNat b.getNat rev.isSome <| ← getMainGoal]
      if let some t := use then
        -- Needed to make the unusedSimpa linter happy with "using rfl"
        if t.raw.matchesIdent `rfl then
          evalTactic <| ← `(tactic|
            simp only [IsIso.inv_inv, Category.assoc, Category.id_comp, Category.comp_id]; done)
        else
          evalTactic <| ← `(tactic|
            simpa only [IsIso.inv_inv, Category.assoc, Category.id_comp,
              Category.comp_id] using $t))
    (failed := fun _ => throwError "rotate_isos failed")

end Mathlib.Tactic.CategoryTheory.RotateIsos
