/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

import SymmMonCoherence.Spans.Inclusions

/-! # Adjunctions and Spans

In this file, given an arrow `f : c ⟶ c'` in a category `C` with pullbacks,
the 1-cells `(Spans.inl C).map f.toloc` and
`(Spans.inr C).map f.op.toloc` are adjoint to each other in the bicategorical
sense.

We also give an explicit criterion to construct pseudofunctors out of spans
bicategories
-- TODO: everything here
-/
