/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Data.PFun
/-!

# Partial vertex labeling

-/
@[expose] public section

/-- A **partial vertex labeling** (`VertexPLabeling V K` or `V →ᵥ. K`)
  is a map which assigns type `K` labels to a subset of the "vertices" of type `V`. -/
def VertexPLabeling (V K : Type*) := V → Option K

@[inherit_doc]
infixr:25 " →ᵥ. " => VertexPLabeling
