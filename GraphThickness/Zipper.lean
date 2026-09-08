/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import GraphThickness.Orbits.OrbitGraph
public import GraphThickness.VertexPLabeling.Pairing
public import Mathlib.Combinatorics.SimpleGraph.Sum
/-!

# Zipper

-/
@[expose] public section

universe uV uK

variable {V : Type uV} {K : Type uK}

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace VertexPLabeling

variable (l : V →ᵥ. K) (G H : SimpleGraph V)

/-- The simple graph formed by merging `G` and `H` at the vertices labeled by `l`. -/
abbrev zipper : SimpleGraph l.pairingPerm.orbits := (G ⊕g H).orbitGraph l.pairingPerm

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Adj

variable {l G H} {v w : V}

@[simp]
lemma zipper_adj_inl_inl_iff :
    (l.zipper G H).Adj ⟦.inl v⟧ ⟦.inl w⟧ ↔ G.Adj v w ∨ H.Adj v w ∧ l v ≠ none ∧ l w ≠ none := by
  aesop

@[simp]
lemma zipper_adj_inl_inr_iff :
    (l.zipper G H).Adj ⟦.inl v⟧ ⟦.inr w⟧ ↔ G.Adj v w ∧ l w ≠ none ∨ H.Adj v w ∧ l v ≠ none := by
  aesop

@[simp]
lemma zipper_adj_inr_inl_iff :
    (l.zipper G H).Adj ⟦.inr v⟧ ⟦.inl w⟧ ↔ G.Adj v w ∧ l v ≠ none ∨ H.Adj v w ∧ l w ≠ none := by
  aesop

@[simp]
lemma zipper_adj_inr_inr_iff :
    (l.zipper G H).Adj ⟦.inr v⟧ ⟦.inr w⟧ ↔ G.Adj v w ∧ l v ≠ none ∧ l w ≠ none ∨ H.Adj v w := by
  aesop

end Adj
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end VertexPLabeling
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
