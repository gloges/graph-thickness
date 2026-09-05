/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import GraphThickness.Orbits.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
/-!

# Orbit graph

-/
@[expose] public section

universe uV

variable {V : Type uV}

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace SimpleGraph

open Equiv

variable (G : SimpleGraph V) (f : Perm V)

/-- The simple graph on the *orbits* of `V` under the action of `f` where two orbits are joined
  by an edge if they contain elements which are adjacent in `G`.

  This is a special case of `SimpleGraph.map`. -/
def orbitGraph : SimpleGraph f.orbits := G.map (.mk <| MulAction.orbitRel (Subgroup.zpowers f) V)

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Adj

variable {f} in
@[simp]
lemma orbitGraph_adj (x y : f.orbits) :
    (G.orbitGraph f).Adj x y ↔ x ≠ y ∧ ∃ v w : V, G.Adj v w ∧ ⟦v⟧ = x ∧ ⟦w⟧ = y :=
  G.map_adj' _ x y

variable {G} in
lemma orbitGraph_adj_apply {v w : V} (hadj : G.Adj v w) (hne : (⟦v⟧ : f.orbits) ≠ ⟦w⟧) :
    (G.orbitGraph f).Adj ⟦v⟧ ⟦w⟧ :=
  G.map_adj_apply' hadj hne

end Adj
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace Iso

/-- The isomorphism between the orbit graph induced by the identity permutation
  and the underlying graph. -/
noncomputable def orbitGraph : G.orbitGraph 1 ≃g G where
  toEquiv := Perm.orbitsEquiv
  map_rel_iff' := by aesop

end Iso
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Poset

@[simp]
lemma bot_orbitGraph : orbitGraph ⊥ f = ⊥ := by aesop

@[simp]
lemma top_orbitGraph : orbitGraph ⊤ f = ⊤ := by
  ext x y
  rw [orbitGraph_adj, top_adj, and_iff_left_iff_imp]
  exact fun h ↦ ⟨x.out, y.out, by simp [h]⟩

lemma orbitGraph_monotone : Monotone (orbitGraph · f) := map_monotone _

end Poset
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end SimpleGraph
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
