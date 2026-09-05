/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Perm.Support
/-!

# Orbit graph

-/
@[expose] public section

universe uV uW

variable {V : Type uV}

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace Equiv.Perm

open MulAction

/-- The orbits of `V` under the action of `f`. -/
abbrev orbits (f : Perm V) := orbitRel.Quotient (Subgroup.zpowers f) V

/-- The orbit of a fixed point contains exactly one element and therefore `Quotient.out`
  is uniquely determined. -/
@[simp]
lemma out_mk_of_fixedPoint {f : Perm V} {v : V} (h : f v = v) : (⟦v⟧ : f.orbits).out = v := by
  suffices ∀ w : V, (⟦w⟧ : f.orbits) = ⟦v⟧ → w = v by exact this _ (Quotient.out_eq _)
  intro w hw
  obtain ⟨⟨_, k, rfl⟩, rfl⟩ := mem_orbit_iff.mp <| orbitRel_apply.mpr <| Quotient.exact hw
  exact f.zpow_apply_eq_self_of_apply_eq_self h k

@[simp]
lemma out_mk_of_one_orbits (v : V) : (⟦v⟧ : (1 : Perm V).orbits).out = v :=
  out_mk_of_fixedPoint <| one_apply v

/-- The equivalence between the orbits of the identity permutation and the underlying type. -/
@[simps]
noncomputable def orbitsEquiv : (1 : Perm V).orbits ≃ V where
  toFun := Quotient.out
  invFun := Quotient.mk''
  left_inv := Quotient.out_eq
  right_inv v := out_mk_of_fixedPoint <| one_apply v

end Equiv.Perm
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

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
