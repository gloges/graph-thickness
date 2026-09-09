/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import GraphThickness.Orbit.OrbitGraph
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
abbrev zipper : SimpleGraph (Orbit l.pairingPerm) := (G ⊕g H).orbitGraph l.pairingPerm

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Hom

/-- The graph homomorphism mapping `v : V` to `⟦.inl v⟧` in `l.zipper G H`. -/
def zipperLeft : G →g l.zipper G H where
  toFun v := ⟦.inl v, l.pairingPerm⟧
  map_rel' _ := by aesop

/-- The graph homomorphism mapping `v : V` to `⟦.inr v⟧` in `l.zipper G H`. -/
def zipperRight : H →g l.zipper G H where
  toFun v := ⟦.inr v, l.pairingPerm⟧
  map_rel' _ := by aesop

@[simp]
lemma zipperLeft_apply (v : V) : l.zipperLeft G H v = ⟦.inl v, l.pairingPerm⟧ := rfl

@[simp]
lemma zipperRight_apply (v : V) : l.zipperRight G H v = ⟦.inr v, l.pairingPerm⟧ := rfl

end Hom
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end VertexPLabeling
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
