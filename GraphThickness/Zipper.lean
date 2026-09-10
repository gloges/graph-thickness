/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import GraphThickness.Orbit.OrbitGraph
public import GraphThickness.VertexPLabeling.SwapLabeled
public import Mathlib.Combinatorics.SimpleGraph.Sum
/-!

# Zipper

-/
@[expose] public section

universe uV uK

variable {V : Type uV} {K : Type uK}

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace VertexPLabeling

/-- The simple graph formed by merging `G` and `H` at the vertices labeled by `l`. -/
abbrev zipper (l : V →ᵥ. K) (G H : SimpleGraph V) : SimpleGraph (Orbit l.swapLabeled) :=
  (G ⊕g H).orbitGraph l.swapLabeled

variable (l : V →ᵥ. K)

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Hom

variable (G H : SimpleGraph V) (v : V)

/-- The graph homomorphism mapping `v : V` to `⟦.inl v⟧` in `l.zipper G H`. -/
def zipperLeft : G →g l.zipper G H where
  toFun v := ⟦.inl v, l.swapLabeled⟧
  map_rel' _ := by aesop

/-- The graph homomorphism mapping `v : V` to `⟦.inr v⟧` in `l.zipper G H`. -/
def zipperRight : H →g l.zipper G H where
  toFun v := ⟦.inr v, l.swapLabeled⟧
  map_rel' _ := by aesop

@[simp]
lemma zipperLeft_apply : l.zipperLeft G H v = ⟦.inl v, l.swapLabeled⟧ := rfl

@[simp]
lemma zipperRight_apply : l.zipperRight G H v = ⟦.inr v, l.swapLabeled⟧ := rfl

lemma zipperLeft_injective : Function.Injective (l.zipperLeft G H) := fun _ _ ↦ by aesop

lemma zipperRight_injective : Function.Injective (l.zipperRight G H) := fun _ _ ↦ by aesop

end Hom
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Mono

variable {G G' : SimpleGraph V} (hG : G ≤ G') {H H' : SimpleGraph V} (hH : H ≤ H')

include hG in
variable (H) in
lemma zipper_mono_left : l.zipper G H ≤ l.zipper G' H := fun _ _ _ ↦ by aesop

include hH in
variable (G) in
lemma zipper_mono_right : l.zipper G H ≤ l.zipper G H' := fun _ _ _ ↦ by aesop

include hG hH in
lemma zipper_mono : l.zipper G H ≤ l.zipper G' H' :=
  (l.zipper_mono_left hG H).trans (l.zipper_mono_right G' hH)

end Mono
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end VertexPLabeling
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
