/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Perm.Support
/-!

# Permutation orbits

-/
@[expose] public section

universe uV

variable {V : Type uV}

open Equiv MulAction

/-- The orbits under the action of the permutation `f`. -/
def Orbit (f : Perm V) : Type uV := orbitRel.Quotient (Subgroup.zpowers f) V

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace Orbit

/-- Map `v` to its orbit under the action of `f`. -/
protected def mk (f : Perm V) (v : V) : Orbit f := ⟦v⟧

@[inherit_doc Orbit.mk]
notation "⟦" v ", " f "⟧" => Orbit.mk f v

variable {f : Perm V} {v w : V} (x : Orbit f)

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section OrbitEquality

@[simp]
lemma orbit_out_eq : ⟦x.out, f⟧ = x := Quotient.out_eq x

lemma orbit_eq_iff_exists_int : ⟦v, f⟧ = ⟦w, f⟧ ↔ ∃ k : ℤ, v = (f ^ k) w := by
  constructor
  · intro h
    obtain ⟨⟨_, k, rfl⟩, rfl⟩ := mem_orbit_iff.mp <| orbitRel_apply.mp <| Quotient.exact h
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    refine Quotient.sound <| orbitRel_apply.mp <| mem_orbit_iff.mp ?_
    exact ⟨⟨f ^ k, Subgroup.zpow_mem_zpowers f k⟩, rfl⟩

variable (f v) in
@[simp]
lemma orbit_zpow_apply_eq (k : ℤ) : ⟦(f ^ k) v, f⟧ = ⟦v, f⟧ := orbit_eq_iff_exists_int.mpr ⟨k, rfl⟩

end OrbitEquality
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section FixedPoints

/-- Orbits of fixed points contain exactly one element. -/
@[aesop safe forward]
lemma eq_of_orbit_eq_of_isFixedPt (hw : f w = w) (h : ⟦v, f⟧ = ⟦w, f⟧) : v = w := by
  obtain ⟨k, rfl⟩ := orbit_eq_iff_exists_int.mp h
  exact f.zpow_apply_eq_self_of_apply_eq_self hw k

variable {x} in
/-- Orbits of fixed points contain exactly one element. -/
@[simp]
lemma orbit_eq_iff_eq_out_of_isFixedPt (h : f v = v) : ⟦v, f⟧ = x ↔ v = x.out :=
  ⟨fun _ ↦ Eq.symm <| eq_of_orbit_eq_of_isFixedPt h <| by simp_all, by simp_all⟩

end FixedPoints
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section IdentityPerm

variable {x : Orbit 1}

/-- Orbits of the identity permutation contain exactly one element. -/
@[aesop safe forward]
lemma eq_of_orbit_one_eq (h : ⟦v, 1⟧ = ⟦w, 1⟧) : v = w := eq_of_orbit_eq_of_isFixedPt rfl h

@[simp]
lemma orbit_one_eq_iff_eq_out : ⟦v, 1⟧ = x ↔ v = x.out := orbit_eq_iff_eq_out_of_isFixedPt rfl

/-- The equivalence between the orbits of the identity permutation and the underlying type. -/
@[simps]
noncomputable def orbitEquiv : Orbit (1 : Perm V) ≃ V where
  toFun x := x.out
  invFun v := ⟦v, 1⟧
  left_inv := orbit_out_eq
  right_inv _ := eq_of_orbit_one_eq (orbit_out_eq _)

end IdentityPerm
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end Orbit
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
