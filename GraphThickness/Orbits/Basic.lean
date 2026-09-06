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

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace Equiv.Perm

open MulAction

/-- The orbits of `V` under the action of `f`. -/
abbrev orbits (f : Perm V) := orbitRel.Quotient (Subgroup.zpowers f) V

variable {f : Perm V} {v w : V}

lemma exists_int_of_orbit_eq (h : (⟦v⟧ : f.orbits) = ⟦w⟧) : ∃ k : ℤ, v = (f ^ k) w := by
  obtain ⟨⟨_, k, rfl⟩, rfl⟩ := mem_orbit_iff.mp <| orbitRel_apply.mpr <| Quotient.exact h
  exact ⟨k, rfl⟩

/-- Orbits of fixed points contain exactly one element. -/
@[aesop safe forward]
lemma eq_of_orbit_eq_of_isFixedPt (hw : f w = w) (h : (⟦v⟧ : f.orbits) = ⟦w⟧) : v = w := by
  obtain ⟨k, hk⟩ := exists_int_of_orbit_eq h
  exact hk ▸ f.zpow_apply_eq_self_of_apply_eq_self hw k

/-- Orbits of the identity permutation contain exactly one element. -/
@[aesop safe forward]
lemma eq_of_one_orbit_eq (h : (⟦v⟧ : (1 : Perm V).orbits) = ⟦w⟧) : v = w :=
  eq_of_orbit_eq_of_isFixedPt rfl h

@[simp]
lemma orbit_eq_iff_eq_out_of_isFixedPt {x : f.orbits} (h : f v = v) :
    (⟦v⟧ : f.orbits) = x ↔ v = x.out :=
  ⟨fun h' ↦ h' ▸ (f.eq_of_orbit_eq_of_isFixedPt h <| Quotient.out_eq' ⟦v⟧).symm, by simp_all⟩

@[simp]
lemma one_orbit_eq_iff_eq_out (x : (1 : Perm V).orbits) :
    (⟦v⟧ : (1 : Perm V).orbits) = x ↔ v = x.out :=
  orbit_eq_iff_eq_out_of_isFixedPt rfl

/-- The equivalence between the orbits of the identity permutation and the underlying type. -/
@[simps]
noncomputable def orbitsEquiv : (1 : Perm V).orbits ≃ V where
  toFun := Quotient.out
  invFun := Quotient.mk''
  left_inv := Quotient.out_eq
  right_inv v := eq_of_one_orbit_eq <| Quotient.out_eq ⟦v⟧

end Equiv.Perm
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
