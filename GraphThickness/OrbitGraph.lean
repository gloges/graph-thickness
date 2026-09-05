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
