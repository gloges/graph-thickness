/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import GraphThickness.Orbits.Basic
public import GraphThickness.VertexPLabeling.Basic
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Set.Restrict
/-!

# Pairing

-/
@[expose] public section

universe uV uK

variable {V : Type uV} {K : Type uK}

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace VertexPLabeling

variable (l : V →ᵥ. K)

/-- The map which is `id` on unlabeled vertices and `swap` on labeled vertices. -/
def pairing : V ⊕ V → V ⊕ V :=
  fun x =>
    match (l ⊕g l) x with
    | none => x
    | some _ => x.swap

@[simp]
lemma pairing_inl (v : V) : l.pairing (.inl v) = if l v = none then .inl v else .inr v := by
  dsimp [pairing]
  aesop

@[simp]
lemma pairing_inr (v : V) : l.pairing (.inr v) = if l v = none then .inr v else .inl v := by
  dsimp [pairing]
  aesop

@[simp]
lemma pairing_apply_apply (x : V ⊕ V) : l.pairing (l.pairing x) = x := by aesop

lemma pairing_involutive : Function.Involutive l.pairing := l.pairing_apply_apply

/-- `l.pairing` acts as the identity on unlabeled vertices. -/
lemma unlabeled_domRestrict_pairing :
    (l ⊕g l).unlabeled.domRestrict l.pairing = Subtype.val := by aesop

/-- `l.pairing` acts as `Sum.swap` on labeled vertices. -/
lemma labeled_domRestrict_pairing :
    (l ⊕g l).labeled.domRestrict l.pairing = Sum.swap ∘ Subtype.val := by aesop

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Perm

open Equiv

/-- `l.pairing` as a permutation of `V ⊕ V`. -/
@[simps!]
def pairingPerm : Perm (V ⊕ V) := l.pairing_involutive.toPerm

lemma pairingPerm_involutive : Function.Involutive l.pairingPerm := l.pairing_involutive

@[simp]
lemma pairingPerm_pow_of_even {k : ℤ} (h : Even k) : l.pairingPerm ^ k = 1 := by
  obtain ⟨k, rfl⟩ := h
  have h_sq : l.pairingPerm ^ 2 = 1 := by ext; simp [Perm.coe_pow]
  induction k with
  | zero => rfl
  | succ n ih => simp_all [← two_mul, mul_add, zpow_add]
  | pred n ih => simp_all [← two_mul, mul_sub, zpow_sub]

@[simp]
lemma pairingPerm_pow_of_odd {k : ℤ} (h : Odd k) : l.pairingPerm ^ k = l.pairingPerm := by
  obtain ⟨_, rfl⟩ := h
  simp [zpow_add]

variable {l}

@[simp]
lemma orbit_eq_of_labeled {v : V} (h : l v ≠ none) :
    (⟦.inl v⟧ : l.pairingPerm.orbits) = ⟦.inr v⟧ := by
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mp
  apply MulAction.mem_orbit_iff.mp
  use ⟨l.pairingPerm, Subgroup.mem_zpowers _⟩
  change l.pairing (.inr v) = .inl v
  simp [h]

/-- Orbits under `l.pairingPerm` contain at most two elements. -/
@[aesop safe forward]
lemma eq_or_eq_pairing_of_orbit_eq {x y : V ⊕ V} (h : (⟦x⟧ : l.pairingPerm.orbits) = ⟦y⟧) :
    x = y ∨ x = l.pairing y := by
  obtain ⟨k, hk⟩ := Perm.exists_int_of_orbit_eq h
  cases k.even_or_odd <;> simp_all

/-- Orbits under `l.pairingPerm` contain at most two elements. -/
@[simp]
lemma orbit_eq_iff_eq_or_eq_pairing {x y : V ⊕ V} :
    (⟦x⟧ : l.pairingPerm.orbits) = ⟦y⟧ ↔ x = y ∨ x = l.pairing y := by
  aesop

end Perm
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end VertexPLabeling
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
