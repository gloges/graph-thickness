/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import GraphThickness.Orbit.Basic
public import GraphThickness.VertexPLabeling.Basic
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Set.Restrict
/-!

# Swap labeled permutation

-/
@[expose] public section

universe uV uK

variable {V : Type uV} {K : Type uK}

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace VertexPLabeling

open Equiv

variable (l : V →ᵥ. K)

/-- The permutation of `V ⊕ V` which is the identity on unlabeled vertices
  and `Sum.swap` on labeled vertices. -/
def swapLabeled : Perm (V ⊕ V) :=
  Function.Involutive.toPerm (fun x ↦ if (l ⊕g l) x = none then x else x.swap)
    fun x ↦ by rcases eq_or_ne ((l ⊕g l) x) none <;> simp_all

@[simp]
lemma swapLabeled_inl (v : V) : l.swapLabeled (.inl v) = if l v = none then .inl v else .inr v :=
  rfl

@[simp]
lemma swapLabeled_inr (v : V) : l.swapLabeled (.inr v) = if l v = none then .inr v else .inl v :=
  rfl

lemma swapLabeled_involutive : Function.Involutive l.swapLabeled := .toPerm_involutive _

@[simp]
lemma swapLabeled_swapLabeled (x : V ⊕ V) : l.swapLabeled (l.swapLabeled x) = x :=
  l.swapLabeled_involutive x

/-- `l.swapLabeled` acts as the identity on unlabeled vertices. -/
lemma unlabeled_domRestrict_swapLabeled :
    (l ⊕g l).unlabeled.domRestrict l.swapLabeled = Subtype.val := by aesop

/-- `l.swapLabeled` acts as `Sum.swap` on labeled vertices. -/
lemma labeled_domRestrict_swapLabeled :
    (l ⊕g l).labeled.domRestrict l.swapLabeled = Sum.swap ∘ Subtype.val := by aesop

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Pow

variable {k : ℤ}

@[simp]
lemma swapLabeled_pow_of_even (h : Even k) : l.swapLabeled ^ k = 1 := by
  obtain ⟨k, rfl⟩ := h
  have h_sq : l.swapLabeled ^ 2 = 1 := by ext; simp [Perm.coe_pow]
  induction k with
  | zero => rfl
  | succ _ _ => simp_all [← two_mul, mul_add, zpow_add]
  | pred _ _ => simp_all [← two_mul, mul_sub, zpow_sub]

@[simp]
lemma swapLabeled_pow_of_odd (h : Odd k) : l.swapLabeled ^ k = l.swapLabeled := by
  obtain ⟨_, rfl⟩ := h
  simp [zpow_add]

end Pow
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Orbits

variable {l} {v : V} {x y : V ⊕ V}

@[aesop safe forward]
lemma exists_eq_orbit (a : Orbit l.swapLabeled) : ∃ x : V ⊕ V, a = ⟦x, l.swapLabeled⟧ :=
  ⟨a.out, (Orbit.orbit_out_eq a).symm⟩

@[simp]
lemma orbit_eq_of_labeled (h : l v ≠ none) : ⟦.inl v, l.swapLabeled⟧ = ⟦.inr v, l.swapLabeled⟧ := by
  refine Quotient.sound <| MulAction.orbitRel_apply.mp <| MulAction.mem_orbit_iff.mp ?_
  use ⟨l.swapLabeled, Subgroup.mem_zpowers _⟩
  change l.swapLabeled (.inr v) = .inl v
  simp [h]

/-- Orbits under `l.swapLabeled` contain at most two elements. -/
@[aesop safe forward]
lemma eq_or_eq_swapLabeled_of_orbit_eq (h : ⟦x, l.swapLabeled⟧ = ⟦y, l.swapLabeled⟧) :
    x = y ∨ x = l.swapLabeled y := by
  obtain ⟨k, hk⟩ := Orbit.orbit_eq_iff_exists_int.mp h
  cases k.even_or_odd <;> simp_all

/-- Orbits under `l.swapLabeled` contain at most two elements. -/
@[simp]
lemma orbit_eq_iff_eq_or_eq_swapLabeled :
    ⟦x, l.swapLabeled⟧ = ⟦y, l.swapLabeled⟧ ↔ x = y ∨ x = l.swapLabeled y := by aesop

end Orbits
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Lift

/-- Lift the labeling `l ⊕g l` of `V ⊕ V` to a labeling of the orbits under `l.swapLabeled`. -/
protected def lift : Orbit l.swapLabeled →ᵥ. K := Quotient.lift (l ⊕g l) fun _ _ _ ↦ by aesop

@[simp]
lemma lift_apply (x : V ⊕ V) : l.lift ⟦x, l.swapLabeled⟧ = (l ⊕g l) x := rfl

end Lift
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section SwapOrbit

/-- `Sum.swap` mapped to the orbits of `V ⊕ V` under `l.swapLabeled`.

  `l.swapOrbit` sends `⟦x, l.swapLabeled⟧` to `⟦x.swap, l.swapLabeled⟧`. -/
def swapOrbit : Perm (Orbit l.swapLabeled) :=
  Function.Involutive.toPerm (Quotient.map Sum.swap <| by aesop) fun _ ↦ by aesop

@[simp]
lemma swapOrbit_apply (x : V ⊕ V) : l.swapOrbit ⟦x, l.swapLabeled⟧ = ⟦x.swap, l.swapLabeled⟧ := rfl

lemma swapOrbit_involutive : Function.Involutive l.swapOrbit := .toPerm_involutive _

@[simp]
lemma swapOrbit_swapOrbit (a : Orbit l.swapLabeled) : l.swapOrbit (l.swapOrbit a) = a :=
  l.swapOrbit_involutive _

@[simp]
lemma lift_swapOrbit_eq_lift (a : Orbit l.swapLabeled) : l.lift (l.swapOrbit a) = l.lift a := by
  aesop

end SwapOrbit
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end VertexPLabeling
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
