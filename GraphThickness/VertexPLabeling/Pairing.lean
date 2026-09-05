/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import GraphThickness.VertexPLabeling.Basic
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

end VertexPLabeling
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
