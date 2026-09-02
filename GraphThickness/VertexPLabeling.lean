/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Data.PFun
/-!

# Partial vertex labeling

-/
@[expose] public section

universe u v

/-- A **partial vertex labeling** `VertexPLabeling V K` (or `V →ᵥ. K`)
  is a map which assigns type `K` labels to a subset of the "vertices" of type `V`. -/
def VertexPLabeling (V : Type u) (K : Type v) := V → Option K

@[inherit_doc]
infixr:25 " →ᵥ. " => VertexPLabeling

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace VertexPLabeling

open Option Set

variable {V : Type u} {K : Type v}

@[ext]
lemma ext {l l' : V →ᵥ. K} (h : ∀ v, l v = l' v) : l = l' := by
  funext v
  exact h v

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section VertexSets

variable (k : K) (l : V →ᵥ. K)

/-- The set of vertices which are labeled by `l`. -/
def labeled : Set V := {v | l v ≠ none}

/-- The set of vertices which are not labeled by `l`. -/
def unlabeled : Set V := {v | l v = none}

/-- The set of vertices which are assigned the label `k` by `l`. -/
def vertexSet : Set V := {v | l v = some k}

variable {l k}

@[simp]
lemma mem_labeled_iff {v : V} : v ∈ l.labeled ↔ l v ≠ none := mem_ofPred

@[simp]
lemma mem_unlabeled_iff {v : V} : v ∈ l.unlabeled ↔ l v = none := mem_ofPred

@[simp]
lemma mem_vertexSet_iff {v : V} : v ∈ l.vertexSet k ↔ l v = some k := mem_ofPred

variable (l k)

@[simp]
lemma labeled_compl : l.labeledᶜ = l.unlabeled := by
  ext
  simp

@[simp]
lemma unlabeled_compl : l.unlabeledᶜ = l.labeled := by
  ext
  simp

lemma isCompl_labeled_unlabeled : IsCompl l.labeled l.unlabeled := l.labeled_compl ▸ isCompl_compl

lemma vertexSet_subset : l.vertexSet k ⊆ l.labeled := fun _ h ↦ ne_none_iff_exists'.mpr ⟨k, h⟩

end VertexSets
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Remove

variable [DecidableEq K] (l : V →ᵥ. K) (k : K)

/-- Set all vertices labeled with `k` to be unlabeled. -/
def remove : V →ᵥ. K := fun v ↦ if l v = some k then none else l v

@[simp]
lemma remove_apply (v : V) : l.remove k v = if l v = some k then none else l v := rfl

@[simp]
lemma remove_labeled : (l.remove k).labeled = l.labeled \ l.vertexSet k := by
  ext
  simp [And.comm]

@[simp]
lemma remove_unlabeled : (l.remove k).unlabeled = l.unlabeled ∪ l.vertexSet k := by
  ext
  simp [or_iff_not_imp_right]

end Remove
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Update

variable [DecidableEq K] (l : V →ᵥ. K) (k k' : K)

/-- Change all `k` labels to `k'`. -/
def update : V →ᵥ. K := fun v ↦ if l v = some k then some k' else l v

@[simp]
lemma update_apply (v : V) : l.update k k' v = if l v = some k then some k' else l v := rfl

@[simp]
lemma update_same : l.update k k = l := by aesop

@[simp]
lemma update_labeled : (l.update k k').labeled = l.labeled := by aesop

@[simp]
lemma update_unlabeled : (l.update k k').unlabeled = l.unlabeled := by aesop

end Update
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section PartialOrder

variable {l l' : V →ᵥ. K}

/-- Two partial vertex labelings `l` and `l'` satisfy `l ≤ l'` iff they agree on all vertices
  which are labeled by `l`. -/
instance : LE (V →ᵥ. K) where
  le l l' := ∀ v, l v = none ∨ l v = l' v

lemma le_iff : l ≤ l' ↔ ∀ v, l v = none ∨ l v = l' v := Iff.rfl

/-- Forward direction of `le_iff` applied at the point `v` for use with `aesop`. -/
@[aesop norm forward]
lemma eq_none_or_eq_of_le (h : l ≤ l') (v : V) : l v = none ∨ l v = l' v := h v

-- TODO: Understand why adding the `aesop` tag to `le_iff` directly makes the proofs below fail.

instance : PartialOrder (V →ᵥ. K) where
  le_refl _ := by tauto
  le_trans _ _ _ _ _ _ := by aesop
  le_antisymm _ _ _ _ := by aesop

lemma labeled_subset_of_le (h : l ≤ l') : l.labeled ⊆ l'.labeled := fun _ ↦ by aesop

lemma unlabeled_subset_of_ge (h : l ≤ l') : l'.unlabeled ⊆ l.unlabeled := fun _ ↦ by aesop

lemma vertexSet_subset_of_le (k : K) (h : l ≤ l') : l.vertexSet k ⊆ l'.vertexSet k :=
  fun _ ↦ by aesop

lemma labeled_monotone : Monotone (labeled : (V →ᵥ. K) → Set V) := fun _ _ ↦ labeled_subset_of_le

lemma unlabeled_antitone : Antitone (unlabeled : (V →ᵥ. K) → Set V) :=
  fun _ _ ↦ unlabeled_subset_of_ge

lemma vertexSet_monotone (k : K) : Monotone (vertexSet k : (V →ᵥ. K) → Set V) :=
  fun _ _ ↦ vertexSet_subset_of_le k

end PartialOrder
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section OrderBot

/-- `⊥ : V →ᵥ. K` leaves all vertices unlabeled. -/
instance : OrderBot (V →ᵥ. K) where
  bot _ := none
  bot_le _ _ := Or.inl rfl

@[simp]
lemma bot_apply (v : V) : (⊥ : V →ᵥ. K) v = none := rfl

@[simp]
lemma bot_labeled : (⊥ : V →ᵥ. K).labeled = ∅ := by aesop

@[simp]
lemma bot_unlabeled : (⊥ : V →ᵥ. K).unlabeled = univ := by aesop

@[simp]
lemma bot_vertexSet (k : K) : (⊥ : V →ᵥ. K).vertexSet k = ∅ := by aesop

@[simp]
lemma bot_remove [DecidableEq K] (k : K) : (⊥ : V →ᵥ. K).remove k = ⊥ := rfl

@[simp]
lemma bot_update [DecidableEq K] (k k' : K) : (⊥ : V →ᵥ. K).update k k' = ⊥ := rfl

end OrderBot
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end VertexPLabeling
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
