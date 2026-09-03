/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Data.Set.Restrict
public import Mathlib.Order.BooleanAlgebra.Set
/-!

# Partial vertex labeling

-/
@[expose] public section

universe uV uW uK

/-- A **partial vertex labeling** `VertexPLabeling V K` (or `V →ᵥ. K`)
  is a map which assigns type `K` labels to a subset of the "vertices" of type `V`. -/
def VertexPLabeling (V : Type uV) (K : Type uK) := V → Option K

@[inherit_doc]
infixr:25 " →ᵥ. " => VertexPLabeling

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace VertexPLabeling

open Option Set

variable {V : Type uV} {W : Type uW} {K : Type uK}

@[ext]
lemma ext {l₁ l₂ : V →ᵥ. K} (h : ∀ v, l₁ v = l₂ v) : l₁ = l₂ := by
  funext v
  exact h v

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section VertexSets

variable (k : K) (l : V →ᵥ. K)

/-- The set of vertices which are not labeled by `l`. -/
def unlabeled : Set V := {v | l v = none}

/-- The set of vertices which are labeled by `l`. -/
def labeled : Set V := {v | l v ≠ none}

/-- The set of vertices which are assigned the label `k` by `l`. -/
def vertexSet : Set V := {v | l v = some k}

variable {k l}

@[simp]
lemma mem_unlabeled_iff {v : V} : v ∈ l.unlabeled ↔ l v = none := mem_ofPred

@[simp]
lemma mem_labeled_iff {v : V} : v ∈ l.labeled ↔ l v ≠ none := mem_ofPred

@[simp]
lemma mem_vertexSet_iff {v : V} : v ∈ l.vertexSet k ↔ l v = some k := mem_ofPred

variable (k l)

@[simp]
lemma unlabeled_compl : l.unlabeledᶜ = l.labeled := by aesop

@[simp]
lemma labeled_compl : l.labeledᶜ = l.unlabeled := by aesop

lemma isCompl_unlabeled_labeled : IsCompl l.unlabeled l.labeled := l.unlabeled_compl ▸ isCompl_compl

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
lemma remove_unlabeled : (l.remove k).unlabeled = l.unlabeled ∪ l.vertexSet k := by
  ext
  simp [or_iff_not_imp_right]

@[simp]
lemma remove_labeled : (l.remove k).labeled = l.labeled \ l.vertexSet k := by
  ext
  simp [And.comm]

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
lemma update_unlabeled : (l.update k k').unlabeled = l.unlabeled := by aesop

@[simp]
lemma update_labeled : (l.update k k').labeled = l.labeled := by aesop

end Update
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Sum

variable (l : V →ᵥ. K) (l' : W →ᵥ. K)

/-- The natural vertex labeling of `V ⊕ W` defined by vertex labelings of `V` and `W`. -/
protected def sum : V ⊕ W →ᵥ. K := Sum.elim l l'

@[inherit_doc]
infixl:60 " ⊕g " => VertexPLabeling.sum

@[simp]
lemma sum_inl (v : V) : (l ⊕g l') (.inl v) = l v := rfl

@[simp]
lemma sum_inr (w : W) : (l ⊕g l') (.inr w) = l' w := rfl

@[simp]
lemma sum_unlabeled : (l ⊕g l').unlabeled = .inl '' l.unlabeled ∪ .inr '' l'.unlabeled := by aesop

@[simp]
lemma sum_labeled : (l ⊕g l').labeled = .inl '' l.labeled ∪ .inr '' l'.labeled := by aesop

@[simp]
lemma sum_vertexSet (k : K) :
    (l ⊕g l').vertexSet k = .inl '' l.vertexSet k ∪ .inr '' l'.vertexSet k := by aesop

end Sum
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section PartialOrder

variable {l₁ l₂ : V →ᵥ. K}

/-- Two partial vertex labelings `l₁` and `l₂` satisfy `l₁ ≤ l₂` iff they agree on all vertices
  which are labeled by `l₁`. -/
instance : LE (V →ᵥ. K) where
  le l₁ l₂ := ∀ v, l₁ v = none ∨ l₁ v = l₂ v

lemma le_iff : l₁ ≤ l₂ ↔ ∀ v, l₁ v = none ∨ l₁ v = l₂ v := Iff.rfl

/-- Forward direction of `le_iff` applied at the vertex `v` for use with `aesop`. -/
@[aesop norm forward]
lemma eq_none_or_eq_of_le (h : l₁ ≤ l₂) (v : V) : l₁ v = none ∨ l₁ v = l₂ v := h v

-- TODO: Understand why adding the `aesop` tag to `le_iff` directly makes the proofs below fail.

instance : PartialOrder (V →ᵥ. K) where
  le_refl _ := by tauto
  le_trans _ _ _ _ _ _ := by aesop
  le_antisymm _ _ _ _ := by aesop

lemma unlabeled_subset_of_ge (h : l₁ ≤ l₂) : l₂.unlabeled ⊆ l₁.unlabeled := fun _ ↦ by aesop

lemma labeled_subset_of_le (h : l₁ ≤ l₂) : l₁.labeled ⊆ l₂.labeled := fun _ ↦ by aesop

lemma vertexSet_subset_of_le (k : K) (h : l₁ ≤ l₂) : l₁.vertexSet k ⊆ l₂.vertexSet k :=
  fun _ ↦ by aesop

lemma unlabeled_antitone : Antitone (unlabeled : (V →ᵥ. K) → Set V) :=
  fun _ _ ↦ unlabeled_subset_of_ge

lemma labeled_monotone : Monotone (labeled : (V →ᵥ. K) → Set V) := fun _ _ ↦ labeled_subset_of_le

lemma vertexSet_monotone (k : K) : Monotone (vertexSet k : (V →ᵥ. K) → Set V) :=
  fun _ _ ↦ vertexSet_subset_of_le k

variable {l₁' l₂' : W →ᵥ. K}

lemma sum_le_sum_iff : l₁ ⊕g l₁' ≤ l₂ ⊕g l₂' ↔ l₁ ≤ l₂ ∧ l₁' ≤ l₂' :=
  ⟨fun h ↦ ⟨fun v ↦ by simpa using h (.inl v), fun w ↦ by simpa using h (.inr w)⟩,
    fun _ _ ↦ by aesop⟩

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
lemma bot_unlabeled : (⊥ : V →ᵥ. K).unlabeled = univ := by aesop

@[simp]
lemma bot_labeled : (⊥ : V →ᵥ. K).labeled = ∅ := by aesop

@[simp]
lemma bot_vertexSet (k : K) : (⊥ : V →ᵥ. K).vertexSet k = ∅ := by aesop

@[simp]
lemma bot_remove [DecidableEq K] (k : K) : (⊥ : V →ᵥ. K).remove k = ⊥ := rfl

@[simp]
lemma bot_update [DecidableEq K] (k k' : K) : (⊥ : V →ᵥ. K).update k k' = ⊥ := rfl

@[simp]
lemma bot_sum_bot : (⊥ : V →ᵥ. K) ⊕g (⊥ : W →ᵥ. K) = ⊥ := by aesop

end OrderBot
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section Pairing

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

end Pairing
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end VertexPLabeling
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
