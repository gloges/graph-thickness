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

/-- A **partial vertex labeling** (`VertexPLabeling V K` or `V →ᵥ. K`)
  is a map which assigns type `K` labels to a subset of the "vertices" of type `V`. -/
def VertexPLabeling (V K : Type*) := V → Option K

@[inherit_doc]
infixr:25 " →ᵥ. " => VertexPLabeling

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace VertexPLabeling

variable {V K : Type*}

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
section VertexSet

variable (l : V →ᵥ. K) (k : K)

def labeled : Set V := {v | ∃ k, l v = some k}

def unlabeled : Set V := {v | l v = none}

def vertexSet : Set V := {v | l v = some k}

variable {l k}

@[simp]
lemma mem_labeled_iff {v : V} : v ∈ l.labeled ↔ l v ≠ none := Option.ne_none_iff_exists'.symm

@[simp]
lemma mem_unlabeled_iff {v : V} : v ∈ l.unlabeled ↔ l v = none := Set.mem_ofPred

@[simp]
lemma mem_vertexSet_iff {v : V} : v ∈ l.vertexSet k ↔ l v = some k := Set.mem_ofPred

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

lemma vertexSet_subset : l.vertexSet k ⊆ l.labeled := fun _ h ↦ ⟨k, h⟩

end VertexSet
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end VertexPLabeling
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
