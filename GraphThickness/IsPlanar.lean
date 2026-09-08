/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Clique
/-!

# Planar graphs

## Table of contents

- A. Maps
- B. Inequalities
- C. Examples

-/
@[expose] public section

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace SimpleGraph

universe uV uW

variable {V : Type uV} {W : Type uW}

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Convex in
/-- A simple graph is planar iff there exists an embedding `V ↪ ℝ²` such that there are no crossings
  when edges are drawn as straight lines connecting their respective endpoints.

  That nothing is lost by requiring edges be embedded in ℝ² as straight lines
  is the content of the **Fáry–Wagner theorem** for finite simple graphs and
  **Thomassen's theorem** for infinite simple graphs. -/
def IsPlanar (G : SimpleGraph V) : Prop :=
  ∃ f : V ↪ ℝ², ∀ v v' w w' : V, G.Adj v v' → G.Adj w w' →
    v ≠ w → v ≠ w' → v' ≠ w → v' ≠ w' → Disjoint [f v -[ℝ] f v'] [f w -[ℝ] f w']

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace IsPlanar

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
/- ## A. Maps -/
section Maps

lemma hom {G : SimpleGraph V} {H : SimpleGraph W} (f : H →g G) (hf : Function.Injective f)
    (hG : G.IsPlanar) : H.IsPlanar := by
  obtain ⟨g, hg⟩ := hG
  use ⟨g ∘ f, g.injective.comp hf⟩
  exact fun v v' w w' h₁ h₂ h₃ h₄ h₅ h₆ ↦ hg (f v) (f v') (f w) (f w') (f.map_adj h₁) (f.map_adj h₂)
    (fun h ↦ h₃ <| hf h) (fun h ↦ h₄ <| hf h) (fun h ↦ h₅ <| hf h) (fun h ↦ h₆ <| hf h)

/-- A graph that embeds into a planar graph is planar. -/
lemma embedding {G : SimpleGraph V} {H : SimpleGraph W} (f : H ↪g G) (hG : G.IsPlanar) :
    H.IsPlanar :=
  hG.hom f.toHom f.injective

/-- Planarity is preserved under graph isomorphism. -/
lemma iso {G : SimpleGraph V} {H : SimpleGraph W} (f : H ≃g G) (hG : G.IsPlanar) : H.IsPlanar :=
  hG.embedding f.toEmbedding

/-- An induced subgraph of a planar graph is planar. -/
lemma induce {G : SimpleGraph V} (s : Set V) (hG : G.IsPlanar) : (G.induce s).IsPlanar :=
  hG.embedding <| .induce s

/-- A subgraph of a planar simple graph is planar. -/
lemma mono {G H : SimpleGraph V} (h : H ≤ G) (hG : G.IsPlanar) : H.IsPlanar :=
  hG.hom (.ofLE h) fun _ _ h' ↦ h'

end Maps
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
/- ## B. Inequalities -/
section Inequalities

lemma ncard_edgeSet_le {G : SimpleGraph V} (h : 3 ≤ G.support.ncard) (hG : G.IsPlanar) :
    G.edgeSet.ncard ≤ 3 * G.support.ncard - 6 :=
  sorry

lemma ncard_edgeSet_le_of_triangleFree
    {G : SimpleGraph V} (h : 3 ≤ G.support.ncard) (h' : G.CliqueFree 3) (hG : G.IsPlanar) :
    G.edgeSet.ncard ≤ 2 * G.support.ncard - 4 :=
  sorry

end Inequalities
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
/- ## C. Examples -/
section Examples

/-- The empty graph is planar provided an embedding of `V` into the plane exists. -/
lemma emptyGraph (f : V ↪ ℝ²) : (emptyGraph V).IsPlanar := ⟨f, by simp⟩

/-- K₄ is planar. -/
lemma completeGraph_four : (completeGraph (Fin 4)).IsPlanar := sorry

/-- K₅ is non-planar. -/
lemma not_completeGraph_five : ¬(completeGraph (Fin 5)).IsPlanar := by
  refine fun h5 ↦ not_lt_of_ge (h5.ncard_edgeSet_le ?_) ?_
  · simp [support_top_of_nontrivial]
  · calc
      _ < 10 := by simp [support_top_of_nontrivial]
      _ = Nat.choose 5 2 := by decide
      _ = (completeGraph (Fin 5)).edgeSet.ncard := by
        simpa [← Set.fintypeCard_eq_ncard] using Sym2.card_diagSet_compl (α := Fin 5).symm

/-- Kₙ is planar iff `n < 5`. -/
lemma completeGraph_iff_lt_five {n : ℕ} : (completeGraph (Fin n)).IsPlanar ↔ n < 5 := by
  constructor <;> intro h
  · by_contra! hn
    exact not_completeGraph_five <| h.embedding <| .completeGraph <| Fin.castLEEmb hn
  · exact completeGraph_four.embedding <| .completeGraph <| Fin.castLEEmb (Nat.le_of_succ_le_succ h)

/-- Embeddings of types induce embeddings of complete bipartite graphs on those types. -/
protected def _root_.SimpleGraph.Embedding.completeBipartiteGraph
    {α β γ δ : Type*} (f : α ↪ γ) (g : β ↪ δ) :
    completeBipartiteGraph α β ↪g completeBipartiteGraph γ δ where
  toFun := Sum.map f g
  inj' _ _ _ := by grind
  map_rel_iff' := by aesop

/-- The isomorphism between `completeBipartiteGraph α β` and `completeBipartiteGraph β α`
  induced by `Sum.swap`. -/
def _root_.SimpleGraph.Iso.completeBipartiteGraphSwap {α β : Type*} :
    completeBipartiteGraph α β ≃g completeBipartiteGraph β α where
  toFun := Sum.swap
  invFun := Sum.swap
  map_rel_iff' := by simp
  left_inv := Sum.swap_leftInverse
  right_inv := Sum.swap_rightInverse

/-- K₂,ₙ is planar for all `n`. -/
lemma completeBipartiteGraph_two (n : ℕ) : (completeBipartiteGraph (Fin 2) (Fin n)).IsPlanar :=
  sorry

/-- K₃,₃ is non-planar. -/
lemma not_completeBipartiteGraph_three_three : ¬(completeBipartiteGraph (Fin 3) (Fin 3)).IsPlanar :=
  sorry

/-- Kₘ,ₙ is planar iff `m < 3` and `n < 3`. -/
lemma completeBipartiteGraph_iff_lt_three (m n : ℕ) :
    (completeBipartiteGraph (Fin m) (Fin n)).IsPlanar ↔ m < 3 ∨ n < 3 := by
  constructor <;> intro h
  · by_contra! hmn
    apply not_completeBipartiteGraph_three_three
    exact h.embedding <| .completeBipartiteGraph (Fin.castLEEmb hmn.1) (Fin.castLEEmb hmn.2)
  · rcases h with hm | hn
    · refine (completeBipartiteGraph_two n).embedding ?_
      exact .completeBipartiteGraph (Fin.castLEEmb <| Nat.le_of_succ_le_succ hm) (.refl _)
    · refine .iso .completeBipartiteGraphSwap ?_
      refine (completeBipartiteGraph_two m).embedding ?_
      exact .completeBipartiteGraph (Fin.castLEEmb <| Nat.le_of_succ_le_succ hn) (.refl _)

end Examples
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end IsPlanar
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end SimpleGraph
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
