/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Maps
/-!

# Planar graphs

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
section Maps

/-- A graph that embeds into a planar graph is planar. -/
lemma embedding {G : SimpleGraph V} {H : SimpleGraph W} (f : H ↪g G) (hG : G.IsPlanar) :
    H.IsPlanar := by
  obtain ⟨g, hg⟩ := hG
  exact ⟨f.toEmbedding.trans g, fun v v' w w' ↦ by simpa using hg (f v) (f v') (f w) (f w')⟩

/-- Planarity is preserved under graph isomorphism. -/
lemma iso {G : SimpleGraph V} {H : SimpleGraph W} (f : H ≃g G) (hG : G.IsPlanar) : H.IsPlanar :=
  hG.embedding f.toEmbedding

/-- An induced subgraph of a planar graph is planar. -/
lemma induce {G : SimpleGraph V} (s : Set V) (hG : G.IsPlanar) : (G.induce s).IsPlanar :=
  hG.embedding <| .induce s

/-- A subgraph of a planar simple graph is planar. -/
lemma mono {G H : SimpleGraph V} (h : H ≤ G) (hG : G.IsPlanar) : H.IsPlanar := by
  obtain ⟨g, hg⟩ := hG
  exact ⟨g, fun v v' w w' hv hw ↦ hg v v' w w' (h hv) (h hw)⟩

end Maps
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end IsPlanar
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end SimpleGraph
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
