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

end SimpleGraph
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
