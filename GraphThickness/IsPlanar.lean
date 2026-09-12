/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.GroupTheory.GroupAction.Embedding
/-!

# Planar graphs

## Table of contents

- A. Maps
- B. Sums
- C. Inequalities
- D. Examples

-/
@[expose] public section

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace SimpleGraph

universe uV uW

variable {V : Type uV} {W : Type uW}

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- A planar embedding of `G` consists of an embedding `φ : V ↪ ℝ²` of the vertices into the plane
and a function `ψ : V → V → unitInterval → ℝ²` such that
  - for all `v w : V`, `ψ v w` is continuous,
  - for all `v w : V`, `ψ v w 0 = φ v` and `ψ v w 1 = φ w`, and
  - for all `v v' w w' : V` with `G.Adj v v'`, `G.Adj w w'`, `v ≠ w`, `v ≠ w'`, `v' ≠ w`
    and `v' ≠ w'`, the sets `ψ v v' '' Ioo 0 1` and `ψ w w' '' Ioo 0 1` are disjoint.
-/
def IsPlanarEmbedding (G : SimpleGraph V) (φ : V ↪ ℝ²) (ψ : V → V → unitInterval → ℝ²) : Prop :=
  (∀ v w : V, G.Adj v w → Continuous (ψ v w) ∧ ψ v w 0 = φ v ∧ ψ v w 1 = φ w) ∧
  ∀ v v' w w' : V, G.Adj v v' → G.Adj w w' → v ≠ w → v ≠ w' → v' ≠ w → v' ≠ w' →
    ∀ t t' : unitInterval, t ≠ 0 → t ≠ 1 → t' ≠ 0 → t' ≠ 1 → ψ v v' t ≠ ψ w w' t'

/-- Composing a planar embedding of `G` with a continuous embedding `ℝ² ↪ ℝ²`
  produces another planar embedding. -/
lemma IsPlanarEmbedding.comp {G : SimpleGraph V} {φ : V ↪ ℝ²} {ψ : V → V → unitInterval → ℝ²}
    (h : G.IsPlanarEmbedding φ ψ) (f : ℝ² ↪ ℝ²) (hf : Continuous f) :
    G.IsPlanarEmbedding (φ.trans f) fun v w ↦ f ∘ ψ v w := by
  refine ⟨fun v w hvw ↦ ⟨hf.comp (h.1 v w hvw).1, ?_, ?_⟩, ?_⟩
  · simpa using (h.1 v w hvw).2.1
  · simpa using (h.1 v w hvw).2.2
  · simpa using h.2

/-- `G` is *planar* if there exist `φ` and `γ` satisfying `G.IsPlanarEmbedding φ γ`. -/
def IsPlanar (G : SimpleGraph V) : Prop := ∃ φ γ, G.IsPlanarEmbedding φ γ

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace IsPlanar

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
/- ## A. Maps -/
section Maps

/-- `H` is planar if there exists an injective graph homomorphism into a planar graph `G`. -/
lemma hom {G : SimpleGraph V} {H : SimpleGraph W} (f : H →g G) (hf : Function.Injective f)
    (hG : G.IsPlanar) : H.IsPlanar := by
  obtain ⟨φ, ψ, hG⟩ := hG
  use ⟨φ ∘ f, φ.injective.comp hf⟩, fun v w ↦ ψ (f v) (f w)
  refine ⟨fun v w hvw ↦ hG.1 (f v) (f w) (f.map_adj hvw), fun v v' w w' h₁ h₂ h₃ h₄ h₅ h₆ ↦ ?_⟩
  exact hG.2 (f v) (f v') (f w) (f w') (f.map_adj h₁) (f.map_adj h₂)
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
/- ## B. Sums -/
section Sums

variable {G : SimpleGraph V} {H : SimpleGraph W}

lemma sum (hG : G.IsPlanar) (hH : H.IsPlanar) : (G ⊕g H).IsPlanar := by
  obtain ⟨φ₁, ψ₁, hG⟩ := hG
  obtain ⟨φ₂, ψ₂, hH⟩ := hH
  let c : ℝ² := !₂[2, 0]
  have hc : ‖c‖ = 2 := by simp [c, PiLp.norm_eq_of_L2]
  let f₁ : ℝ² ↪ ℝ² := Homeomorph.unitBall.toEmbedding.trans (.subtype _)
  let f₂ : ℝ² ↪ ℝ² := c +ᵥ f₁
  have h₁₂ : ∀ x y, f₁ x ≠ f₂ y := by
    intro x y h
    suffices ‖c‖ < 1 + 1 by nlinarith
    suffices h₁ : ∀ x, ‖f₁ x‖ < 1 by
      calc
        _ = ‖f₁ x + (c - f₂ y)‖ := by rw [h, add_sub_cancel]
        _ ≤ ‖f₁ x‖ + ‖c - f₂ y‖ := norm_add_le _ _
        _ < 1 + 1 := add_lt_add (h₁ x) (by simp [f₂, h₁ y])
    intro x
    have hlt : 0 < 1 + ‖x‖ ^ 2 := by nlinarith
    apply (sq_lt_one_iff₀ <| norm_nonneg _).mp
    apply (mul_lt_mul_iff_right₀ hlt).mp
    simp [f₁, Homeomorph.unitBall_apply_coe, OpenPartialHomeomorph.univUnitBall_apply, norm_smul,
      mul_pow, Real.sq_sqrt hlt.le, ← mul_assoc, mul_inv_cancel₀ hlt.ne']
  have hf₁ : Continuous f₁ := by simp [f₁, Function.Embedding.coe_trans, continuous_subtype_val]
  have hf₂ : Continuous f₂ := hf₁.const_vadd c
  let φ : V ⊕ W → ℝ² := Sum.elim (φ₁.trans f₁) (φ₂.trans f₂)
  have hφ : Function.Injective φ := by rintro (v | v) (w | w) h <;> simp_all [φ, Ne.symm]
  let ψ : V ⊕ W → V ⊕ W → unitInterval → ℝ² := fun x y ↦
    match x, y with
    | .inl v, .inl w => f₁ ∘ ψ₁ v w
    | .inr v, .inr w => f₂ ∘ ψ₂ v w
    | _, _ => 0
  use ⟨φ, hφ⟩, ψ
  constructor
  · rintro (v | v) (w | w) hadj <;> simp_all [φ, ψ, hG.1, hH.1, Continuous.comp]
  · rintro (v | v) (v' | v')
    · rintro (w | w) (w' | w') <;> simp_all [ψ, hG.2]
    · simp
    · simp
    · rintro (w | w) (w' | w') <;> simp_all [ψ, hH.2, Ne.symm]

lemma sum_iff : (G ⊕g H).IsPlanar ↔ G.IsPlanar ∧ H.IsPlanar :=
  ⟨fun h ↦ ⟨h.embedding .sumInl, h.embedding .sumInr⟩, fun h ↦ h.1.sum h.2⟩

end Sums
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
/- ## C. Inequalities -/
section Inequalities

set_option warn.sorry false in
lemma ncard_edgeSet_le {G : SimpleGraph V} (h : 3 ≤ G.support.ncard) (hG : G.IsPlanar) :
    G.edgeSet.ncard ≤ 3 * G.support.ncard - 6 :=
  sorry

set_option warn.sorry false in
lemma ncard_edgeSet_le_of_triangleFree
    {G : SimpleGraph V} (h : 3 ≤ G.support.ncard) (h' : G.CliqueFree 3) (hG : G.IsPlanar) :
    G.edgeSet.ncard ≤ 2 * G.support.ncard - 4 :=
  sorry

end Inequalities
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
/- ## D. Examples -/
section Examples

/-- The empty graph is planar provided an embedding of `V` into the plane exists. -/
lemma emptyGraph (f : V ↪ ℝ²) : (emptyGraph V).IsPlanar := ⟨f, 0, by simp, by simp⟩

set_option warn.sorry false in
/-- K₄ is planar. -/
lemma completeGraph_four : (completeGraph (Fin 4)).IsPlanar := sorry

/-- K₅ is non-planar. -/
lemma not_completeGraph_five : ¬(completeGraph (Fin 5)).IsPlanar := by
  refine fun h5 ↦ not_lt_of_ge (h5.ncard_edgeSet_le ?_) ?_
  · simp
  · calc
      _ < 10 := by simp
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

set_option warn.sorry false in
/-- K₂,ₙ is planar for all `n`. -/
lemma completeBipartiteGraph_two (n : ℕ) : (completeBipartiteGraph (Fin 2) (Fin n)).IsPlanar :=
  sorry

@[simp]
lemma _root_.SimpleGraph.completeBipartiteGraph_support [Nonempty V] [Nonempty W] :
    (completeBipartiteGraph V W).support = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  cases x <;> simp [mem_support]

@[simp]
lemma _root_.SimpleGraph.completeBipartiteGraph_edgeSet_ncard (m n : ℕ) :
    (completeBipartiteGraph (Fin m) (Fin n)).edgeSet.ncard = m * n := by
  let f : Fin m × Fin n → Sym2 (Fin m ⊕ Fin n) := fun (i, j) ↦ s(.inl i, .inr j)
  refine Set.ncard_eq_of_bijective (fun k hk ↦ f (finProdFinEquiv.symm ⟨k, hk⟩)) ?_ ?_ ?_
  · intro e he
    obtain ⟨x, y, hxy⟩ : ∃ x y : Fin m ⊕ Fin n, e.out = (x, y) := by use e.out.1, e.out.2
    rw [show e = Quot.mk _ (x, y) by simp [← hxy]] at he
    rw [show e = Quot.mk _ (x, y) by simp [← hxy]]
    cases x with
    | inl i =>
      cases y with
      | inl j => simp at he
      | inr j' =>
        use n * i + j', by nlinarith [i.2, j'.2]
        simp only [finProdFinEquiv_symm_apply, Fin.divNat, Fin.modNat, Nat.mul_add_mod_self_left,
          Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, Prod.swap_prod_mk,
          reduceCtorEq, and_self, or_false, f]
        constructor
        · refine Fin.eq_of_val_eq <| Nat.div_eq_of_lt_le ?_ ?_
          · linarith
          · simp [mul_comm, mul_add]
        · exact Fin.eq_of_val_eq <| Nat.mod_eq_of_lt j'.prop
    | inr i' =>
      cases y with
      | inl j =>
        use i' + n * j, by nlinarith [i'.2, j.2]
        simp only [finProdFinEquiv_symm_apply, Fin.divNat, Fin.modNat, Nat.add_mul_mod_self_left,
          Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, reduceCtorEq, and_self, Prod.swap_prod_mk,
          Sum.inl.injEq, Sum.inr.injEq, false_or, f]
        constructor
        · refine Fin.eq_of_val_eq <| Nat.div_eq_of_lt_le ?_ ?_
          · linarith
          · simp [mul_comm, mul_add, add_comm]
        · exact Fin.eq_of_val_eq <| Nat.mod_eq_of_lt i'.prop
      | inr j' => simp at he
  · exact fun _ _ ↦ by simp [f]
  · intro i j hi hj hf
    suffices i / n = j / n ∧ i % n = j % n by
      rw [← i.mod_add_div n, ← j.mod_add_div n, this.1, this.2]
    simp_all [f, Fin.divNat, Fin.modNat]

/-- K₃,₃ is non-planar. -/
lemma not_completeBipartiteGraph_three_three :
    ¬(completeBipartiteGraph (Fin 3) (Fin 3)).IsPlanar := by
  refine fun h33 ↦ not_lt_of_ge (h33.ncard_edgeSet_le_of_triangleFree (by simp) ?_) (by simp)
  refine cliqueFree_of_chromaticNumber_lt ?_
  rw [CompleteBipartiteGraph.chromaticNumber]
  norm_num

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
