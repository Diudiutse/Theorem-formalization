import CheckUniform

set_option autoImplicit false

noncomputable section

namespace TheoremOnePointOne

open scoped BigOperators Pointwise

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance (α : Type*) : DecidableEq α := Classical.decEq α

omit [Fintype V] [DecidableEq V] in
lemma graphAut_isPretransitive {G : SimpleGraph V}
    (hvt : IsVertexTransitive' G) :
    MulAction.IsPretransitive (GraphAut G) V := by
  refine MulAction.IsPretransitive.mk ?_
  intro x y
  obtain ⟨e, he⟩ := hvt x y
  exact ⟨e, by simpa [GraphAut.smul_def] using he⟩

lemma graphAut_fiber_card
    {G : SimpleGraph V} (hvt : IsVertexTransitive' G)
    (x y : V) :
    Fintype.card {e : GraphAut G // e • x = y} =
      Fintype.card (MulAction.stabilizer (GraphAut G) x) := by
  letI : MulAction.IsPretransitive (GraphAut G) V := graphAut_isPretransitive hvt
  obtain ⟨h, hh⟩ := hvt x y
  have hh' : h • x = y := by simpa [GraphAut.smul_def] using hh
  let e : {s : GraphAut G // s ∈ MulAction.stabilizer (GraphAut G) x} ≃
      {g : GraphAut G // g • x = y} :=
    { toFun := fun s => ⟨h * s.1, by
          rw [← smul_smul, s.2, hh']⟩
      invFun := fun g => ⟨h⁻¹ * g.1, by
          change (h⁻¹ * g.1) • x = x
          rw [← smul_smul, g.2, ← hh', inv_smul_smul]⟩
      left_inv := by
        intro s
        apply Subtype.ext
        simp
      right_inv := by
        intro g
        apply Subtype.ext
        simp }
  exact Fintype.card_congr e.symm

noncomputable def graphAutFiber
    {G : SimpleGraph V} (x z : V) : Finset (GraphAut G) :=
  Finset.univ.filter (fun e => e • x = z)

lemma graphAutFiber_card
    {G : SimpleGraph V} (hvt : IsVertexTransitive' G)
    (x z : V) :
    (graphAutFiber (G := G) x z).card =
      Fintype.card (MulAction.stabilizer (GraphAut G) x) := by
  classical
  rw [← graphAut_fiber_card hvt x z]
  rw [Fintype.card_subtype]
  rfl

lemma graphAutFiber_card_mul_card
    {G : SimpleGraph V} (hvt : IsVertexTransitive' G)
    (x z : V) :
    (graphAutFiber (G := G) x z).card * Fintype.card V =
      Fintype.card (GraphAut G) := by
  letI : MulAction.IsPretransitive (GraphAut G) V := graphAut_isPretransitive hvt
  letI : Fintype (MulAction.orbit (GraphAut G) x) := Fintype.ofFinite _
  have horb :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (GraphAut G) x
  have horbcard : Fintype.card (MulAction.orbit (GraphAut G) x) = Fintype.card V := by
    simpa using Fintype.card_congr
      (Equiv.setCongr (MulAction.orbit_eq_univ (GraphAut G) x))
  have hf := graphAutFiber_card hvt x z
  calc
    (graphAutFiber (G := G) x z).card * Fintype.card V =
        Fintype.card (MulAction.stabilizer (GraphAut G) x) * Fintype.card V := by rw [hf]
    _ = Fintype.card V * Fintype.card (MulAction.stabilizer (GraphAut G) x) :=
      Nat.mul_comm _ _
    _ = Fintype.card (MulAction.orbit (GraphAut G) x) *
        Fintype.card (MulAction.stabilizer (GraphAut G) x) := by rw [horbcard]
    _ = Fintype.card (GraphAut G) := horb

noncomputable def graphAutPairBad
    {G : SimpleGraph V} (x y : V) : Finset (GraphAut G) :=
  by
    classical
    exact Finset.univ.filter (fun e => e • x = y ∨ G.Adj (e • x) y)

noncomputable def graphAutTargets
    {G : SimpleGraph V} (y : V) : Finset V :=
  by
    classical
    letI : G.LocallyFinite := finiteNeighbor G
    exact insert y (G.neighborFinset y)

lemma graphAutTargets_card_le
    {G : SimpleGraph V} {d : ℕ} (hreg : IsRegularFinite G d) (y : V) :
    (graphAutTargets (G := G) y).card ≤ d + 1 := by
  classical
  letI : G.LocallyFinite := finiteNeighbor G
  have hdeg : G.degree y = d := by
    exact hreg y
  simp [graphAutTargets, SimpleGraph.card_neighborFinset_eq_degree, hdeg]

lemma graphAutPairBad_subset_biUnion
    {G : SimpleGraph V} (x y : V) :
    graphAutPairBad (G := G) x y ⊆
      (graphAutTargets (G := G) y).biUnion (fun z => graphAutFiber (G := G) x z) := by
  classical
  intro e he
  have he' := (Finset.mem_filter.mp he).2
  by_cases hxy : e • x = y
  · apply Finset.mem_biUnion.mpr
    refine ⟨y, by simp [graphAutTargets], ?_⟩
    simp [graphAutFiber, hxy]
  · have hadj : G.Adj y (e • x) :=
      (G.adj_comm (e • x) y).mp (he'.resolve_left hxy)
    apply Finset.mem_biUnion.mpr
    refine ⟨e • x, ?_, ?_⟩
    · simp [graphAutTargets, hadj]
    · simp [graphAutFiber]

lemma graphAutPairBad_card_mul_card
    {G : SimpleGraph V} {d : ℕ}
    (hvt : IsVertexTransitive' G) (hreg : IsRegularFinite G d)
    (x y : V) :
    (graphAutPairBad (G := G) x y).card * Fintype.card V ≤
      (d + 1) * Fintype.card (GraphAut G) := by
  classical
  have hsub := graphAutPairBad_subset_biUnion (G := G) x y
  let S : Finset V := graphAutTargets (G := G) y
  have hsubS : graphAutPairBad (G := G) x y ⊆
      S.biUnion (fun z => graphAutFiber (G := G) x z) := by
    simpa [S] using hsub
  have hbi := Finset.card_biUnion_le
    (s := S)
    (t := fun z => graphAutFiber (G := G) x z)
  have hcard := graphAutTargets_card_le hreg y
  calc
    (graphAutPairBad (G := G) x y).card * Fintype.card V ≤
        (S.biUnion
          (fun z => graphAutFiber (G := G) x z)).card * Fintype.card V :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hsubS)
    _ ≤ (∑ z ∈ S,
          (graphAutFiber (G := G) x z).card) * Fintype.card V :=
      Nat.mul_le_mul_right _ hbi
    _ = (∑ z ∈ S,
          (graphAutFiber (G := G) x z).card * Fintype.card V) := by
      rw [Finset.sum_mul]
    _ = (∑ _z ∈ S, Fintype.card (GraphAut G)) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact graphAutFiber_card_mul_card hvt x z
    _ = S.card * Fintype.card (GraphAut G) := by simp
    _ ≤ (d + 1) * Fintype.card (GraphAut G) :=
      Nat.mul_le_mul_right _ (by simpa [S] using hcard)

noncomputable def graphAutBad
    {G : SimpleGraph V} (F : Finset V) : Finset (GraphAut G) :=
  by
    classical
    exact (F.product F).biUnion
      (fun p => graphAutPairBad (G := G) p.1 p.2)

lemma graphAutBad_card_mul_card
    {G : SimpleGraph V} {d : ℕ}
    (hvt : IsVertexTransitive' G) (hreg : IsRegularFinite G d)
    (F : Finset V) :
    (graphAutBad (G := G) F).card * Fintype.card V ≤
      (d + 1) * (F.card * F.card) * Fintype.card (GraphAut G) := by
  classical
  let P : Finset (V × V) := F.product F
  let B : Finset (GraphAut G) :=
    P.biUnion (fun p => graphAutPairBad (G := G) p.1 p.2)
  have hB : graphAutBad (G := G) F = B := by
    simp [graphAutBad, P, B]
  have hbi := Finset.card_biUnion_le
    (s := P)
    (t := fun p => graphAutPairBad (G := G) p.1 p.2)
  have hpair : ∀ p ∈ P,
      (graphAutPairBad (G := G) p.1 p.2).card * Fintype.card V ≤
        (d + 1) * Fintype.card (GraphAut G) := by
    intro p hp
    exact graphAutPairBad_card_mul_card hvt hreg p.1 p.2
  rw [hB]
  calc
    B.card * Fintype.card V ≤
        (∑ p ∈ P, (graphAutPairBad (G := G) p.1 p.2).card) *
          Fintype.card V := Nat.mul_le_mul_right _ hbi
    _ = ∑ p ∈ P,
          (graphAutPairBad (G := G) p.1 p.2).card * Fintype.card V := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _p ∈ P, (d + 1) * Fintype.card (GraphAut G) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpair p hp
    _ = P.card * ((d + 1) * Fintype.card (GraphAut G)) := by simp
    _ = (d + 1) * (F.card * F.card) * Fintype.card (GraphAut G) := by
      simp [P, Nat.mul_assoc, Nat.mul_comm]

lemma exists_good_graphAut
    {G : SimpleGraph V} {d : ℕ}
    (hvt : IsVertexTransitive' G) (hreg : IsRegularFinite G d)
    (F : Finset V)
    (hsmall : (d + 1) * (F.card * F.card) < Fintype.card V) :
    ∃ e : GraphAut G, ∀ x ∈ F, ∀ y ∈ F,
      e • x ≠ y ∧ ¬ G.Adj (e • x) y := by
  classical
  let B := graphAutBad (G := G) F
  have hBbound := graphAutBad_card_mul_card hvt hreg F
  have hHpos : 0 < Fintype.card (GraphAut G) := by
    letI : Nonempty (GraphAut G) := ⟨1⟩
    exact Fintype.card_pos
  have hBlt : B.card < Fintype.card (GraphAut G) := by
    by_contra hnot
    have hle : Fintype.card (GraphAut G) ≤ B.card := Nat.not_lt.mp hnot
    have hmul : Fintype.card (GraphAut G) * Fintype.card V ≤
        B.card * Fintype.card V := Nat.mul_le_mul_right _ hle
    have hBbound' : B.card * Fintype.card V ≤
        Fintype.card (GraphAut G) * ((d + 1) * (F.card * F.card)) := by
      simpa [B, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hBbound
    have hchain : Fintype.card (GraphAut G) * Fintype.card V ≤
        Fintype.card (GraphAut G) * ((d + 1) * (F.card * F.card)) :=
      hmul.trans hBbound'
    have hnle : Fintype.card V ≤ (d + 1) * (F.card * F.card) :=
      Nat.le_of_mul_le_mul_left hchain hHpos
    exact (Nat.not_le_of_gt hsmall) hnle
  have hcardlt : B.card < (Finset.univ : Finset (GraphAut G)).card := by
    simpa using hBlt
  obtain ⟨e, heuniv, henot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardlt
  refine ⟨e, ?_⟩
  intro x hx y hy
  have hpair : e ∉ graphAutPairBad (G := G) x y := by
    intro hpair
    apply henot
    exact Finset.mem_biUnion.mpr
      ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, hpair⟩
  have hrel : ¬ (e • x = y ∨ G.Adj (e • x) y) := by
    intro hrel
    apply hpair
    simpa [graphAutPairBad] using hrel
  exact ⟨fun h => hrel (Or.inl h), fun h => hrel (Or.inr h)⟩

end TheoremOnePointOne

end
