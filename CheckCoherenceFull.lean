import CheckUniform
import CheckEdge

set_option autoImplicit false

namespace MainTheorem

open scoped InnerProductSpace BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma multiplicity_pos_of_eigenvalue'
    (G : SimpleGraph V) (lam : ℝ)
    (hlam : IsAdjacencyEigenvalue G lam) :
    0 < adjacencyEigenvalueMultiplicity G lam := by
  let K := LinearMap.ker (adjacencyOperator G - lam • LinearMap.id)
  have hne : K ≠ ⊥ := by
    intro hbot
    obtain ⟨f, hf, hfeq⟩ := hlam
    have hfmem : f ∈ K := by
      rw [LinearMap.mem_ker]
      simp [hfeq]
    have hfzero : f = 0 := by
      have : (f : V → ℝ) ∈ (⊥ : Submodule ℝ (V → ℝ)) := by
        simpa [hbot] using hfmem
      simpa using this
    exact hf hfzero
  exact (Module.finrank_pos_iff.mpr (by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact hne Submodule.eq_bot_of_subsingleton))

omit [Fintype V] [DecidableEq V] in
lemma norm_sub_le_walk''
    {E : Type*} [NormedAddCommGroup E]
    {G : SimpleGraph V} (Φ : V → E) (B : ℝ)
    (hstep : ∀ {u v : V}, G.Adj u v → ‖Φ u - Φ v‖ ≤ B)
    {u v : V} (p : G.Walk u v) :
    ‖Φ v - Φ u‖ ≤ (p.length : ℝ) * B := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have hs : ‖Φ u - Φ v‖ ≤ B := by
      simpa [norm_sub_rev] using hstep h
    have hsrev : ‖Φ v - Φ u‖ ≤ B := by
      simpa [norm_sub_rev] using hs
    have htri : ‖Φ w - Φ u‖ ≤ ‖Φ w - Φ v‖ + ‖Φ v - Φ u‖ := by
      calc
        ‖Φ w - Φ u‖ = ‖(Φ w - Φ v) + (Φ v - Φ u)‖ := by
          congr 1
          abel
        _ ≤ ‖Φ w - Φ v‖ + ‖Φ v - Φ u‖ := norm_add_le _ _
    have hlen : ((p.length + 1 : ℕ) : ℝ) * B =
        (p.length : ℝ) * B + B := by push_cast; ring
    rw [SimpleGraph.Walk.length_cons, hlen]
    exact htri.trans (add_le_add ih hsrev)

omit [DecidableEq V] in
lemma coherence_ball_bound'
    {G : SimpleGraph V} (hconn : G.Connected)
    (Φ : V → EuclideanSpace ℝ V) (α γ r : ℝ) (s : ℕ) (o : V)
    (hα : 0 < α) (hγ : 0 ≤ γ) (_hr : 0 ≤ r)
    (hαr : α * r = 1)
    (hnorm : ∀ x, ‖Φ x‖ ^ 2 = α)
    (hframe : ∀ x, ∑ z : V, (⟪Φ x, Φ z⟫_ℝ) ^ 2 = α)
    (hedge : ∀ {x y}, G.Adj x y → ‖Φ x - Φ y‖ ^ 2 ≤ 2 * γ * α)
    (hs : γ * (s : ℝ) ^ 2 ≤ 1 / 2) :
    (Set.ncard {x : V | G.dist x o ≤ s} : ℝ) ≤ 4 * r := by
  let B : ℝ := Real.sqrt (2 * γ * α)
  have hBsq : B ^ 2 = 2 * γ * α := by
    dsimp [B]
    exact Real.sq_sqrt (by positivity)
  have hB : 0 ≤ B := by dsimp [B]; exact Real.sqrt_nonneg _
  have hstep : ∀ {x y}, G.Adj x y → ‖Φ x - Φ y‖ ≤ B := by
    intro x y hxy
    apply (sq_le_sq₀ (norm_nonneg _) hB).mp
    rw [hBsq]
    exact hedge hxy
  let S : Finset V := (Set.toFinite {x : V | G.dist x o ≤ s}).toFinset
  have hS_mem : ∀ x ∈ S, G.dist x o ≤ s := by
    intro x hx
    simpa [S] using hx
  have hinner : ∀ x ∈ S, (α / 2 : ℝ) ≤ ⟪Φ o, Φ x⟫_ℝ := by
    intro x hx
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x o
    have hdist : (G.dist x o : ℝ) ≤ s := by
      exact_mod_cast hS_mem x hx
    have hbound : ‖Φ o - Φ x‖ ≤ (s : ℝ) * B := by
      have h₁ := norm_sub_le_walk'' Φ B hstep p
      rw [hp] at h₁
      exact h₁.trans (mul_le_mul_of_nonneg_right hdist hB)
    have hsq : ‖Φ o - Φ x‖ ^ 2 ≤ ((s : ℝ) * B) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbound
    have hmul : γ * (s : ℝ) ^ 2 * α ≤ α / 2 := by
      have := mul_le_mul_of_nonneg_right hs (le_of_lt hα)
      nlinarith
    have hsq' : ‖Φ o - Φ x‖ ^ 2 ≤ α := by
      have hsquare : ((s : ℝ) * B) ^ 2 =
          2 * γ * α * (s : ℝ) ^ 2 := by
        rw [mul_pow, hBsq]
        ring
      rw [hsquare] at hsq
      nlinarith [hsq, hmul]
    rw [norm_sub_sq_real, hnorm o, hnorm x] at hsq'
    nlinarith
  have hlow : (S.card : ℝ) * (α ^ 2 / 4) ≤
      (Finset.sum S (fun x => (⟪Φ o, Φ x⟫_ℝ) ^ 2)) := by
    calc
      (S.card : ℝ) * (α ^ 2 / 4) = (∑ _x ∈ S, (α ^ 2 / 4)) := by simp
      _ ≤ (∑ x ∈ S, (⟪Φ o, Φ x⟫_ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro x hx
        have hi := hinner x hx
        nlinarith [sq_nonneg (⟪Φ o, Φ x⟫_ℝ - α / 2)]
  have hupper : (∑ x ∈ S, (⟪Φ o, Φ x⟫_ℝ) ^ 2) ≤ α := by
    have hsub : S ⊆ Finset.univ := Finset.subset_univ S
    have hnonneg : ∀ x ∈ (Finset.univ : Finset V), x ∉ S →
        0 ≤ (⟪Φ o, Φ x⟫_ℝ) ^ 2 := by
      intro x hx hxs
      exact sq_nonneg _
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg).trans_eq (hframe o)
  have hcard : (S.card : ℝ) ≤ 4 * r := by
    have hdiv : (S.card : ℝ) ≤ 4 / α := by
      apply (le_div_iff₀ hα).2
      nlinarith [hlow, hupper]
    calc
      (S.card : ℝ) ≤ 4 / α := hdiv
      _ = 4 * r := by
        field_simp
        nlinarith [hαr]
  have hScard : Set.ncard {x : V | G.dist x o ≤ s} = S.card := by
    simp [S, Set.ncard_eq_toFinset_card']
  calc
    (Set.ncard {x : V | G.dist x o ≤ s} : ℝ) = (S.card : ℝ) := by
      rw [hScard]
    _ ≤ 4 * r := hcard

lemma projector_coherence_data
    (G : SimpleGraph V) (d : ℕ) (lam : ℝ)
    (hconn : G.Connected) (hreg : IsRegularFinite G d)
    (hvt : IsVertexTransitive G)
    (hlam : IsAdjacencyEigenvalue G lam) :
    ∃ α : ℝ, ∃ Φ : V → EuclideanSpace ℝ V,
      0 < α ∧
      α * ((Fintype.card V : ℝ) /
        (adjacencyEigenvalueMultiplicity G lam : ℝ)) = 1 ∧
      (∀ x, ‖Φ x‖ ^ 2 = α) ∧
      (∀ x, ∑ z : V, (⟪Φ x, Φ z⟫_ℝ) ^ 2 = α) ∧
      (∀ {x y}, G.Adj x y →
        ‖Φ x - Φ y‖ ^ 2 ≤
          2 * ((d : ℝ) - lam) * α) := by
  classical
  letI : Nonempty V := hconn.nonempty
  let T := Matrix.toEuclideanLin (adjacencyMatrix G)
  let U := Module.End.eigenspace T lam
  let P := U.starProjection
  let b := EuclideanSpace.basisFun V ℝ
  have hvt' : IsVertexTransitive' G := vertexTransitive'_of_original hvt
  have hmpos : 0 < adjacencyEigenvalueMultiplicity G lam :=
    multiplicity_pos_of_eigenvalue' G lam hlam
  have hUpos : 0 < Module.finrank ℝ U := by
    rw [show Module.finrank ℝ U = adjacencyEigenvalueMultiplicity G lam by
      exact adjacency_eigenspace_finrank_eq G lam]
    exact_mod_cast hmpos
  obtain ⟨α, hα, hnorm, hratio⟩ :=
    spectral_projector_uniform_norm G lam hvt' hUpos
  have hcard : 0 < (Fintype.card V : ℝ) := by positivity
  have hm : 0 < (adjacencyEigenvalueMultiplicity G lam : ℝ) := by
    exact_mod_cast hmpos
  have hαr : α * ((Fintype.card V : ℝ) /
      (adjacencyEigenvalueMultiplicity G lam : ℝ)) = 1 := by
    rw [hratio, adjacency_eigenspace_finrank_eq]
    field_simp
  let Φ : V → EuclideanSpace ℝ V := fun x => P (b x)
  have hproj (x y : V) :
      ⟪Φ x, Φ y⟫_ℝ = ⟪Φ x, b y⟫_ℝ := by
    have hmem : P (b x) ∈ U := U.starProjection_apply_mem _
    have h := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (K := U) ⟨P (b x), hmem⟩ (b y)
    exact h
  have heigen (x : V) : T (P (b x)) = lam • P (b x) := by
    exact Module.End.mem_eigenspace_iff.mp (U.starProjection_apply_mem _)
  have hframe : ∀ x, ∑ z : V, (⟪Φ x, Φ z⟫_ℝ) ^ 2 = α := by
    intro x
    have hsum := (EuclideanSpace.basisFun V ℝ).sum_sq_inner_right (P (b x))
    calc
      ∑ z : V, (⟪Φ x, Φ z⟫_ℝ) ^ 2 =
          ∑ z : V, (⟪b z, P (b x)⟫_ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hproj x z, real_inner_comm]
      _ = ‖P (b x)‖ ^ 2 := hsum
      _ = α := hnorm x
  have hedge : ∀ {x y}, G.Adj x y →
      ‖Φ x - Φ y‖ ^ 2 ≤ 2 * ((d : ℝ) - lam) * α := by
    intro x y hxy
    have henergy := projector_edge_energy G d lam hreg P α
      (by intro z; exact hnorm z) hproj heigen x
    have hnonneg : ∀ z : V, 0 ≤ (if G.Adj x z then
        ‖Φ x - Φ z‖ ^ 2 else 0) := by
      intro z
      positivity
    have hle : ‖Φ x - Φ y‖ ^ 2 ≤
        ∑ z : V, (if G.Adj x z then ‖Φ x - Φ z‖ ^ 2 else 0) := by
      have hle' := Finset.single_le_sum (s := (Finset.univ : Finset V))
        (a := y) (fun z hz => hnonneg z) (by simp)
      simpa [hxy] using hle'
    simpa [hxy] using hle.trans_eq henergy
  exact ⟨α, Φ, hα, hαr, hnorm, hframe, hedge⟩

end MainTheorem
