import MainTheoremSpectral

set_option autoImplicit false

namespace MainTheorem

open scoped BigOperators InnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

example (G : SimpleGraph V) (i : V) :
    IsAdjacencyEigenvalue G ((adjacencyMatrix_isHermitian G).eigenvalues i) := by
  let hA : Matrix.IsHermitian (adjacencyMatrix G) := adjacencyMatrix_isHermitian G
  let b := hA.eigenvectorBasis
  refine ⟨(b i : V → ℝ), ?_, ?_⟩
  · intro h
    apply b.orthonormal.ne_zero i
    ext v
    exact congrFun h v
  · rw [adjacencyOperator, Matrix.toLin'_apply']
    simpa [b, hA] using hA.mulVec_eigenvectorBasis i

example (G : SimpleGraph V) :
    Matrix.IsHermitian (adjacencyMatrix G * adjacencyMatrix G) := by
  have hA := adjacencyMatrix_isHermitian G
  exact (hA.commute_iff hA).1 (Commute.refl _)

example (G : SimpleGraph V) :
    Module.finrank ℝ (V → ℝ) = Fintype.card V := by
  simpa using (Module.finrank_fintype_fun_eq_card : Module.finrank ℝ (V → ℝ) = Fintype.card V)

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (T : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n) :
    LinearMap.trace ℝ E (T * T) =
      ∑ i : Fin n, (hT.eigenvalues hn i) ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner (T * T) (hT.eigenvectorBasis hn)]
  apply Fintype.sum_congr
  intro i
  have hi := hT.apply_eigenvectorBasis hn i
  change ⟪(hT.eigenvectorBasis hn) i, T (T ((hT.eigenvectorBasis hn) i))⟫_ℝ = _
  rw [hi, map_smul, hi]
  simp [inner_smul_right]
  ring

example (G : SimpleGraph V) (i : V) :
    Matrix.toEuclideanLin (adjacencyMatrix G) ((adjacencyMatrix_isHermitian G).eigenvectorBasis i) =
      (adjacencyMatrix_isHermitian G).eigenvalues i •
        (adjacencyMatrix_isHermitian G).eigenvectorBasis i := by
  simpa [Matrix.toEuclideanLin_apply] using
    congrArg (WithLp.toLp 2) ((adjacencyMatrix_isHermitian G).mulVec_eigenvectorBasis i)

example (G : SimpleGraph V) :
    Matrix.trace (adjacencyMatrix G * adjacencyMatrix G) =
      ∑ i : V, ((adjacencyMatrix_isHermitian G).eigenvalues i) ^ 2 := by
  let A := adjacencyMatrix G
  let hA : Matrix.IsHermitian A := adjacencyMatrix_isHermitian G
  let T := Matrix.toEuclideanLin A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have htrace : LinearMap.trace ℝ (EuclideanSpace ℝ V) (T * T) =
      Matrix.trace (A * A) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun V ℝ).toBasis]
    rw [show T = Matrix.toLin (EuclideanSpace.basisFun V ℝ).toBasis
        (EuclideanSpace.basisFun V ℝ).toBasis A by
      simpa only [T] using congrArg (fun f => f A)
        (Matrix.toEuclideanLin_eq_toLin_orthonormal (𝕜 := ℝ) (m := V) (n := V))]
    simp only [LinearMap.toMatrix_mul, LinearMap.toMatrix_toLin]
  rw [← htrace]
  rw [LinearMap.trace_eq_sum_inner (T * T) hA.eigenvectorBasis]
  apply Fintype.sum_congr
  intro i
  have hi : T (hA.eigenvectorBasis i) = hA.eigenvalues i • hA.eigenvectorBasis i := by
    simpa [T, Matrix.toEuclideanLin_apply] using
      congrArg (WithLp.toLp 2) (hA.mulVec_eigenvectorBasis i)
  change ⟪hA.eigenvectorBasis i, T (T (hA.eigenvectorBasis i))⟫_ℝ = _
  rw [hi, map_smul, hi]
  simp [inner_smul_right]
  ring

lemma check_regular_lapMatrix_toLin {G : SimpleGraph V} {d : ℕ}
    [DecidableRel G.Adj] (hreg : IsRegularFinite G d) :
    Matrix.toLin' (G.lapMatrix ℝ) =
      (d : ℝ) • LinearMap.id - adjacencyOperator G := by
  classical
  apply LinearMap.ext
  intro f
  funext v
  rw [Matrix.toLin'_apply, adjacencyOperator, Matrix.toLin'_apply']
  rw [SimpleGraph.lapMatrix_mulVec_apply]
  simp [adjacencyMatrix]
  have hdeg : @SimpleGraph.degree V G v (finiteNeighbor G v) = G.degree v := by
    have hsource : @SimpleGraph.degree V G v (finiteNeighbor G v) =
        @Fintype.card (G.neighborSet v) (finiteNeighbor G v) := by
      letI : Fintype (G.neighborSet v) := finiteNeighbor G v
      exact (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := v)).symm
    have hcard : @Fintype.card (G.neighborSet v) (finiteNeighbor G v) =
        @Fintype.card (G.neighborSet v) inferInstance := by
      exact @Fintype.card_congr (G.neighborSet v) (G.neighborSet v)
        (finiteNeighbor G v) inferInstance (Equiv.refl _)
    calc
      @SimpleGraph.degree V G v (finiteNeighbor G v) =
          @Fintype.card (G.neighborSet v) (finiteNeighbor G v) := hsource
      _ = @Fintype.card (G.neighborSet v) inferInstance := hcard
      _ = G.degree v := SimpleGraph.card_neighborSet_eq_degree (G := G) (v := v)
  rw [← hdeg, hreg v]
  congr 2
  ext u
  simp [SimpleGraph.neighborFinset]

example {G : SimpleGraph V} [DecidableRel G.Adj] (v : V) :
    @SimpleGraph.degree V G v (finiteNeighbor G v) = G.degree v := by
  have hsource : @SimpleGraph.degree V G v (finiteNeighbor G v) =
      @Fintype.card (G.neighborSet v) (finiteNeighbor G v) := by
    letI : Fintype (G.neighborSet v) := finiteNeighbor G v
    exact (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := v)).symm
  have hcard : @Fintype.card (G.neighborSet v) (finiteNeighbor G v) =
      @Fintype.card (G.neighborSet v) inferInstance := by
    exact @Fintype.card_congr (G.neighborSet v) (G.neighborSet v)
      (finiteNeighbor G v) inferInstance (Equiv.refl _)
  calc
    @SimpleGraph.degree V G v (finiteNeighbor G v) =
        @Fintype.card (G.neighborSet v) (finiteNeighbor G v) := hsource
    _ = @Fintype.card (G.neighborSet v) inferInstance := hcard
    _ = G.degree v := SimpleGraph.card_neighborSet_eq_degree (G := G) (v := v)

example {G : SimpleGraph V} (hconn : G.Connected) :
    Fintype.card G.ConnectedComponent = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  obtain ⟨v⟩ := hconn.nonempty
  refine ⟨G.connectedComponentMk v, ?_⟩
  intro c
  obtain ⟨w, rfl⟩ := c.exists_rep
  exact SimpleGraph.ConnectedComponent.sound (hconn w v)

example {G : SimpleGraph V} {d : ℕ} [DecidableRel G.Adj] (hreg : IsRegularFinite G d)
    (hconn : G.Connected) :
    Module.finrank ℝ (LinearMap.ker (adjacencyOperator G - (d : ℝ) • LinearMap.id)) = 1 := by
  classical
  letI : G.LocallyFinite := finiteNeighbor G
  have hlap : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ))) = 1 := by
    rw [← G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
    exact (Fintype.card_eq_one_iff.mpr (by
      obtain ⟨v⟩ := hconn.nonempty
      refine ⟨G.connectedComponentMk v, ?_⟩
      intro c
      obtain ⟨w, rfl⟩ := c.exists_rep
      exact SimpleGraph.ConnectedComponent.sound (hconn w v)))
  have heq : Matrix.toLin' (G.lapMatrix ℝ) =
      - (adjacencyOperator G - (d : ℝ) • LinearMap.id) := by
    rw [check_regular_lapMatrix_toLin hreg]
    ext f v
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hker : LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ)) =
      LinearMap.ker (adjacencyOperator G - (d : ℝ) • LinearMap.id) := by
    rw [heq]
    apply le_antisymm <;> intro f hf
    · rw [LinearMap.mem_ker] at hf ⊢
      exact neg_eq_zero.mp (by simpa using hf)
    · rw [LinearMap.mem_ker] at hf ⊢
      exact neg_eq_zero.mpr (by simpa using hf)
  rw [← hker]
  exact hlap

lemma check_nonpositive_spectrum_card_bound
    {n d : ℕ} (hd : 0 < d) (θ : Fin n → ℝ) (i₀ : Fin n)
    (hθtop : ∀ i, θ i ≤ d)
    (hθbottom : ∀ i, - (d : ℝ) ≤ θ i)
    (hθnonpos : ∀ i, i ≠ i₀ → θ i ≤ 0)
    (hθi₀ : θ i₀ = d)
    (htrace : ∑ i, θ i = 0)
    (htrace_sq : ∑ i, (θ i) ^ 2 = (n : ℝ) * d) :
    n ≤ 2 * d := by
  have hsq : ∀ i ∈ Finset.univ.erase i₀, (θ i) ^ 2 ≤ (d : ℝ) * (-θ i) := by
    intro i hi
    have hne : i ≠ i₀ := by simpa using (Finset.mem_erase.mp hi).1
    have hnonpos := hθnonpos i hne
    have hbottom := hθbottom i
    nlinarith
  have hsum_sq :
      ∑ i ∈ Finset.univ.erase i₀, (θ i) ^ 2 ≤
        (d : ℝ) * ∑ i ∈ Finset.univ.erase i₀, (-θ i) := by
    calc
      ∑ i ∈ Finset.univ.erase i₀, (θ i) ^ 2 ≤
        ∑ i ∈ Finset.univ.erase i₀, (d : ℝ) * (-θ i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hsq i hi
      _ = (d : ℝ) * ∑ i ∈ Finset.univ.erase i₀, (-θ i) := by
        rw [Finset.mul_sum]
  have hsum : ∑ i ∈ Finset.univ.erase i₀, θ i = -(d : ℝ) := by
    have hdecomp := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) θ
      (a := i₀) (Finset.mem_univ i₀)
    rw [hθi₀] at hdecomp
    linarith
  have hsum_neg : ∑ i ∈ Finset.univ.erase i₀, (-θ i) = (d : ℝ) := by
    rw [Finset.sum_neg_distrib θ]
    rw [hsum]
    ring
  have hsq_decomp := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun i => (θ i) ^ 2) (a := i₀) (Finset.mem_univ i₀)
  rw [hθi₀] at hsq_decomp
  have htotal : (n : ℝ) * d ≤ 2 * (d : ℝ) ^ 2 := by
    calc
      (n : ℝ) * d = ∑ i, (θ i) ^ 2 := htrace_sq.symm
      _ = (d : ℝ) ^ 2 + ∑ i ∈ Finset.univ.erase i₀, (θ i) ^ 2 := by
        linarith [hsq_decomp]
      _ ≤ (d : ℝ) ^ 2 + (d : ℝ) *
          ∑ i ∈ Finset.univ.erase i₀, (-θ i) := by
        gcongr
      _ = 2 * (d : ℝ) ^ 2 := by rw [hsum_neg]; ring
  have hdn : (0 : ℝ) < d := by exact_mod_cast hd
  have hreal : (n : ℝ) ≤ 2 * d := by nlinarith
  exact_mod_cast hreal

lemma check_adjacency_row_norm_sum
    {G : SimpleGraph V} {d : ℕ} (hreg : IsRegularFinite G d) (v : V) :
    ∑ j ∈ Finset.univ.erase v, ‖adjacencyMatrix G v j‖ = (d : ℝ) := by
  classical
  simp only [adjacencyMatrix, SimpleGraph.adjMatrix_apply]
  have hnorm (x : V) :
      ‖if G.Adj v x then (1 : ℝ) else 0‖ = if G.Adj v x then 1 else 0 := by
    by_cases hx : G.Adj v x <;> simp [hx]
  simp_rw [hnorm]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ.erase v).filter (fun j => G.Adj v j) = G.neighborFinset v := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      SimpleGraph.neighborFinset, Set.mem_toFinset, SimpleGraph.mem_neighborSet]
    constructor
    · intro h
      exact h.2
    · intro h
      refine ⟨⟨?_, trivial⟩, h⟩
      intro hj
      subst j
      exact G.loopless.irrefl v h
  have hcard :
      (Finset.filter (fun j => G.Adj v j) (Finset.univ.erase v)).card =
        G.degree v := by
    rw [hfilter]
    exact SimpleGraph.card_neighborFinset_eq_degree G v
  have hdeg : G.degree v = d := by
    have hsource : @SimpleGraph.degree V G v (finiteNeighbor G v) =
        @Fintype.card (G.neighborSet v) (finiteNeighbor G v) := by
      letI : Fintype (G.neighborSet v) := finiteNeighbor G v
      exact (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := v)).symm
    have hcard' : @Fintype.card (G.neighborSet v) (finiteNeighbor G v) =
        @Fintype.card (G.neighborSet v) inferInstance := by
      exact @Fintype.card_congr (G.neighborSet v) (G.neighborSet v)
        (finiteNeighbor G v) inferInstance (Equiv.refl _)
    calc
      G.degree v = @Fintype.card (G.neighborSet v) inferInstance :=
        (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := v)).symm
      _ = @Fintype.card (G.neighborSet v) (finiteNeighbor G v) := hcard'.symm
      _ = @SimpleGraph.degree V G v (finiteNeighbor G v) := hsource.symm
      _ = d := hreg v
  simp [hfilter, hcard, hdeg]

lemma check_adjacency_eigenvalue_bounds
    {G : SimpleGraph V} {d : ℕ} (hreg : IsRegularFinite G d) {μ : ℝ}
    (hμ : IsAdjacencyEigenvalue G μ) :
    - (d : ℝ) ≤ μ ∧ μ ≤ d := by
  classical
  obtain ⟨f, hf, heq⟩ := hμ
  have hμ' : Module.End.HasEigenvalue (Matrix.toLin' (adjacencyMatrix G)) μ := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hf⟩
    apply Module.End.mem_eigenspace_iff.mpr
    simpa [adjacencyOperator] using heq
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ'
  have hrow : ∑ j ∈ Finset.univ.erase k, ‖adjacencyMatrix G k j‖ = (d : ℝ) := by
    exact check_adjacency_row_norm_sum hreg k
  have hdiag : adjacencyMatrix G k k = 0 := by
    simp [adjacencyMatrix, SimpleGraph.adjMatrix_apply, G.loopless.irrefl]
  rw [Metric.mem_closedBall] at hk
  rw [hdiag, hrow] at hk
  have habs : |μ| ≤ (d : ℝ) := by
    simpa [Real.dist_eq] using hk
  exact abs_le.mp habs

end MainTheorem
