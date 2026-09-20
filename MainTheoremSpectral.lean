import MainTheorem

set_option autoImplicit false

namespace MainTheorem

open scoped BigOperators InnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma adjacencyMatrix_isHermitian (G : SimpleGraph V) :
    Matrix.IsHermitian (adjacencyMatrix G) := by
  classical
  ext v w
  simp [adjacencyMatrix, SimpleGraph.adj_comm]

omit [DecidableEq V] in
lemma adjacencyMatrix_trace (G : SimpleGraph V) :
    Matrix.trace (adjacencyMatrix G) = 0 := by
  classical
  change Matrix.trace (G.adjMatrix ℝ) = 0
  exact G.trace_adjMatrix (α := ℝ)

omit [DecidableEq V] in
lemma adjacencyMatrix_regular_constant
    {G : SimpleGraph V} {d : ℕ}
    (hreg : IsRegularFinite G d) :
    Matrix.mulVec (adjacencyMatrix G) (Function.const V (1 : ℝ)) =
      Function.const V (d : ℝ) := by
  classical
  letI : G.LocallyFinite := finiteNeighbor G
  have hreg' : G.IsRegularOfDegree d := hreg
  ext v
  letI : Fintype (G.neighborSet v) := finiteNeighbor G v
  simpa [adjacencyMatrix] using
    (G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) hreg'
      (a := (1 : ℝ)) (v := v))

omit [DecidableEq V] in
lemma adjacencyMatrix_sq_diagonal
    (G : SimpleGraph V) (v : V) :
    (adjacencyMatrix G * adjacencyMatrix G) v v =
      (finiteDegree G v : ℝ) := by
  classical
  letI : G.LocallyFinite := finiteNeighbor G
  letI : Fintype (G.neighborSet v) := finiteNeighbor G v
  simpa [adjacencyMatrix, finiteDegree] using
    G.adjMatrix_mul_self_apply_self (α := ℝ) v

omit [DecidableEq V] in
lemma finiteDegree_eq_of_regular
    {G : SimpleGraph V} {d : ℕ} (hreg : IsRegularFinite G d) (v : V) :
    finiteDegree G v = d := by
  letI : G.LocallyFinite := finiteNeighbor G
  exact hreg v

omit [DecidableEq V] in
lemma adjacencyMatrix_sq_trace_of_regular
    {G : SimpleGraph V} {d : ℕ} (hreg : IsRegularFinite G d) :
    Matrix.trace (adjacencyMatrix G * adjacencyMatrix G) =
      (Fintype.card V : ℝ) * d := by
  classical
  letI : G.LocallyFinite := finiteNeighbor G
  rw [Matrix.trace]
  calc
    (∑ v : V, (adjacencyMatrix G * adjacencyMatrix G) v v) =
        ∑ v : V, (finiteDegree G v : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact adjacencyMatrix_sq_diagonal G v
    _ = ∑ _v : V, (d : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [finiteDegree_eq_of_regular hreg]
    _ = (Fintype.card V : ℝ) * d := by simp

lemma regular_constant_is_adjacencyEigenvalue
    {G : SimpleGraph V} {d : ℕ} [Nonempty V]
    (hreg : IsRegularFinite G d) :
    IsAdjacencyEigenvalue G (d : ℝ) := by
  classical
  let f : V → ℝ := Function.const V (1 : ℝ)
  refine ⟨f, ?_, ?_⟩
  · exact (Function.const_ne_zero).2 (by norm_num)
  · have hmul := adjacencyMatrix_regular_constant hreg
    rw [adjacencyOperator, Matrix.toLin'_apply']
    calc
      Matrix.mulVec (adjacencyMatrix G) f = Function.const V (d : ℝ) := by
        simpa [f] using hmul
      _ = (d : ℝ) • f := by
        ext v
        simp [f]

lemma adjacency_eigenvalue_of_hermitian_eigenvalue
    (G : SimpleGraph V) (i : V) :
    IsAdjacencyEigenvalue G ((adjacencyMatrix_isHermitian G).eigenvalues i) := by
  classical
  let hA : Matrix.IsHermitian (adjacencyMatrix G) := adjacencyMatrix_isHermitian G
  let b := hA.eigenvectorBasis
  refine ⟨(b i : V → ℝ), ?_, ?_⟩
  · intro h
    apply b.orthonormal.ne_zero i
    ext v
    exact congrFun h v
  · rw [adjacencyOperator, Matrix.toLin'_apply']
    simpa [b, hA] using hA.mulVec_eigenvectorBasis i

lemma adjacencyMatrix_trace_sq_eq_sum_eigenvalues_sq
    (G : SimpleGraph V) :
    Matrix.trace (adjacencyMatrix G * adjacencyMatrix G) =
      ∑ i : V, ((adjacencyMatrix_isHermitian G).eigenvalues i) ^ 2 := by
  classical
  let A := adjacencyMatrix G
  let hA : Matrix.IsHermitian A := adjacencyMatrix_isHermitian G
  let T := Matrix.toEuclideanLin A
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
    simpa [T, Matrix.toLpLin_apply] using
      congrArg (WithLp.toLp 2) (hA.mulVec_eigenvectorBasis i)
  change ⟪hA.eigenvectorBasis i, T (T (hA.eigenvectorBasis i))⟫_ℝ = _
  rw [hi, map_smul, hi]
  simp [inner_smul_right]
  ring

lemma regular_lapMatrix_toLin
    {G : SimpleGraph V} {d : ℕ} [DecidableRel G.Adj]
    (hreg : IsRegularFinite G d) :
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

lemma connected_degree_eigenspace_finrank_one
    {G : SimpleGraph V} {d : ℕ} [DecidableRel G.Adj]
    (hreg : IsRegularFinite G d) (hconn : G.Connected) :
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
    rw [regular_lapMatrix_toLin hreg]
    ext f v
    simp [sub_eq_add_neg]
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

lemma adjacencyEigenvalueMultiplicity_le_card
    (G : SimpleGraph V) (lam : ℝ) :
    adjacencyEigenvalueMultiplicity G lam ≤ Fintype.card V := by
  classical
  unfold adjacencyEigenvalueMultiplicity
  calc
    Module.finrank ℝ (LinearMap.ker (adjacencyOperator G - lam • LinearMap.id)) ≤
        Module.finrank ℝ (V → ℝ) := Submodule.finrank_le _
    _ = Fintype.card V := by
      exact Module.finrank_fintype_fun_eq_card ℝ

lemma adjacency_row_norm_sum
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
  simp [hfilter, hdeg]

lemma adjacency_eigenvalue_bounds
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
  have hrow : ∑ j ∈ Finset.univ.erase k, ‖adjacencyMatrix G k j‖ = (d : ℝ) :=
    adjacency_row_norm_sum hreg k
  have hdiag : adjacencyMatrix G k k = 0 := by
    simp [adjacencyMatrix, SimpleGraph.adjMatrix_apply]
  rw [Metric.mem_closedBall] at hk
  rw [hdiag, hrow] at hk
  have habs : |μ| ≤ (d : ℝ) := by
    simpa [Real.dist_eq] using hk
  exact abs_le.mp habs

lemma adjacency_eigenspace_map
    (G : SimpleGraph V) (μ : ℝ) :
    let A := adjacencyMatrix G
    let T := Matrix.toEuclideanLin A
    let e := WithLp.linearEquiv 2 ℝ (V → ℝ)
    Submodule.map e.toLinearMap (Module.End.eigenspace T μ) =
      Module.End.eigenspace (adjacencyOperator G) μ := by
  classical
  dsimp
  let e := WithLp.linearEquiv 2 ℝ (V → ℝ)
  let T := Matrix.toEuclideanLin (adjacencyMatrix G)
  have hconj : e.toLinearMap.comp T =
      (adjacencyOperator G).comp e.toLinearMap := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [Matrix.toLpLin_apply]
    rfl
  apply le_antisymm
  · intro y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← hxy]
    have hconj_x := congrArg (fun f => f x) hconj
    calc
      adjacencyOperator G (e x) = e (T x) := hconj_x.symm
      _ = e (μ • x) := by rw [hx]
      _ = μ • e x := e.map_smul μ x
  · intro y hy
    rw [Submodule.mem_map]
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    have hconj_y := congrArg (fun f => f (e.symm y)) hconj
    calc
      T (e.symm y) = e.symm (adjacencyOperator G y) := by
        apply e.injective
        simpa [e] using hconj_y
      _ = e.symm (μ • y) := by rw [hy]
      _ = μ • e.symm y := e.symm.map_smul μ y

lemma adjacency_eigenspace_finrank_eq
    (G : SimpleGraph V) (μ : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace
      (Matrix.toEuclideanLin (adjacencyMatrix G)) μ) =
      adjacencyEigenvalueMultiplicity G μ := by
  classical
  let e := WithLp.linearEquiv 2 ℝ (V → ℝ)
  let T := Matrix.toEuclideanLin (adjacencyMatrix G)
  have hmap : Submodule.map e.toLinearMap (Module.End.eigenspace T μ) =
      Module.End.eigenspace (adjacencyOperator G) μ := by
    simpa [e, T] using adjacency_eigenspace_map G μ
  have heq : Module.finrank ℝ (Module.End.eigenspace T μ) =
      Module.finrank ℝ (Module.End.eigenspace (adjacencyOperator G) μ) := by
    rw [← hmap]
    exact (LinearEquiv.submoduleMap e (Module.End.eigenspace T μ)).finrank_eq
  rw [heq]
  unfold adjacencyEigenvalueMultiplicity
  have hk : Module.End.eigenspace (adjacencyOperator G) μ =
      LinearMap.ker (adjacencyOperator G -
        μ • (LinearMap.id : (V → ℝ) →ₗ[ℝ] (V → ℝ))) := by
    ext x
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · intro h
      rw [h]
      exact sub_self _
    · intro h
      exact sub_eq_zero.mp h
  rw [hk]

lemma connected_degree_eigenspace_finrank_one_euclidean
    {G : SimpleGraph V} {d : ℕ} [DecidableRel G.Adj]
    (hreg : IsRegularFinite G d) (hconn : G.Connected) :
    Module.finrank ℝ (Module.End.eigenspace
      (Matrix.toEuclideanLin (adjacencyMatrix G)) (d : ℝ)) = 1 := by
  rw [adjacency_eigenspace_finrank_eq]
  exact connected_degree_eigenspace_finrank_one hreg hconn

lemma euclidean_hasEigenvalue_of_adjacency
    (G : SimpleGraph V) {μ : ℝ}
    (hμ : IsAdjacencyEigenvalue G μ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin (adjacencyMatrix G)) μ := by
  classical
  obtain ⟨f, hf, hLf⟩ := hμ
  let e := WithLp.linearEquiv 2 ℝ (V → ℝ)
  let T := Matrix.toEuclideanLin (adjacencyMatrix G)
  have hconj : e.toLinearMap.comp T =
      (adjacencyOperator G).comp e.toLinearMap := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [Matrix.toLpLin_apply]
    rfl
  let x : EuclideanSpace ℝ V := e.symm f
  have hx : x ∈ Module.End.eigenspace T μ := by
    rw [Module.End.mem_eigenspace_iff]
    apply e.injective
    have hconj_x := congrArg (fun g => g x) hconj
    calc
      e (T x) = adjacencyOperator G (e x) := hconj_x
      _ = adjacencyOperator G f := by rw [e.apply_symm_apply]
      _ = μ • f := hLf
      _ = μ • e x := by rw [e.apply_symm_apply]
  have hx0 : x ≠ 0 := by
    intro hx0
    apply hf
    rw [← e.apply_symm_apply f, ← show x = e.symm f by rfl, hx0]
    exact e.map_zero
  exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩

lemma adjacency_eigenvalue_of_euclidean_eigenvector
    (G : SimpleGraph V) {μ : ℝ} (x : EuclideanSpace ℝ V)
    (hx : Matrix.toEuclideanLin (adjacencyMatrix G) x = μ • x)
    (hx0 : x ≠ 0) : IsAdjacencyEigenvalue G μ := by
  classical
  let e := WithLp.linearEquiv 2 ℝ (V → ℝ)
  have hxe : e x ≠ 0 := by
    intro h
    apply hx0
    exact e.injective (by simpa using h)
  refine ⟨e x, hxe, ?_⟩
  have hconj : e.toLinearMap.comp (Matrix.toEuclideanLin (adjacencyMatrix G)) =
      (adjacencyOperator G).comp e.toLinearMap := by
    ext y
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [Matrix.toLpLin_apply]
    rfl
  have hconj_x := congrArg (fun g => g x) hconj
  calc
    adjacencyOperator G (e x) = e (Matrix.toEuclideanLin (adjacencyMatrix G) x) := hconj_x.symm
    _ = e (μ • x) := by rw [hx]
    _ = μ • e x := e.map_smul μ x

lemma euclidean_trace_square_eigenvalues
    (G : SimpleGraph V) :
    let A := adjacencyMatrix G
    let T := Matrix.toEuclideanLin A
    let hT : T.IsSymmetric :=
      (Matrix.isSymmetric_toEuclideanLin_iff).2 (adjacencyMatrix_isHermitian G)
    let hn : Module.finrank ℝ (EuclideanSpace ℝ V) = Fintype.card V := by simp
    ∑ i : Fin (Fintype.card V), (hT.eigenvalues hn i) ^ 2 =
      Matrix.trace (A * A) := by
  classical
  dsimp
  let A := adjacencyMatrix G
  let T := Matrix.toEuclideanLin A
  let hT : T.IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff).2 (adjacencyMatrix_isHermitian G)
  let hn : Module.finrank ℝ (EuclideanSpace ℝ V) = Fintype.card V := by simp
  have htrace : LinearMap.trace ℝ (EuclideanSpace ℝ V) (T * T) =
      Matrix.trace (A * A) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun V ℝ).toBasis]
    rw [show T = Matrix.toLin (EuclideanSpace.basisFun V ℝ).toBasis
        (EuclideanSpace.basisFun V ℝ).toBasis A by
      simpa only [T] using congrArg (fun f => f A)
        (Matrix.toEuclideanLin_eq_toLin_orthonormal (𝕜 := ℝ) (m := V) (n := V))]
    simp only [LinearMap.toMatrix_mul, LinearMap.toMatrix_toLin]
  rw [← htrace]
  rw [LinearMap.trace_eq_sum_inner (T * T) (hT.eigenvectorBasis hn)]
  apply Fintype.sum_congr
  intro i
  have hi := hT.apply_eigenvectorBasis hn i
  rw [Module.End.mul_eq_comp, LinearMap.comp_apply]
  rw [hi, map_smul, hi]
  simp [inner_smul_right]
  ring

end MainTheorem
