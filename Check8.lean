import Theorem11Spectral

set_option autoImplicit false

namespace TheoremOnePointOne

open scoped BigOperators InnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma check_euclidean_hasEigenvalue_of_adjacency
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
    rw [Matrix.toEuclideanLin_apply]
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

lemma check_adjacency_eigenvalue_of_euclidean_eigenvector
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
    rw [Matrix.toEuclideanLin_apply]
    rfl
  have hconj_x := congrArg (fun g => g x) hconj
  calc
    adjacencyOperator G (e x) = e (Matrix.toEuclideanLin (adjacencyMatrix G) x) := hconj_x.symm
    _ = e (μ • x) := by rw [hx]
    _ = μ • e x := e.map_smul μ x

lemma check_trace_square_eigenvalues
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

end TheoremOnePointOne
