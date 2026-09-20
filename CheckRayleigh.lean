import Theorem11Spectral

set_option autoImplicit false

namespace TheoremOnePointOne

open scoped InnerProductSpace BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
lemma rayleigh_le_of_eigenbasis
    (T : E →ₗ[ℝ] E)
    (b : OrthonormalBasis ι ℝ E)
    (θ : ι → ℝ) (lam : ℝ)
    (hθ : ∀ i, T (b i) = θ i • b i)
    (hbound : ∀ i, θ i ≤ lam) :
    ∀ x, ⟪T x, x⟫_ℝ ≤ lam * ‖x‖ ^ 2 := by
  intro x
  have hx := b.sum_repr' x
  have hTx : T x = ∑ i : ι, (⟪b i, x⟫_ℝ) • (θ i • b i) := by
    calc
      T x = T (∑ i : ι, (⟪b i, x⟫_ℝ) • b i) := by rw [hx]
      _ = ∑ i : ι, (⟪b i, x⟫_ℝ) • (θ i • b i) := by
        simp_rw [map_sum, map_smul, hθ]
  rw [hTx, sum_inner]
  simp only [inner_smul_left,
    starRingEnd_apply, star_trivial]
  rw [← b.sum_sq_inner_right x]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hiθ := hbound i
  nlinarith [sq_nonneg (⟪b i, x⟫_ℝ)]

lemma rayleigh_le_of_eigenbasis_except
    (T : E →ₗ[ℝ] E)
    (b : OrthonormalBasis ι ℝ E)
    (θ : ι → ℝ) (lam : ℝ) (i₀ : ι)
    (hθ : ∀ i, T (b i) = θ i • b i)
    (hbound : ∀ i, i ≠ i₀ → θ i ≤ lam)
    (x : E)
    (hx₀ : ⟪b i₀, x⟫_ℝ = 0) :
    ⟪T x, x⟫_ℝ ≤ lam * ‖x‖ ^ 2 := by
  have hx := b.sum_repr' x
  have hTx : T x = ∑ i : ι, (⟪b i, x⟫_ℝ) • (θ i • b i) := by
    calc
      T x = T (∑ i : ι, (⟪b i, x⟫_ℝ) • b i) := by rw [hx]
      _ = ∑ i : ι, (⟪b i, x⟫_ℝ) • (θ i • b i) := by
        simp_rw [map_sum, map_smul, hθ]
  rw [hTx, sum_inner]
  simp only [inner_smul_left,
    starRingEnd_apply, star_trivial]
  rw [← b.sum_sq_inner_right x]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hii : i = i₀
  · subst i
    simp [hx₀]
  · have hiθ := hbound i hii
    nlinarith [sq_nonneg (⟪b i, x⟫_ℝ)]

lemma rayleigh_le_on_const_orthogonal
    {G : SimpleGraph V} {d : ℕ} [DecidableRel G.Adj]
    (hreg : IsRegularFinite G d) (hconn : G.Connected) :
    ∀ x : EuclideanSpace ℝ V,
      ⟪x, WithLp.toLp 2 (Function.const V (1 : ℝ))⟫_ℝ = 0 →
      ⟪Matrix.toEuclideanLin (adjacencyMatrix G) x, x⟫_ℝ ≤
        (d : ℝ) * ‖x‖ ^ 2 := by
  classical
  let T := Matrix.toEuclideanLin (adjacencyMatrix G)
  let hT : T.IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff).2 (adjacencyMatrix_isHermitian G)
  let hn : Module.finrank ℝ (EuclideanSpace ℝ V) = Fintype.card V := by simp
  let b := hT.eigenvectorBasis hn
  let θ := hT.eigenvalues hn
  have hconst : IsAdjacencyEigenvalue G (d : ℝ) := by
    letI : Nonempty V := hconn.nonempty
    exact regular_constant_is_adjacencyEigenvalue hreg
  have hconstE : Module.End.HasEigenvalue T (d : ℝ) := by
    exact euclidean_hasEigenvalue_of_adjacency G hconst
  obtain ⟨i₀, hi₀⟩ := hT.exists_eigenvalues_eq hn hconstE
  have hθ : ∀ i, T (b i) = θ i • b i := by
    intro i
    exact hT.apply_eigenvectorBasis hn i
  have hbound : ∀ i, θ i ≤ (d : ℝ) := by
    intro i
    have hiE := hT.hasEigenvector_eigenvectorBasis hn i
    have hiA : IsAdjacencyEigenvalue G (θ i) :=
      adjacency_eigenvalue_of_euclidean_eigenvector G (b i)
        (hθ i) (b.orthonormal.ne_zero i)
    exact (adjacency_eigenvalue_bounds hreg hiA).2
  have hdim : Module.finrank ℝ (Module.End.eigenspace T (d : ℝ)) = 1 := by
    simpa [T] using connected_degree_eigenspace_finrank_one_euclidean hreg hconn
  let e := WithLp.linearEquiv 2 ℝ (V → ℝ)
  let u : EuclideanSpace ℝ V := e.symm (Function.const V (1 : ℝ))
  have hu0 : u ≠ 0 := by
    intro hu
    have hzero : (Function.const V (1 : ℝ) : V → ℝ) = 0 := by
      have hEu : e u = 0 := by
        rw [hu]
        exact e.map_zero
      simpa [u] using hEu
    obtain ⟨v⟩ := hconn.nonempty
    have := congrFun hzero v
    norm_num at this
  have huE : u ∈ Module.End.eigenspace T (d : ℝ) := by
    rw [Module.End.mem_eigenspace_iff]
    apply e.injective
    have hconj : e.toLinearMap.comp T =
        (adjacencyOperator G).comp e.toLinearMap := by
      ext y
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      rw [Matrix.toLpLin_apply]
      rfl
    have hconj_u := congrArg (fun f => f u) hconj
    calc
      e (T u) = adjacencyOperator G (e u) := hconj_u
      _ = adjacencyOperator G (Function.const V (1 : ℝ)) := by
        rw [e.apply_symm_apply]
      _ = (d : ℝ) • Function.const V (1 : ℝ) := by
        rw [adjacencyOperator, Matrix.toLin'_apply']
        calc
          Matrix.mulVec (adjacencyMatrix G) (Function.const V (1 : ℝ)) =
              Function.const V (d : ℝ) := adjacencyMatrix_regular_constant hreg
          _ = (d : ℝ) • Function.const V (1 : ℝ) := by
            ext v
            simp
      _ = e ((d : ℝ) • u) := by
        rw [e.map_smul, e.apply_symm_apply]
  have hbiE : b i₀ ∈ Module.End.eigenspace T (d : ℝ) := by
    rw [Module.End.mem_eigenspace_iff]
    rw [hθ i₀]
    have hi₀' : θ i₀ = (d : ℝ) := hi₀
    rw [hi₀']
  have hEeq : Module.End.eigenspace T (d : ℝ) =
      ℝ ∙ u := eq_span_singleton_of_mem_of_finrank_eq_one hdim huE hu0
  have hbiSpan : b i₀ ∈ (ℝ ∙ u) := by
    rw [← hEeq]
    exact hbiE
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hbiSpan
  intro x hx
  have hxu : ⟪u, x⟫_ℝ = 0 := by
    rw [real_inner_comm]
    simpa [u, e] using hx
  apply rayleigh_le_of_eigenbasis_except (ι := Fin (Fintype.card V))
    (E := EuclideanSpace ℝ V)
    T b θ (d : ℝ) i₀ hθ (fun i _ => hbound i) x
  rw [← hc, real_inner_smul_left, hxu, mul_zero]

lemma rayleigh_le_on_second_eigenvalue
    {G : SimpleGraph V} {d : ℕ} {lam : ℝ} [DecidableRel G.Adj]
    (hreg : IsRegularFinite G d) (hconn : G.Connected)
    (hlam : IsSecondAdjacencyEigenvalue G (d : ℝ) lam) :
    ∀ x : EuclideanSpace ℝ V,
      ⟪x, WithLp.toLp 2 (Function.const V (1 : ℝ))⟫_ℝ = 0 →
      ⟪Matrix.toEuclideanLin (adjacencyMatrix G) x, x⟫_ℝ ≤
        lam * ‖x‖ ^ 2 := by
  classical
  let T := Matrix.toEuclideanLin (adjacencyMatrix G)
  let hT : T.IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff).2 (adjacencyMatrix_isHermitian G)
  let hn : Module.finrank ℝ (EuclideanSpace ℝ V) = Fintype.card V := by simp
  let b := hT.eigenvectorBasis hn
  let θ := hT.eigenvalues hn
  have hθadj : ∀ i, IsAdjacencyEigenvalue G (θ i) := by
    intro i
    exact adjacency_eigenvalue_of_euclidean_eigenvector G
      (b i) (hT.apply_eigenvectorBasis hn i) (b.orthonormal.ne_zero i)
  have hθtop : ∀ i, θ i ≤ d := by
    intro i
    exact hlam.2.2.1 _ (hθadj i)
  have hconst : IsAdjacencyEigenvalue G (d : ℝ) := by
    letI : Nonempty V := hconn.nonempty
    exact regular_constant_is_adjacencyEigenvalue hreg
  have hconstE : Module.End.HasEigenvalue T (d : ℝ) := by
    exact euclidean_hasEigenvalue_of_adjacency G hconst
  obtain ⟨i₀, hi₀⟩ := hT.exists_eigenvalues_eq hn hconstE
  have hθi₀ : θ i₀ = d := hi₀
  have hcardtop :
      (Finset.univ.filter (fun i : Fin (Fintype.card V) => θ i = d)).card = 1 := by
    calc
      (Finset.univ.filter (fun i : Fin (Fintype.card V) => θ i = d)).card =
          Module.finrank ℝ (Module.End.eigenspace T (d : ℝ)) := by
        simpa [θ] using hT.card_filter_eigenvalues_eq hn (d : ℝ)
      _ = 1 := by
        simpa [T] using connected_degree_eigenspace_finrank_one_euclidean hreg hconn
  have hbound : ∀ i, i ≠ i₀ → θ i ≤ lam := by
    intro i hne
    have hnotd : θ i ≠ d := by
      intro hEq
      have hmem : i ∈ Finset.univ.filter
          (fun j : Fin (Fintype.card V) => θ j = d) := by
        simp [hEq]
      have hmem₀ : i₀ ∈ Finset.univ.filter
          (fun j : Fin (Fintype.card V) => θ j = d) := by
        simp [hθi₀]
      obtain ⟨a, ha, huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp hcardtop
      have hia : i = a := huniq i hmem
      have hi₀a : i₀ = a := huniq i₀ hmem₀
      exact hne (hia.trans hi₀a.symm)
    have hlt : θ i < d := lt_of_le_of_ne (hθtop i) hnotd
    exact hlam.2.2.2 _ (hθadj i) hlt
  have hdim : Module.finrank ℝ (Module.End.eigenspace T (d : ℝ)) = 1 := by
    simpa [T] using connected_degree_eigenspace_finrank_one_euclidean hreg hconn
  let e := WithLp.linearEquiv 2 ℝ (V → ℝ)
  let u : EuclideanSpace ℝ V := e.symm (Function.const V (1 : ℝ))
  have hu0 : u ≠ 0 := by
    intro hu
    have hzero : (Function.const V (1 : ℝ) : V → ℝ) = 0 := by
      have hEu : e u = 0 := by
        rw [hu]
        exact e.map_zero
      simpa [u] using hEu
    obtain ⟨v⟩ := hconn.nonempty
    have := congrFun hzero v
    norm_num at this
  have huE : u ∈ Module.End.eigenspace T (d : ℝ) := by
    rw [Module.End.mem_eigenspace_iff]
    apply e.injective
    have hconj : e.toLinearMap.comp T =
        (adjacencyOperator G).comp e.toLinearMap := by
      ext y
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      rw [Matrix.toLpLin_apply]
      rfl
    have hconj_u := congrArg (fun f => f u) hconj
    calc
      e (T u) = adjacencyOperator G (e u) := hconj_u
      _ = adjacencyOperator G (Function.const V (1 : ℝ)) := by
        rw [e.apply_symm_apply]
      _ = (d : ℝ) • Function.const V (1 : ℝ) := by
        rw [adjacencyOperator, Matrix.toLin'_apply']
        calc
          Matrix.mulVec (adjacencyMatrix G) (Function.const V (1 : ℝ)) =
              Function.const V (d : ℝ) := adjacencyMatrix_regular_constant hreg
          _ = (d : ℝ) • Function.const V (1 : ℝ) := by
            ext v
            simp
      _ = e ((d : ℝ) • u) := by
        rw [e.map_smul, e.apply_symm_apply]
  have hbiE : b i₀ ∈ Module.End.eigenspace T (d : ℝ) := by
    rw [Module.End.mem_eigenspace_iff]
    have hi := hT.apply_eigenvectorBasis hn i₀
    rw [hi₀] at hi
    exact hi
  have hEeq : Module.End.eigenspace T (d : ℝ) = ℝ ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim huE hu0
  have hbiSpan : b i₀ ∈ (ℝ ∙ u) := by
    rw [← hEeq]
    exact hbiE
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hbiSpan
  intro x hx
  have hxu : ⟪u, x⟫_ℝ = 0 := by
    rw [real_inner_comm]
    simpa [u, e] using hx
  apply rayleigh_le_of_eigenbasis_except (ι := Fin (Fintype.card V))
    (E := EuclideanSpace ℝ V) T b θ lam i₀
    (fun i => by
      change T (b i) = θ i • b i
      exact hT.apply_eigenvectorBasis hn i)
    hbound x
  rw [← hc, real_inner_smul_left, hxu, mul_zero]

end TheoremOnePointOne
