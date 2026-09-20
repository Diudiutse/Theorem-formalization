import Theorem11Spectral

set_option autoImplicit false

namespace TheoremOnePointOne

open scoped InnerProductSpace BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma inner_basis (v : EuclideanSpace ℝ V) (y : V) :
    ⟪v, EuclideanSpace.basisFun V ℝ y⟫_ℝ = v.ofLp y := by
  rw [PiLp.inner_apply]
  simp [EuclideanSpace.basisFun_apply]

lemma inner_T_basis (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : EuclideanSpace ℝ V) (x : V) :
    ⟪v, Matrix.toEuclideanLin (adjacencyMatrix G)
        (EuclideanSpace.basisFun V ℝ x)⟫_ℝ =
      ∑ y : V, (if G.Adj x y then 1 else 0) *
        ⟪v, EuclideanSpace.basisFun V ℝ y⟫_ℝ := by
  classical
  rw [PiLp.inner_apply, Matrix.toLpLin_apply]
  simp only [EuclideanSpace.basisFun_apply]
  change (∑ y : V, ⟪v.ofLp y,
      (adjacencyMatrix G).mulVec (EuclideanSpace.single x 1).ofLp y⟫_ℝ) = _
  simp only [Matrix.mulVec, dotProduct, PiLp.single_apply]
  simp [adjacencyMatrix, SimpleGraph.adjMatrix_apply, SimpleGraph.adj_comm,
    PiLp.inner_apply]

lemma projector_edge_energy
    (G : SimpleGraph V) (d : ℕ) (lam : ℝ)
    [DecidableRel G.Adj]
    (hreg : IsRegularFinite G d)
    (P : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V)
    (α : ℝ)
    (hnorm : ∀ x : V, ‖P (EuclideanSpace.basisFun V ℝ x)‖ ^ 2 = α)
    (hproj : ∀ x y : V,
      ⟪P (EuclideanSpace.basisFun V ℝ x),
        P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ =
      ⟪P (EuclideanSpace.basisFun V ℝ x),
        EuclideanSpace.basisFun V ℝ y⟫_ℝ)
    (heigen : ∀ x : V,
      Matrix.toEuclideanLin (adjacencyMatrix G)
          (P (EuclideanSpace.basisFun V ℝ x)) =
        lam • P (EuclideanSpace.basisFun V ℝ x)) :
    ∀ x : V, ∑ y : V, (if G.Adj x y then
      ‖P (EuclideanSpace.basisFun V ℝ x) -
        P (EuclideanSpace.basisFun V ℝ y)‖ ^ 2 else 0) =
      2 * ((d : ℝ) - lam) * α := by
  classical
  have hdegree (x : V) :
      ∑ y : V, (if G.Adj x y then (1 : ℝ) else 0) = d := by
    have hsumNat :
        ∑ y : V, (if G.Adj x y then (1 : ℕ) else 0) = finiteDegree G x := by
      letI : Fintype (G.neighborSet x) := finiteNeighbor G x
      calc
        ∑ y : V, (if G.Adj x y then (1 : ℕ) else 0) =
            (Finset.filter (fun y => G.Adj x y) Finset.univ).card := by
          exact Finset.sum_boole (p := fun y : V => G.Adj x y)
            (s := (Finset.univ : Finset V))
        _ = (G.neighborFinset x).card := by
          congr 1
          ext y
          simp
        _ = finiteDegree G x := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          rfl
    calc
      ∑ y : V, (if G.Adj x y then (1 : ℝ) else 0) =
          (finiteDegree G x : ℝ) := by exact_mod_cast hsumNat
      _ = d := by exact_mod_cast finiteDegree_eq_of_regular hreg x
  have hT : (Matrix.toEuclideanLin (adjacencyMatrix G)).IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff).2 (adjacencyMatrix_isHermitian G)
  have hdiag (x : V) :
      ⟪P (EuclideanSpace.basisFun V ℝ x),
        EuclideanSpace.basisFun V ℝ x⟫_ℝ = α := by
    calc
      ⟪P (EuclideanSpace.basisFun V ℝ x),
          EuclideanSpace.basisFun V ℝ x⟫_ℝ =
          ⟪P (EuclideanSpace.basisFun V ℝ x),
            P (EuclideanSpace.basisFun V ℝ x)⟫_ℝ := (hproj x x).symm
      _ = ‖P (EuclideanSpace.basisFun V ℝ x)‖ ^ 2 :=
        real_inner_self_eq_norm_sq _
      _ = α := hnorm x
  have hcross (x : V) :
      ∑ y : V, (if G.Adj x y then (1 : ℝ) else 0) *
          ⟪P (EuclideanSpace.basisFun V ℝ x),
            P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ = lam * α := by
    have hsum := inner_T_basis G
      (P (EuclideanSpace.basisFun V ℝ x)) x
    have hsum' :
        ∑ y : V, (if G.Adj x y then (1 : ℝ) else 0) *
            ⟪P (EuclideanSpace.basisFun V ℝ x),
              P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ =
          ⟪P (EuclideanSpace.basisFun V ℝ x),
            Matrix.toEuclideanLin (adjacencyMatrix G)
              (EuclideanSpace.basisFun V ℝ x)⟫_ℝ := by
      rw [hsum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [hproj]
    calc
      _ = ⟪P (EuclideanSpace.basisFun V ℝ x),
          Matrix.toEuclideanLin (adjacencyMatrix G)
            (EuclideanSpace.basisFun V ℝ x)⟫_ℝ := hsum'
      _ = ⟪Matrix.toEuclideanLin (adjacencyMatrix G)
            (P (EuclideanSpace.basisFun V ℝ x)),
          EuclideanSpace.basisFun V ℝ x⟫_ℝ :=
        (hT _ _).symm
      _ = ⟪lam • P (EuclideanSpace.basisFun V ℝ x),
          EuclideanSpace.basisFun V ℝ x⟫_ℝ := by rw [heigen]
      _ = lam * ⟪P (EuclideanSpace.basisFun V ℝ x),
          EuclideanSpace.basisFun V ℝ x⟫_ℝ := by
        rw [real_inner_smul_left]
      _ = lam * α := by rw [hdiag]
  intro x
  have hfirst :
      ∑ y : V, (if G.Adj x y then (1 : ℝ) else 0) *
          ‖P (EuclideanSpace.basisFun V ℝ x)‖ ^ 2 = (d : ℝ) * α := by
    rw [← Finset.sum_mul]
    rw [hdegree, hnorm]
  have hsecond :
      ∑ y : V, (if G.Adj x y then (1 : ℝ) else 0) *
          ‖P (EuclideanSpace.basisFun V ℝ y)‖ ^ 2 = (d : ℝ) * α := by
    simp_rw [hnorm]
    rw [← Finset.sum_mul]
    rw [hdegree]
  calc
    ∑ y : V, (if G.Adj x y then
        ‖P (EuclideanSpace.basisFun V ℝ x) -
          P (EuclideanSpace.basisFun V ℝ y)‖ ^ 2 else 0) =
        ∑ y : V, ((if G.Adj x y then (1 : ℝ) else 0) *
          ‖P (EuclideanSpace.basisFun V ℝ x)‖ ^ 2 -
          2 * ((if G.Adj x y then (1 : ℝ) else 0) *
            ⟪P (EuclideanSpace.basisFun V ℝ x),
              P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ) +
          (if G.Adj x y then (1 : ℝ) else 0) *
            ‖P (EuclideanSpace.basisFun V ℝ y)‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hadj : G.Adj x y
      · simp [hadj, norm_sub_sq_real]
      · simp [hadj]
    _ = (d : ℝ) * α - 2 * (lam * α) + (d : ℝ) * α := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      rw [hfirst, hcross, hsecond]
    _ = 2 * ((d : ℝ) - lam) * α := by ring

end TheoremOnePointOne
