import CheckCoherenceFull
import CheckEdge

set_option autoImplicit false

namespace TheoremOnePointOne

open scoped InnerProductSpace BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def dirichletEnergy
    (G : SimpleGraph V) (d : ℕ) (f : EuclideanSpace ℝ V) : ℝ :=
  ⟪(d : ℝ) • f -
      Matrix.toEuclideanLin (adjacencyMatrix G) f, f⟫_ℝ

lemma dirichletEnergy_of_eigenvector
    {G : SimpleGraph V} {d : ℕ} {lam : ℝ}
    {f : EuclideanSpace ℝ V}
    (heigen : Matrix.toEuclideanLin (adjacencyMatrix G) f = lam • f) :
    dirichletEnergy G d f = ((d : ℝ) - lam) * ‖f‖ ^ 2 := by
  rw [dirichletEnergy, heigen, inner_sub_left]
  simp [real_inner_smul_left]
  ring

lemma projector_kernel_data
    (G : SimpleGraph V) (d : ℕ) (lam : ℝ)
    (hconn : G.Connected) (_hreg : IsRegularFinite G d)
    (hvt : IsVertexTransitive G)
    (hlam : IsAdjacencyEigenvalue G lam) :
    ∃ α : ℝ, ∃ P : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V,
      0 < α ∧
      α * ((Fintype.card V : ℝ) /
        (adjacencyEigenvalueMultiplicity G lam : ℝ)) = 1 ∧
      (∀ x, ‖P (EuclideanSpace.basisFun V ℝ x)‖ ^ 2 = α) ∧
      (∀ x y, ⟪P (EuclideanSpace.basisFun V ℝ x),
          P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ =
        ⟪P (EuclideanSpace.basisFun V ℝ x),
          EuclideanSpace.basisFun V ℝ y⟫_ℝ) ∧
      (∀ x, Matrix.toEuclideanLin (adjacencyMatrix G)
          (P (EuclideanSpace.basisFun V ℝ x)) =
        lam • P (EuclideanSpace.basisFun V ℝ x)) := by
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
  have hcardpos : 0 < (Fintype.card V : ℝ) := by positivity
  have hmpos' : 0 < (adjacencyEigenvalueMultiplicity G lam : ℝ) := by
    exact_mod_cast hmpos
  have hfinrank : Module.finrank ℝ U = adjacencyEigenvalueMultiplicity G lam := by
    simpa [T, U] using adjacency_eigenspace_finrank_eq G lam
  have hαr : α * ((Fintype.card V : ℝ) /
      (adjacencyEigenvalueMultiplicity G lam : ℝ)) = 1 := by
    rw [hratio, hfinrank]
    field_simp [ne_of_gt hcardpos, ne_of_gt hmpos']
  have hproj (x y : V) :
      ⟪P (b x), P (b y)⟫_ℝ = ⟪P (b x), b y⟫_ℝ := by
    have hmem : P (b x) ∈ U := U.starProjection_apply_mem _
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (K := U) ⟨P (b x), hmem⟩ (b y)
  have heigen (x : V) : T (P (b x)) = lam • P (b x) := by
    exact Module.End.mem_eigenspace_iff.mp (U.starProjection_apply_mem _)
  refine ⟨α, P, hα, hαr, ?_, ?_, ?_⟩
  · intro x
    exact hnorm x
  · intro x y
    exact hproj x y
  · intro x
    exact heigen x

lemma dirichletEnergy_smul
    {G : SimpleGraph V} {d : ℕ}
    (f : EuclideanSpace ℝ V) (c : ℝ) :
    dirichletEnergy G d (c • f) = c ^ 2 * dirichletEnergy G d f := by
  rw [dirichletEnergy, map_smul]
  have harg : (d : ℝ) • (c • f) - c •
      Matrix.toEuclideanLin (adjacencyMatrix G) f =
      c • ((d : ℝ) • f -
        Matrix.toEuclideanLin (adjacencyMatrix G) f) := by
    simp [smul_sub, smul_smul, mul_comm]
  rw [harg]
  simp [inner_smul_left, inner_smul_right,
    dirichletEnergy]
  ring

omit [DecidableEq V] in
lemma regular_neighborFinset_card
    {G : SimpleGraph V} {d : ℕ}
    (hreg : IsRegularFinite G d) (o : V)
    [Fintype (G.neighborSet o)] :
    (@SimpleGraph.neighborFinset V G o inferInstance).card = d := by
  classical
  have hsource : @SimpleGraph.degree V G o (finiteNeighbor G o) =
      @Fintype.card (G.neighborSet o) (finiteNeighbor G o) := by
    letI : Fintype (G.neighborSet o) := finiteNeighbor G o
    exact (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := o)).symm
  have hcard' : @Fintype.card (G.neighborSet o) (finiteNeighbor G o) =
      @Fintype.card (G.neighborSet o) inferInstance := by
    exact @Fintype.card_congr (G.neighborSet o) (G.neighborSet o)
      (finiteNeighbor G o) inferInstance (Equiv.refl _)
  have hdeg : @SimpleGraph.degree V G o inferInstance = d := by
    calc
      @SimpleGraph.degree V G o inferInstance =
          @Fintype.card (G.neighborSet o) inferInstance :=
        (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := o)).symm
      _ = @Fintype.card (G.neighborSet o) (finiteNeighbor G o) := hcard'.symm
      _ = @SimpleGraph.degree V G o (finiteNeighbor G o) := hsource.symm
      _ = d := hreg o
  rw [SimpleGraph.card_neighborFinset_eq_degree]
  exact hdeg

lemma projector_gram_sum
    {G : SimpleGraph V} {lam α : ℝ}
    [DecidableRel G.Adj]
    (P : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V)
    (hnorm : ∀ x, ‖P (EuclideanSpace.basisFun V ℝ x)‖ ^ 2 = α)
    (hproj : ∀ x y, ⟪P (EuclideanSpace.basisFun V ℝ x),
        P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ =
      ⟪P (EuclideanSpace.basisFun V ℝ x),
        EuclideanSpace.basisFun V ℝ y⟫_ℝ)
    (heigen : ∀ x, Matrix.toEuclideanLin (adjacencyMatrix G)
        (P (EuclideanSpace.basisFun V ℝ x)) =
      lam • P (EuclideanSpace.basisFun V ℝ x)) :
    ∀ x, ∑ y : V, (if G.Adj x y then (1 : ℝ) else 0) *
      ⟪P (EuclideanSpace.basisFun V ℝ x),
        P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ = lam * α := by
  classical
  have hT : (Matrix.toEuclideanLin (adjacencyMatrix G)).IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff).2 (adjacencyMatrix_isHermitian G)
  have hdiag (x : V) :
      ⟪P (EuclideanSpace.basisFun V ℝ x),
        EuclideanSpace.basisFun V ℝ x⟫_ℝ = α := by
    calc
      _ = ⟪P (EuclideanSpace.basisFun V ℝ x),
          P (EuclideanSpace.basisFun V ℝ x)⟫_ℝ := (hproj x x).symm
      _ = ‖P (EuclideanSpace.basisFun V ℝ x)‖ ^ 2 :=
        real_inner_self_eq_norm_sq _
      _ = α := hnorm x
  intro x
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
        EuclideanSpace.basisFun V ℝ x⟫_ℝ := (hT _ _).symm
    _ = ⟪lam • P (EuclideanSpace.basisFun V ℝ x),
        EuclideanSpace.basisFun V ℝ x⟫_ℝ := by rw [heigen]
    _ = lam * ⟪P (EuclideanSpace.basisFun V ℝ x),
        EuclideanSpace.basisFun V ℝ x⟫_ℝ := by rw [real_inner_smul_left]
    _ = lam * α := by rw [hdiag]

lemma projector_gram_sum_neighbor
    {G : SimpleGraph V} {lam α : ℝ}
    [DecidableRel G.Adj]
    (P : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V)
    (hnorm : ∀ x, ‖P (EuclideanSpace.basisFun V ℝ x)‖ ^ 2 = α)
    (hproj : ∀ x y, ⟪P (EuclideanSpace.basisFun V ℝ x),
        P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ =
      ⟪P (EuclideanSpace.basisFun V ℝ x),
        EuclideanSpace.basisFun V ℝ y⟫_ℝ)
    (heigen : ∀ x, Matrix.toEuclideanLin (adjacencyMatrix G)
        (P (EuclideanSpace.basisFun V ℝ x)) =
      lam • P (EuclideanSpace.basisFun V ℝ x))
    (o : V) [Fintype (G.neighborSet o)] :
    Finset.sum (@SimpleGraph.neighborFinset V G o inferInstance)
      (fun y => ⟪P (EuclideanSpace.basisFun V ℝ o),
        P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ) = lam * α := by
  classical
  have hsum := projector_gram_sum P hnorm hproj heigen o
  have hfilter :
      (Finset.univ.filter (fun y : V => G.Adj o y)) =
        @SimpleGraph.neighborFinset V G o inferInstance := by
    ext y
    simp [SimpleGraph.neighborFinset, SimpleGraph.mem_neighborSet]
  calc
    Finset.sum (@SimpleGraph.neighborFinset V G o inferInstance)
        (fun y => ⟪P (EuclideanSpace.basisFun V ℝ o),
          P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ) =
        Finset.sum (Finset.univ.filter (fun y : V => G.Adj o y))
          (fun y => ⟪P (EuclideanSpace.basisFun V ℝ o),
            P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ) := by rw [hfilter]
    _ = ∑ y : V, if G.Adj o y then
          ⟪P (EuclideanSpace.basisFun V ℝ o),
            P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ y : V, (if G.Adj o y then (1 : ℝ) else 0) *
          ⟪P (EuclideanSpace.basisFun V ℝ o),
            P (EuclideanSpace.basisFun V ℝ y)⟫_ℝ := by
      apply Fintype.sum_congr
      intro y
      by_cases h : G.Adj o y <;> simp [h]
    _ = lam * α := hsum

lemma norm_smul_sq_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (v : E) :
    ‖c • v‖ ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul]
  calc
    (‖c‖ * ‖v‖) ^ 2 = ‖c‖ ^ 2 * ‖v‖ ^ 2 := by ring
    _ = c ^ 2 * ‖v‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]

lemma lemma_2_2
    (G : SimpleGraph V) (d : ℕ) (lam : ℝ)
    (hd : 2 ≤ d)
    (hconn : G.Connected)
    (hreg : IsRegularFinite G d)
    (hvt : IsVertexTransitive G)
    (hlam : IsSecondAdjacencyEigenvalue G (d : ℝ) lam)
    (hlam_pos : 0 < lam) :
    ∃ o w : V, ∃ φ : EuclideanSpace ℝ V,
      G.Adj o w ∧
      Matrix.toEuclideanLin (adjacencyMatrix G) φ = lam • φ ∧
      φ.ofLp o = 1 ∧ φ.ofLp w ≤ 0 ∧
      ‖φ‖ ^ 2 ≤ (d : ℝ) *
        ((Fintype.card V : ℝ) /
          (adjacencyEigenvalueMultiplicity G lam : ℝ)) /
        ((d : ℝ) - lam) ∧
      dirichletEnergy G d φ ≤ (d : ℝ) *
        ((Fintype.card V : ℝ) /
          (adjacencyEigenvalueMultiplicity G lam : ℝ)) := by
  classical
  letI : Nonempty V := hconn.nonempty
  let b := EuclideanSpace.basisFun V ℝ
  let r : ℝ := (Fintype.card V : ℝ) /
    (adjacencyEigenvalueMultiplicity G lam : ℝ)
  let γ : ℝ := (d : ℝ) - lam
  obtain ⟨α, P, hα, hαr, hnorm, hproj, heigen⟩ :=
    projector_kernel_data G d lam hconn hreg hvt hlam.1
  have hγpos : 0 < γ := by
    dsimp [γ]
    exact sub_pos.mpr hlam.2.1
  have hγle : γ ≤ (d : ℝ) := by
    dsimp [γ]
    linarith
  have hrpos : 0 < r := by
    dsimp [r]
    have hcardpos : 0 < (Fintype.card V : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hmpos : 0 < adjacencyEigenvalueMultiplicity G lam :=
      multiplicity_pos_of_eigenvalue' G lam hlam.1
    have hmpos' : 0 <
        (adjacencyEigenvalueMultiplicity G lam : ℝ) := by
      exact_mod_cast hmpos
    exact div_pos hcardpos hmpos'
  have hrnonneg : 0 ≤ r := le_of_lt hrpos
  have hαne : α ≠ 0 := ne_of_gt hα
  have hαr' : α * r = 1 := by
    simpa [r] using hαr
  have hinv : α⁻¹ = r := by
    calc
      α⁻¹ = α⁻¹ * 1 := by ring
      _ = α⁻¹ * (α * r) := by rw [hαr']
      _ = r := by field_simp [hαne]
  have hcoord (x y : V) :
      (P (b x)).ofLp y =
        ⟪P (b x), P (b y)⟫_ℝ := by
    calc
      (P (b x)).ofLp y = ⟪P (b x), b y⟫_ℝ := by
        simpa [b] using (inner_basis (P (b x)) y).symm
      _ = ⟪P (b x), P (b y)⟫_ℝ := (hproj x y).symm
  have hdiag (x : V) :
      ⟪P (b x), P (b x)⟫_ℝ = α := by
    calc
      _ = ‖P (b x)‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = α := hnorm x
  have hKsym (x y : V) :
      ⟪P (b x), P (b y)⟫_ℝ =
        ⟪P (b y), P (b x)⟫_ℝ := by
    exact real_inner_comm _ _
  by_cases hbad : ∃ o w : V, G.Adj o w ∧
      ⟪P (b o), P (b w)⟫_ℝ ≤ 0
  · rcases hbad with ⟨o, w, how, hw⟩
    let φ : EuclideanSpace ℝ V := α⁻¹ • P (b o)
    have hφeigen : Matrix.toEuclideanLin (adjacencyMatrix G) φ = lam • φ := by
      dsimp [φ]
      simpa [smul_smul, b, EuclideanSpace.basisFun_apply, mul_comm] using
        congrArg (fun z => α⁻¹ • z) (heigen o)
    have hφo : φ.ofLp o = 1 := by
      dsimp [φ]
      change α⁻¹ * (P (b o)).ofLp o = 1
      rw [hcoord, hdiag]
      field_simp
    have hφw : φ.ofLp w ≤ 0 := by
      dsimp [φ]
      change α⁻¹ * (P (b o)).ofLp w ≤ 0
      rw [hcoord]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr hα)) hw
    have hφnorm : ‖φ‖ ^ 2 = r := by
      dsimp [φ]
      rw [norm_smul_sq_real, hnorm o]
      have : (α⁻¹) ^ 2 * α = r := by
        field_simp [hαne]
        nlinarith [hαr']
      exact this
    have hφenergy : dirichletEnergy G d φ = γ * r := by
      rw [dirichletEnergy_of_eigenvector hφeigen, hφnorm]
    refine ⟨o, w, φ, how, hφeigen, hφo, hφw, ?_, ?_⟩
    · rw [hφnorm]
      dsimp [r, γ]
      apply (le_div_iff₀ (sub_pos.mpr hlam.2.1)).2
      nlinarith
    · rw [hφenergy]
      nlinarith
  · have hgood : ∀ {x y : V}, G.Adj x y →
        0 < ⟪P (b x), P (b y)⟫_ℝ := by
      intro x y hxy
      by_contra hnot
      apply hbad
      exact ⟨x, y, hxy, le_of_not_gt hnot⟩
    let o : V := Classical.choice hconn.nonempty
    letI : Fintype (G.neighborSet o) := finiteNeighbor G o
    let N : Finset V := @SimpleGraph.neighborFinset V G o inferInstance
    have hNcard : N.card = d := by
      exact regular_neighborFinset_card hreg o
    have hdpos : 0 < (d : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hd)
    have hNpos : 0 < N.card := by
      rw [hNcard]
      exact Nat.zero_lt_of_lt hd
    have hNnonempty : N.Nonempty := Finset.card_pos.mp hNpos
    have hsumN : Finset.sum N
        (fun y => ⟪P (b o), P (b y)⟫_ℝ) = lam * α := by
      dsimp [N]
      exact projector_gram_sum_neighbor P hnorm hproj heigen o
    have hsum_le : Finset.sum N
        (fun y => ⟪P (b o), P (b y)⟫_ℝ) ≤
        Finset.sum N (fun _ => lam * α / (d : ℝ)) := by
      rw [hsumN]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hNcard]
      field_simp [ne_of_gt hdpos]
      exact le_rfl
    obtain ⟨w, hwN, hwle⟩ :=
      Finset.exists_le_of_sum_le hNnonempty hsum_le
    have how : G.Adj o w := by
      simpa [N] using hwN
    let a : ℝ :=
      ⟪P (b o), P (b w)⟫_ℝ / α
    have ha_pos : 0 < a := by
      dsimp [a]
      exact div_pos (hgood how) hα
    have ha_le : a ≤ lam / (d : ℝ) := by
      dsimp [a]
      apply (div_le_iff₀ hα).2
      exact hwle.trans_eq (by ring)
    have hla_d : lam / (d : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]
      exact hlam.2.1
    have ha_lt_one : a < 1 := lt_of_le_of_lt ha_le hla_d
    have hdenpos : 0 < 1 - a ^ 2 := by nlinarith
    have hden_ge : γ / (d : ℝ) ≤ 1 - a ^ 2 := by
      have hbound : a ^ 2 ≤ (lam / (d : ℝ)) ^ 2 := by
        exact sq_le_sq₀ (le_of_lt ha_pos) (by positivity) |>.mpr ha_le
      dsimp [γ]
      have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
      field_simp [hdne] at hbound ⊢
      have hlamle : lam ≤ (d : ℝ) := le_of_lt hlam.2.1
      have hlamnonneg : 0 ≤ lam := le_of_lt hlam_pos
      nlinarith [hbound]
    let C (x : V) : EuclideanSpace ℝ V := α⁻¹ • P (b x)
    let φ : EuclideanSpace ℝ V :=
      (1 - a ^ 2)⁻¹ • (C o - a • C w)
    have hCeigen (x : V) :
        Matrix.toEuclideanLin (adjacencyMatrix G) (C x) = lam • C x := by
      dsimp [C]
      simpa [smul_smul, b, EuclideanSpace.basisFun_apply, mul_comm] using
        congrArg (fun z => α⁻¹ • z) (heigen x)
    have hφeigen : Matrix.toEuclideanLin (adjacencyMatrix G) φ = lam • φ := by
      dsimp [φ]
      simp only [map_smul, map_sub]
      rw [hCeigen o, hCeigen w]
      module
    have hCcoord (x y : V) : (C x).ofLp y =
        ⟪P (b x), P (b y)⟫_ℝ / α := by
      dsimp [C]
      change α⁻¹ * (P (b x)).ofLp y = _
      rw [hcoord]
      ring
    have hCoo : (C o).ofLp o = 1 := by
      rw [hCcoord, hdiag]
      field_simp [hαne]
    have hCow : (C o).ofLp w = a := by
      rw [hCcoord]
    have hCww : (C w).ofLp w = 1 := by
      rw [hCcoord, hdiag]
      field_simp [hαne]
    have hCwo : (C w).ofLp o = a := by
      rw [hCcoord, hKsym]
    have hφo : φ.ofLp o = 1 := by
      dsimp [φ]
      change (1 - a ^ 2)⁻¹ * ((C o).ofLp o - a * (C w).ofLp o) = 1
      rw [hCoo, hCwo]
      field_simp
    have hφw : φ.ofLp w = 0 := by
      dsimp [φ]
      change (1 - a ^ 2)⁻¹ * ((C o).ofLp w - a * (C w).ofLp w) = 0
      rw [hCow, hCww]
      ring
    have hCnorm (x : V) : ‖C x‖ ^ 2 = r := by
      dsimp [C]
      rw [norm_smul_sq_real, hnorm x]
      calc
        (α⁻¹) ^ 2 * α = α⁻¹ := by field_simp [hαne]
        _ = r := hinv
    have hCinner :
        ⟪C o, C w⟫_ℝ = a * r := by
      dsimp [C]
      rw [real_inner_smul_left, real_inner_smul_right]
      dsimp [a]
      calc
        α⁻¹ * (α⁻¹ * ⟪P (b o), P (b w)⟫_ℝ) =
            (⟪P (b o), P (b w)⟫_ℝ / α) * r := by
              rw [div_eq_mul_inv, hinv]
              ring
         _ = a * r := by simp [a]
    have hφnorm : ‖φ‖ ^ 2 = r / (1 - a ^ 2) := by
      dsimp [φ]
      rw [norm_smul_sq_real]
      have haCnorm : ‖a • C w‖ ^ 2 = a ^ 2 * r := by
        rw [norm_smul_sq_real, hCnorm w]
      rw [norm_sub_sq_real, real_inner_smul_right,
        hCnorm o, haCnorm, hCinner]
      field_simp [hdenpos.ne']
      ring
    have hφenergy : dirichletEnergy G d φ =
        γ * (r / (1 - a ^ 2)) := by
      rw [dirichletEnergy_of_eigenvector hφeigen, hφnorm]
    refine ⟨o, w, φ, how, hφeigen, hφo, le_of_eq hφw, ?_, ?_⟩
    · rw [hφnorm]
      change r / (1 - a ^ 2) ≤ (d : ℝ) * r / γ
      have hmul : γ * r ≤ (d : ℝ) * r * (1 - a ^ 2) := by
        have hmul' := mul_le_mul_of_nonneg_right hden_ge hrnonneg
        calc
          γ * r = (d : ℝ) * (γ / (d : ℝ) * r) := by
            field_simp [ne_of_gt hdpos]
          _ ≤ (d : ℝ) * ((1 - a ^ 2) * r) := by
            gcongr
          _ = (d : ℝ) * r * (1 - a ^ 2) := by ring
      apply (div_le_iff₀ hdenpos).2
      calc
        r ≤ ((d : ℝ) * r * (1 - a ^ 2)) / γ :=
          (le_div_iff₀ hγpos).2 (by simpa [mul_comm] using hmul)
        _ = (d : ℝ) * r / γ * (1 - a ^ 2) := by ring
    · rw [hφenergy]
      change γ * (r / (1 - a ^ 2)) ≤ (d : ℝ) * r
      have hmul : γ * r ≤ (d : ℝ) * r * (1 - a ^ 2) := by
        have hmul' := mul_le_mul_of_nonneg_right hden_ge hrnonneg
        calc
          γ * r = (d : ℝ) * (γ / (d : ℝ) * r) := by
            field_simp [ne_of_gt hdpos]
          _ ≤ (d : ℝ) * ((1 - a ^ 2) * r) := by
            gcongr
          _ = (d : ℝ) * r * (1 - a ^ 2) := by ring
      calc
        γ * (r / (1 - a ^ 2)) = (γ * r) / (1 - a ^ 2) := by ring
        _ ≤ (d : ℝ) * r := (div_le_iff₀ hdenpos).2 (by simpa [mul_comm] using hmul)

end TheoremOnePointOne
