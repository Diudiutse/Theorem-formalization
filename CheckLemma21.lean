import CheckUniform
import CheckRayleigh
import CheckCounting

set_option autoImplicit false

namespace MainTheorem

open scoped InnerProductSpace BigOperators Pointwise

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def constVector : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (Function.const V (1 : ℝ))

def supportedOn (F : Finset V) (f : EuclideanSpace ℝ V) : Prop :=
  ∀ x, x ∉ F → f.ofLp x = 0

def IsSupercritical
    (G : SimpleGraph V) (lam : ℝ) (F : Finset V) : Prop :=
  ∃ f : EuclideanSpace ℝ V, supportedOn F f ∧
    lam * ‖f‖ ^ 2 <
      ⟪Matrix.toEuclideanLin (adjacencyMatrix G) f, f⟫_ℝ

lemma permIso_support
    {G : SimpleGraph V} (e : GraphAut G) (F : Finset V)
    {f : EuclideanSpace ℝ V} (hf : supportedOn F f) :
    supportedOn (F.image e.toEquiv) (permIso e.toEquiv f) := by
  intro z hz
  change f.ofLp (e.toEquiv.symm z) = 0
  apply hf
  intro hF
  apply hz
  exact Finset.mem_image.mpr ⟨e.toEquiv.symm z, hF, by simp⟩

omit [DecidableEq V] in
lemma constVector_permIso {G : SimpleGraph V} (e : GraphAut G) :
    permIso e.toEquiv (constVector (V := V)) = constVector := by
  ext z
  change (permIso e.toEquiv (constVector (V := V))).ofLp z =
    (constVector (V := V)).ofLp z
  dsimp [permIso, constVector]
  simp

omit [DecidableEq V] in
lemma permIso_inner_constVector
    {G : SimpleGraph V} (e : GraphAut G) (f : EuclideanSpace ℝ V) :
    ⟪permIso e.toEquiv f, constVector⟫_ℝ = ⟪f, constVector⟫_ℝ := by
  rw [← constVector_permIso e]
  exact (permIso e.toEquiv).inner_map_map f constVector

lemma inner_eq_zero_of_disjoint_support
    {F H : Finset V} {f g : EuclideanSpace ℝ V}
    (hf : supportedOn F f) (hg : supportedOn H g)
    (hdisj : Disjoint F H) :
    ⟪f, g⟫_ℝ = 0 := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro z hz
  by_cases hzF : z ∈ F
  · have hzH : z ∉ H := by
      intro hzH
      exact Finset.disjoint_left.1 hdisj hzF hzH
    have hg0 := hg z hzH
    simp [hg0]
  · have hf0 := hf z hzF
    simp [hf0]

lemma adjacency_inner_expand
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (f g : EuclideanSpace ℝ V) :
    ⟪Matrix.toEuclideanLin (adjacencyMatrix G) f, g⟫_ℝ =
      ∑ x : V, ∑ y : V,
        (if G.Adj x y then f.ofLp y else 0) * g.ofLp x := by
  classical
  rw [PiLp.inner_apply]
  apply Fintype.sum_congr
  intro x
  rw [Matrix.toLpLin_apply]
  simp only [Matrix.mulVec, adjacencyMatrix, SimpleGraph.adjMatrix_apply]
  rw [dotProduct]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro y
  by_cases hxy : G.Adj x y <;> simp [hxy, mul_comm]

lemma adjacency_inner_zero_of_good
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {F : Finset V} {e : GraphAut G} {f : EuclideanSpace ℝ V}
    (hf : supportedOn F f)
    (hgood : ∀ x ∈ F, ∀ y ∈ F,
      e • x ≠ y ∧ ¬ G.Adj (e • x) y) :
    ⟪Matrix.toEuclideanLin (adjacencyMatrix G) f,
        permIso e.toEquiv f⟫_ℝ = 0 := by
  classical
  rw [adjacency_inner_expand]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hxy : G.Adj x y
  · by_cases hyF : y ∈ F
    · by_cases hxE : x ∈ F.image e.toEquiv
      · obtain ⟨x', hx'F, rfl⟩ := Finset.mem_image.mp hxE
        have hno := (hgood x' hx'F y hyF).2
        exfalso
        apply hno
        simpa [GraphAut.smul_def] using hxy
      · have hg0 := permIso_support e F hf x hxE
        simp [hg0]
    · have hf0 := hf y hyF
      simp [hf0]
  · simp [hxy]

lemma adjacency_inner_zero_of_good_reverse
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {F : Finset V} {e : GraphAut G} {f : EuclideanSpace ℝ V}
    (hf : supportedOn F f)
    (hgood : ∀ x ∈ F, ∀ y ∈ F,
      e • x ≠ y ∧ ¬ G.Adj (e • x) y) :
    ⟪Matrix.toEuclideanLin (adjacencyMatrix G) (permIso e.toEquiv f), f⟫_ℝ = 0 := by
  have hT : (Matrix.toEuclideanLin (adjacencyMatrix G)).IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff).2 (adjacencyMatrix_isHermitian G)
  calc
    ⟪Matrix.toEuclideanLin (adjacencyMatrix G) (permIso e.toEquiv f), f⟫_ℝ =
        ⟪permIso e.toEquiv f,
          Matrix.toEuclideanLin (adjacencyMatrix G) f⟫_ℝ := hT _ _
    _ = ⟪Matrix.toEuclideanLin (adjacencyMatrix G) f,
          permIso e.toEquiv f⟫_ℝ := real_inner_comm _ _
    _ = 0 := adjacency_inner_zero_of_good hf hgood

lemma lemma_2_1_of_rayleigh
    {G : SimpleGraph V} {d : ℕ} {lam : ℝ} [DecidableRel G.Adj]
    (hreg : IsRegularFinite G d)
    (hvt : IsVertexTransitive' G)
    (hRayleigh : ∀ x : EuclideanSpace ℝ V,
      ⟪x, constVector⟫_ℝ = 0 →
      ⟪Matrix.toEuclideanLin (adjacencyMatrix G) x, x⟫_ℝ ≤
        lam * ‖x‖ ^ 2)
    (F : Finset V)
    (hsuper : IsSupercritical G lam F) :
    Fintype.card V ≤ (d + 1) * (F.card * F.card) := by
  classical
  by_contra hcard
  have hsmall : (d + 1) * (F.card * F.card) < Fintype.card V :=
    lt_of_not_ge hcard
  obtain ⟨e, hgood⟩ := exists_good_graphAut hvt hreg F hsmall
  obtain ⟨f, hf, hcrit⟩ := hsuper
  have hdisj : Disjoint F (F.image e.toEquiv) := by
    rw [Finset.disjoint_left]
    intro z hzF hzE
    obtain ⟨y, hyF, hyz⟩ := Finset.mem_image.mp hzE
    have hne := (hgood y hyF z hzF).1
    exact hne (by simpa [GraphAut.smul_def] using hyz)
  have hinner : ⟪f, permIso e.toEquiv f⟫_ℝ = 0 :=
    inner_eq_zero_of_disjoint_support hf (permIso_support e F hf) hdisj
  have hcross :
      ⟪Matrix.toEuclideanLin (adjacencyMatrix G) f,
          permIso e.toEquiv f⟫_ℝ = 0 :=
    adjacency_inner_zero_of_good hf hgood
  have hcross' :
      ⟪Matrix.toEuclideanLin (adjacencyMatrix G) (permIso e.toEquiv f), f⟫_ℝ = 0 :=
    adjacency_inner_zero_of_good_reverse hf hgood
  have horth :
      ⟪f - permIso e.toEquiv f, constVector⟫_ℝ = 0 := by
    rw [inner_sub_left, permIso_inner_constVector]
    exact sub_self _
  have hnorm : ‖f - permIso e.toEquiv f‖ ^ 2 =
      ‖f‖ ^ 2 + ‖permIso e.toEquiv f‖ ^ 2 := by
    rw [norm_sub_sq_real, hinner]
    ring
  have hpermnorm : ‖permIso e.toEquiv f‖ = ‖f‖ :=
    (permIso e.toEquiv).norm_map f
  have hcomm :
      Matrix.toEuclideanLin (adjacencyMatrix G) (permIso e.toEquiv f) =
        permIso e.toEquiv (Matrix.toEuclideanLin (adjacencyMatrix G) f) := by
    exact (adjacency_perm_commute G e f).symm
  have hqperm :
      ⟪Matrix.toEuclideanLin (adjacencyMatrix G) (permIso e.toEquiv f),
          permIso e.toEquiv f⟫_ℝ =
        ⟪Matrix.toEuclideanLin (adjacencyMatrix G) f, f⟫_ℝ := by
    rw [hcomm]
    exact (permIso e.toEquiv).inner_map_map _ _
  have hqsub :
      ⟪Matrix.toEuclideanLin (adjacencyMatrix G)
          (f - permIso e.toEquiv f),
          f - permIso e.toEquiv f⟫_ℝ =
        ⟪Matrix.toEuclideanLin (adjacencyMatrix G) f, f⟫_ℝ +
          ⟪Matrix.toEuclideanLin (adjacencyMatrix G) (permIso e.toEquiv f),
            permIso e.toEquiv f⟫_ℝ := by
    rw [map_sub]
    simp only [inner_sub_left, inner_sub_right]
    rw [hcross, hcross']
    ring
  have hsuper_sub :
      lam * ‖f - permIso e.toEquiv f‖ ^ 2 <
        ⟪Matrix.toEuclideanLin (adjacencyMatrix G)
            (f - permIso e.toEquiv f),
            f - permIso e.toEquiv f⟫_ℝ := by
    rw [hnorm, hqsub, hqperm, hpermnorm]
    nlinarith
  exact (not_lt_of_ge (hRayleigh (f - permIso e.toEquiv f) horth)) hsuper_sub

lemma lemma_2_1
    {G : SimpleGraph V} {d : ℕ} {lam : ℝ} [DecidableRel G.Adj]
    (hreg : IsRegularFinite G d) (hconn : G.Connected)
    (hvt : IsVertexTransitive' G)
    (hlam : IsSecondAdjacencyEigenvalue G (d : ℝ) lam)
    (F : Finset V) (hsuper : IsSupercritical G lam F) :
    Fintype.card V ≤ (d + 1) * (F.card * F.card) := by
  apply lemma_2_1_of_rayleigh hreg hvt
    (rayleigh_le_on_second_eigenvalue hreg hconn hlam) F hsuper

end MainTheorem
