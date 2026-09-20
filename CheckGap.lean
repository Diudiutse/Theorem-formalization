import CheckBall
import Theorem11Arithmetic
import Theorem11Arithmetic

set_option autoImplicit false

namespace TheoremOnePointOne

open scoped InnerProductSpace BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma coherence_gap_multiplicity_alternative
    (G : SimpleGraph V) (d : ℕ) (lam : ℝ)
    (_hd : 2 ≤ d) (hconn : G.Connected) (hreg : IsRegularFinite G d)
    (hvt : IsVertexTransitive G)
    (hlam : IsSecondAdjacencyEigenvalue G (d : ℝ) lam)
    (_hlam_pos : 0 < lam) :
    adjacencyEigenvalueMultiplicity G lam ≤ 4 ∨
      1 / (32 * ((Fintype.card V : ℝ) /
        (adjacencyEigenvalueMultiplicity G lam : ℝ)) ^ 2) <
        (d : ℝ) - lam := by
  classical
  letI : Nonempty V := hconn.nonempty
  let n : ℝ := Fintype.card V
  let m : ℝ := adjacencyEigenvalueMultiplicity G lam
  let r : ℝ := n / m
  let γ : ℝ := (d : ℝ) - lam
  have hmpos_nat : 0 < adjacencyEigenvalueMultiplicity G lam :=
    multiplicity_pos_of_eigenvalue' G lam hlam.1
  have hmpos : 0 < m := by
    dsimp [m]
    exact_mod_cast hmpos_nat
  have hnpos : 0 < n := by
    dsimp [n]
    positivity
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hγ : 0 < γ := by
    dsimp [γ]
    linarith [hlam.2.1]
  obtain ⟨α, Φ, hα, hαr, hnorm, hframe, hedge⟩ :=
    projector_coherence_data G d lam hconn hreg hvt hlam.1
  have hαr' : α * r = 1 := by simpa [r, n, m] using hαr
  let q : ℝ := Real.sqrt ((2 * γ)⁻¹)
  let R : ℕ := ⌊q⌋₊
  have hq : 0 ≤ q := by dsimp [q]; exact Real.sqrt_nonneg _
  have hq_sq : q ^ 2 = (2 * γ)⁻¹ := by
    dsimp [q]
    exact Real.sq_sqrt (by positivity)
  have hγq : γ * q ^ 2 = 1 / 2 := by
    rw [hq_sq]
    field_simp
  have hRq : (R : ℝ) ≤ q := by
    dsimp [R]
    exact Nat.floor_le hq
  have hRnonneg : 0 ≤ (R : ℝ) := by positivity
  have hRsq : (R : ℝ) ^ 2 ≤ q ^ 2 := by
    exact (sq_le_sq₀ hRnonneg hq).mpr hRq
  have hRcoh : γ * (R : ℝ) ^ 2 ≤ 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hRsq (le_of_lt hγ)]
  have hball (o : V) :
      (Set.ncard {x : V | G.dist x o ≤ R} : ℝ) ≤ 4 * r := by
    exact coherence_ball_bound' hconn Φ α γ r R o hα
      (le_of_lt hγ) (le_of_lt hrpos) hαr' hnorm hframe hedge hRcoh
  have hediam : G.ediam ≠ ⊤ :=
    (G.connected_iff_ediam_ne_top).mp hconn
  by_cases hRD : G.diam ≤ R
  · have hball_univ (o : V) :
        {x : V | G.dist x o ≤ R} = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact (G.dist_le_diam hediam).trans hRD
    have hcard_bound : n ≤ 4 * r := by
      obtain ⟨o⟩ := (inferInstance : Nonempty V)
      have hb := hball o
      rw [hball_univ o, Set.ncard_univ] at hb
      simpa [n] using hb
    left
    have hnr : n ≤ (4 * n) / m := by
      dsimp [r] at hcard_bound
      convert hcard_bound using 1
      all_goals ring
    have hmul : n * m ≤ 4 * n := (le_div_iff₀ hmpos).mp hnr
    have hmul' : m * n ≤ 4 * n := by nlinarith [hmul]
    have hm4 : m ≤ 4 := by nlinarith [hmul', hnpos]
    have hm4' : (adjacencyEigenvalueMultiplicity G lam : ℝ) ≤ 4 := by
      simpa [m] using hm4
    exact_mod_cast hm4'
  · right
    have hRdiam : R < G.diam := Nat.lt_of_not_ge hRD
    obtain ⟨o, v, hdv⟩ := G.exists_dist_eq_diam
    obtain ⟨p, hp, hplen⟩ := hconn.exists_path_of_dist o v
    have hRle : R ≤ p.length := by
      rw [hplen, hdv]
      exact hRdiam.le
    have hlow := ball_card_ge_of_path p hp R hRle
    have hRupper : (R + 1 : ℝ) ≤ 4 * r := (hlow.trans (hball o))
    have hqupper : q < 4 * r := by
      exact (by
        have := Nat.lt_floor_add_one q
        exact this.trans_le hRupper)
    have hq_sq_lt : q ^ 2 < (4 * r) ^ 2 := by
      nlinarith [hq, hrpos, hqupper]
    have h_inv_lt : (2 * γ)⁻¹ < (4 * r) ^ 2 := by
      rw [← hq_sq]
      exact hq_sq_lt
    have hineq : 1 < 32 * γ * r ^ 2 := by
      have hγne : γ ≠ 0 := ne_of_gt hγ
      field_simp [hγne] at h_inv_lt
      nlinarith [h_inv_lt]
    apply (div_lt_iff₀ (by positivity : 0 < 32 * r ^ 2)).2
    nlinarith [hineq]

/-! This is the PDF's Lemma 3.1, with the projector/coherence calculation
    discharged by `coherence_gap_multiplicity_alternative`. -/
lemma lemma_3_1
    (G : SimpleGraph V) (d : ℕ) (lam : ℝ)
    (hd : 2 ≤ d) (hconn : G.Connected) (hreg : IsRegularFinite G d)
    (hvt : IsVertexTransitive G)
    (hlam : IsSecondAdjacencyEigenvalue G (d : ℝ) lam)
    (hlam_pos : 0 < lam) :
    adjacencyEigenvalueMultiplicity G lam ≤ 4 ∨
      1 / (32 * ((Fintype.card V : ℝ) /
        (adjacencyEigenvalueMultiplicity G lam : ℝ)) ^ 2) <
        (d : ℝ) - lam := by
  exact coherence_gap_multiplicity_alternative G d lam hd hconn hreg hvt hlam hlam_pos

end TheoremOnePointOne
