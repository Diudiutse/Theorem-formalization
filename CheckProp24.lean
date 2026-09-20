import CheckLemma21
import CheckLemma22
import CheckLemma23

set_option autoImplicit false

namespace MainTheorem

open scoped BigOperators InnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! The logarithmic tradeoff in Proposition 2.4. -/
lemma proposition_2_4
    (G : SimpleGraph V) (d : ℕ) (lam : ℝ)
    (hd : 2 ≤ d)
    (hconn : G.Connected)
    (hreg : IsRegularFinite G d)
    (hvt : IsVertexTransitive G)
    (hlam : IsSecondAdjacencyEigenvalue G (d : ℝ) lam)
    (hlam_pos : 0 < lam) :
    Real.log (Fintype.card V : ℝ) ≤
      Real.log (4 * ((d : ℝ) + 1)) +
        2 * Real.log ((d : ℝ) *
          ((Fintype.card V : ℝ) /
            (adjacencyEigenvalueMultiplicity G lam : ℝ)) /
          ((d : ℝ) - lam)) +
        8 * (d : ℝ) * Real.sqrt
          ((Fintype.card V : ℝ) /
            (adjacencyEigenvalueMultiplicity G lam : ℝ)) := by
  classical
  letI : Nonempty V := hconn.nonempty
  let n : ℝ := Fintype.card V
  let m : ℝ := adjacencyEigenvalueMultiplicity G lam
  let r : ℝ := n / m
  let γ : ℝ := (d : ℝ) - lam
  have hnpos : 0 < n := by
    dsimp [n]
    positivity
  have hmpos : 0 < m := by
    dsimp [m]
    exact_mod_cast multiplicity_pos_of_eigenvalue' G lam hlam.1
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos hnpos hmpos
  have hrone : 1 ≤ r := by
    dsimp [r]
    apply (le_div_iff₀ hmpos).2
    have hmn : m ≤ n := by
      dsimp [m, n]
      exact_mod_cast adjacencyEigenvalueMultiplicity_le_card G lam
    simpa using hmn
  have hγpos : 0 < γ := by
    dsimp [γ]
    exact sub_pos.mpr hlam.2.1
  obtain ⟨o, w, φ, how, hφeig, hφo, hφw, hφnorm, hφenergy⟩ :=
    lemma_2_2 G d lam hd hconn hreg hvt hlam hlam_pos
  let T : ℝ := 2 * (d : ℝ) * Real.sqrt r
  have hTpos : 0 < T := by
    dsimp [T]
    positivity
  have hT_sq : T ^ 2 = 4 * (d : ℝ) ^ 2 * r := by
    dsimp [T]
    calc
      (2 * (d : ℝ) * Real.sqrt r) ^ 2 =
          4 * (d : ℝ) ^ 2 * (Real.sqrt r) ^ 2 := by ring
      _ = 4 * (d : ℝ) ^ 2 * r := by
        rw [Real.sq_sqrt (le_of_lt hrpos)]
  have henergy_bound : lam * dirichletEnergy G d φ < T ^ 2 := by
    have hde : dirichletEnergy G d φ ≤ (d : ℝ) * r := by
      simpa [r] using hφenergy
    have hE_nonneg : 0 ≤ dirichletEnergy G d φ := by
      rw [dirichletEnergy_of_eigenvector hφeig]
      positivity
    have hlamd : lam ≤ (d : ℝ) := le_of_lt hlam.2.1
    have hfirst : lam * dirichletEnergy G d φ ≤
        (d : ℝ) * dirichletEnergy G d φ := by
      exact mul_le_mul_of_nonneg_right hlamd hE_nonneg
    have hsecond : (d : ℝ) * dirichletEnergy G d φ ≤
        (d : ℝ) * ((d : ℝ) * r) := by
      gcongr
    rw [hT_sq]
    nlinarith [hfirst, hsecond]
  obtain ⟨F, hFne, hFsuper, hFcard⟩ :=
    lemma_2_3 G d lam T hconn hreg hvt hlam_pos o w φ how hφeig hφo hφw
      hTpos henergy_bound
  have hcard_bound : n ≤ ((d : ℝ) + 1) * (F.card : ℝ) ^ 2 := by
    have hvt' : IsVertexTransitive' G := vertexTransitive'_of_original hvt
    have h := lemma_2_1 hreg hconn hvt' hlam F hFsuper
    have h' : (Fintype.card V : ℝ) ≤
        (((d + 1) * (F.card * F.card) : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [n, Nat.cast_mul, pow_two, Nat.cast_add] using h'
  have hFcard' : (F.card : ℝ) ≤
      1 + Real.exp (2 * T) * ‖φ‖ ^ 2 := by
    exact hFcard
  have hφnorm' : ‖φ‖ ^ 2 ≤ (d : ℝ) * r / γ := by
    simpa [r, γ] using hφnorm
  have hBpos : 0 < (d : ℝ) * r / γ := by
    positivity
  have hBone : 1 ≤ (d : ℝ) * r / γ := by
    have hγle : γ ≤ (d : ℝ) := by
      dsimp [γ]
      linarith
    apply (le_div_iff₀ hγpos).2
    nlinarith [hrone]
  have hXone : 1 ≤ Real.exp (2 * T) * ‖φ‖ ^ 2 := by
    have hexp : 1 ≤ Real.exp (2 * T) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hnormone : 1 ≤ ‖φ‖ ^ 2 := by
      rw [norm_sq_eq_sum_coord]
      have hs := Finset.single_le_sum (s := (Finset.univ : Finset V))
        (f := fun x : V => (φ.ofLp x) ^ 2)
        (fun x hx => sq_nonneg _) (a := o) (by simp)
      simpa [hφo] using hs
    nlinarith [mul_le_mul hexp hnormone (by positivity) (by positivity)]
  have hFcard'' : (F.card : ℝ) ≤
      2 * Real.exp (2 * T) * ((d : ℝ) * r / γ) := by
    have hsum : 1 + Real.exp (2 * T) * ‖φ‖ ^ 2 ≤
        2 * Real.exp (2 * T) * ((d : ℝ) * r / γ) := by
      have hleft : 1 + Real.exp (2 * T) * ‖φ‖ ^ 2 ≤
          2 * (Real.exp (2 * T) * ‖φ‖ ^ 2) := by
        nlinarith [hXone]
      have hright : Real.exp (2 * T) * ‖φ‖ ^ 2 ≤
          Real.exp (2 * T) * ((d : ℝ) * r / γ) := by
        gcongr
      nlinarith
    exact hFcard'.trans hsum
  have hNupper : n ≤ (d + 1 : ℝ) *
      (2 * Real.exp (2 * T) * ((d : ℝ) * r / γ)) ^ 2 := by
    calc
      n ≤ (d + 1 : ℝ) * (F.card : ℝ) ^ 2 := hcard_bound
      _ ≤ (d + 1 : ℝ) *
          (2 * Real.exp (2 * T) * ((d : ℝ) * r / γ)) ^ 2 := by
        gcongr
  have hlogN : Real.log n ≤ Real.log ((d + 1 : ℝ) *
      (2 * Real.exp (2 * T) * ((d : ℝ) * r / γ)) ^ 2) := by
    exact Real.log_le_log (by positivity) hNupper
  have hlog_expand : Real.log ((d + 1 : ℝ) *
      (2 * Real.exp (2 * T) * ((d : ℝ) * r / γ)) ^ 2) =
      Real.log (4 * ((d : ℝ) + 1)) +
        4 * T + 2 * Real.log ((d : ℝ) * r / γ) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_exp]
    rw [Real.log_mul (by positivity) (by positivity)]
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog4]
    ring
  rw [hlog_expand] at hlogN
  dsimp [T] at hlogN
  change Real.log n ≤ Real.log (4 * ((d : ℝ) + 1)) +
      2 * Real.log ((d : ℝ) * r / γ) + 8 * (d : ℝ) * Real.sqrt r
  convert hlogN using 1
  all_goals ring

end MainTheorem
