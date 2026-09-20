import MainTheoremSpectral
import MainTheoremArithmetic
import CheckGap
import CheckProp24

set_option autoImplicit false

namespace MainTheorem

open scoped BigOperators InnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! The fully formalized `λ₂ ≤ 0` branch of the main theorem. -/
lemma nonpositive_second_eigenvalue_branch
    (G : SimpleGraph V) (d : ℕ) (lam : ℝ)
    (hd : 2 ≤ d)
    (hG : IsMainGraph G d)
    (hlam : IsSecondAdjacencyEigenvalue G (d : ℝ) lam)
    (hlam_nonpos : lam ≤ 0) :
    MainTheoremClaim G d lam := by
  classical
  rcases hG with ⟨hconn, hreg, hvt⟩
  letI : Nonempty V := hconn.nonempty
  let A := adjacencyMatrix G
  let T := Matrix.toEuclideanLin A
  let hT : T.IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff).2 (adjacencyMatrix_isHermitian G)
  let hn : Module.finrank ℝ (EuclideanSpace ℝ V) = Fintype.card V := by simp
  let θ : Fin (Fintype.card V) → ℝ := hT.eigenvalues hn
  have hθadj : ∀ i, IsAdjacencyEigenvalue G (θ i) := by
    intro i
    apply adjacency_eigenvalue_of_euclidean_eigenvector G
      (hT.eigenvectorBasis hn i)
      (hT.apply_eigenvectorBasis hn i)
    exact (hT.eigenvectorBasis hn).orthonormal.ne_zero i
  have hθtop : ∀ i, θ i ≤ d := by
    intro i
    exact hlam.2.2.1 _ (hθadj i)
  have hθbottom : ∀ i, - (d : ℝ) ≤ θ i := by
    intro i
    exact (adjacency_eigenvalue_bounds hreg (hθadj i)).1
  have hdpos : 0 < d := by omega
  have hconst : IsAdjacencyEigenvalue G (d : ℝ) :=
    regular_constant_is_adjacencyEigenvalue hreg
  have hconstT : Module.End.HasEigenvalue T (d : ℝ) := by
    simpa [T, A] using euclidean_hasEigenvalue_of_adjacency G hconst
  obtain ⟨i₀, hi₀⟩ := hT.exists_eigenvalues_eq hn hconstT
  have hθi₀ : θ i₀ = d := hi₀
  have hcardtop :
      (Finset.univ.filter (fun i : Fin (Fintype.card V) => θ i = d)).card = 1 := by
    calc
      (Finset.univ.filter (fun i : Fin (Fintype.card V) => θ i = d)).card =
          Module.finrank ℝ (Module.End.eigenspace T (d : ℝ)) := by
        simpa [θ] using hT.card_filter_eigenvalues_eq hn (d : ℝ)
      _ = 1 := by
        simpa [T, A] using connected_degree_eigenspace_finrank_one_euclidean hreg hconn
  have hθnonpos : ∀ i, i ≠ i₀ → θ i ≤ 0 := by
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
    exact (hlam.2.2.2 _ (hθadj i) hlt).trans hlam_nonpos
  have htraceT : LinearMap.trace ℝ (EuclideanSpace ℝ V) T = 0 := by
    rw [show T = Matrix.toEuclideanLin (adjacencyMatrix G) by rfl]
    rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun V ℝ).toBasis]
    rw [show Matrix.toEuclideanLin (adjacencyMatrix G) =
        Matrix.toLin (EuclideanSpace.basisFun V ℝ).toBasis
          (EuclideanSpace.basisFun V ℝ).toBasis (adjacencyMatrix G) by
      simpa only using congrArg (fun f => f (adjacencyMatrix G))
        (Matrix.toEuclideanLin_eq_toLin_orthonormal (𝕜 := ℝ) (m := V) (n := V))]
    simpa using adjacencyMatrix_trace G
  have htrace : ∑ i, θ i = 0 := by
    have h := hT.trace_eq_sum_eigenvalues hn
    dsimp [θ] at h ⊢
    rw [htraceT] at h
    simpa using h.symm
  have htrace_sq : ∑ i, (θ i) ^ 2 = (Fintype.card V : ℝ) * d := by
    have h := euclidean_trace_square_eigenvalues G
    dsimp [θ, hT, hn, T, A]
    rw [h]
    exact adjacencyMatrix_sq_trace_of_regular hreg
  have hcard : Fintype.card V ≤ 2 * d :=
    nonpositive_spectrum_card_bound hdpos θ i₀ hθbottom hθnonpos hθi₀
      htrace htrace_sq
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos
  have hcard_real : (Fintype.card V : ℝ) ≤ 2 * d := by exact_mod_cast hcard
  have hmn : (adjacencyEigenvalueMultiplicity G lam : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast adjacencyEigenvalueMultiplicity_le_card G lam
  have hL : 0 ≤ Real.log (Fintype.card V : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcard_pos))
  have hU : 0 ≤ Real.log (2 * (d : ℝ)) := by
    apply Real.log_nonneg
    have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hlog : 1 + Real.log (Fintype.card V : ℝ) ≤
      1 + Real.log (2 * (d : ℝ)) := by
    gcongr
  have hden : 0 < (1 + Real.log (Fintype.card V : ℝ)) ^ 2 := by
    positivity
  have hL' : 0 ≤ 1 + Real.log (Fintype.card V : ℝ) := by linarith
  have hU' : 0 ≤ 1 + Real.log (2 * (d : ℝ)) := by linarith
  exact nonpositive_second_eigenvalue_arithmetic
    (by positivity) (by positivity) hmn hL' hU' hlog
    (log_constant_sq_le_C d) hden

/-! The remaining positive-eigenvalue branch is the analytic core of the paper. -/
theorem main_theorem
    (G : SimpleGraph V) (d : ℕ) (lam : ℝ)
    (hd : 2 ≤ d)
    (hG : IsMainGraph G d)
    (hlam : IsSecondAdjacencyEigenvalue G (d : ℝ) lam) :
    MainTheoremClaim G d lam := by
  by_cases hlam_nonpos : lam ≤ 0
  · exact nonpositive_second_eigenvalue_branch G d lam hd hG hlam hlam_nonpos
  · have hlam_pos : 0 < lam := lt_of_not_ge hlam_nonpos
    rcases hG with ⟨hconn, hreg, hvt⟩
    letI : G.LocallyFinite := finiteNeighbor G
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    have hn : (3 : ℝ) ≤ Fintype.card V := by
      obtain ⟨v⟩ := hconn.nonempty
      have hdeg : G.degree v = d := hreg v
      have hlt : G.degree v < Fintype.card V := G.degree_lt_card_verts v
      rw [hdeg] at hlt
      have hnat : 3 ≤ Fintype.card V := by omega
      exact_mod_cast hnat
    let n : ℝ := Fintype.card V
    let m : ℝ := adjacencyEigenvalueMultiplicity G lam
    let r : ℝ := n / m
    let γ : ℝ := (d : ℝ) - lam
    have hmpos : 0 < m := by
      dsimp [m]
      exact_mod_cast multiplicity_pos_of_eigenvalue' G lam hlam.1
    have hmn : m ≤ n := by
      dsimp [m, n]
      exact_mod_cast adjacencyEigenvalueMultiplicity_le_card G lam
    have hr : 1 ≤ r := by
      dsimp [r]
      apply (le_div_iff₀ hmpos).2
      simpa using hmn
    have hratio : r * m = n := by
      dsimp [r]
      field_simp
    obtain hsmall | hgap :=
      lemma_3_1 G d lam hd hconn hreg hvt hlam hlam_pos
    · have hn1 : (1 : ℝ) ≤ n := by linarith
      have hsmall' : m ≤ 4 := by
        dsimp [m]
        exact_mod_cast hsmall
      exact small_multiplicity_branch_arithmetic hd hn1 hsmall'
    · by_cases hmle : m ≤ 4
      · have hn1 : (1 : ℝ) ≤ n := by linarith
        exact small_multiplicity_branch_arithmetic hd hn1 hmle
      · have hm4 : 4 < m := lt_of_not_ge hmle
        have htrade :
            Real.log n ≤ Real.log (4 * ((d : ℝ) + 1)) +
              2 * Real.log ((d : ℝ) * r / γ) +
              8 * (d : ℝ) * Real.sqrt r := by
          dsimp [n, m, r, γ]
          exact proposition_2_4 G d lam hd hconn hreg hvt hlam hlam_pos
        have hgap' : 1 / (32 * r ^ 2) < γ := by
          simpa [n, m, r, γ] using hgap
        have hn' : (3 : ℝ) ≤ n := by simpa [n] using hn
        exact positive_gap_arithmetic hd hn' hm4 hr hratio hgap'
          (by simpa [n] using htrade)

end MainTheorem
