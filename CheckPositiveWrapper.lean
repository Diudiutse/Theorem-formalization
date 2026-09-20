import MainTheoremSpectral
import MainTheoremArithmetic

set_option autoImplicit false

namespace MainTheorem

open scoped BigOperators InnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma multiplicity_pos_of_eigenvalue
    (G : SimpleGraph V) (lam : ℝ)
    (hlam : IsAdjacencyEigenvalue G lam) :
    0 < adjacencyEigenvalueMultiplicity G lam := by
  let K := LinearMap.ker (adjacencyOperator G - lam • LinearMap.id)
  have hne : K ≠ ⊥ := by
    intro hbot
    obtain ⟨f, hf, hfeq⟩ := hlam
    have hfmem : f ∈ K := by
      rw [LinearMap.mem_ker]
      simp [K, sub_eq_zero, hfeq]
    have hfzero : f = 0 := by
      have : (f : V → ℝ) ∈ (⊥ : Submodule ℝ (V → ℝ)) := by
        simpa [hbot] using hfmem
      simpa using this
    exact hf hfzero
  exact (Module.finrank_pos_iff.mpr (by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact hne Submodule.eq_bot_of_subsingleton))

lemma positive_second_eigenvalue_branch_of_inputs
    (G : SimpleGraph V) (d : ℕ) (lam : ℝ)
    (hd : 2 ≤ d)
    (hG : IsMainGraph G d)
    (hlam : IsSecondAdjacencyEigenvalue G (d : ℝ) lam)
    (hn : (3 : ℝ) ≤ Fintype.card V)
    (htrade :
      let n : ℝ := Fintype.card V
      let m : ℝ := adjacencyEigenvalueMultiplicity G lam
      let r : ℝ := n / m
      let γ : ℝ := d - lam
      Real.log n ≤ Real.log (4 * (d + 1)) + 2 * Real.log (d * r / γ) +
        8 * d * Real.sqrt r)
    (hgap :
      let n : ℝ := Fintype.card V
      let m : ℝ := adjacencyEigenvalueMultiplicity G lam
      let r : ℝ := n / m
      let γ : ℝ := d - lam
      1 / (32 * r ^ 2) < γ)
    (hlam_pos : 0 < lam) :
    MainTheoremClaim G d lam := by
  let n : ℝ := Fintype.card V
  let m : ℝ := adjacencyEigenvalueMultiplicity G lam
  let r : ℝ := n / m
  have hmpos : 0 < m := by
    dsimp [m]
    exact_mod_cast multiplicity_pos_of_eigenvalue G lam hlam.1
  have hmn_nat := adjacencyEigenvalueMultiplicity_le_card G lam
  have hmn : m ≤ n := by
    dsimp [m, n]
    exact_mod_cast hmn_nat
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hr : 1 ≤ r := by
    dsimp [r]
    apply (le_div_iff₀ (show 0 < m by exact_mod_cast hmpos)).2
    simpa using hmn
  by_cases hm4 : m ≤ 4
  · exact small_multiplicity_branch_arithmetic hd hn1 hm4
  · have hm4' : 4 < m := lt_of_not_ge hm4
    apply positive_gap_arithmetic hd hn hm4' hr
    · dsimp [r]
      field_simp
      rfl
    · simpa [n, m, r] using hgap
    · simpa [n, m, r] using htrade

end MainTheorem
