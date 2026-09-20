import MainTheoremArithmetic

set_option autoImplicit false

namespace MainTheorem

lemma check_positive_gap_arithmetic
    {n m r γ : ℝ} {d : ℕ}
    (hd : 2 ≤ d) (hn : 3 ≤ n) (hm : 4 < m) (hr : 1 ≤ r)
    (hratio : r * m = n)
    (hgap : 1 / (32 * r ^ 2) < γ)
    (htrade : Real.log n ≤ Real.log (4 * ((d + 1 : ℕ) : ℝ)) +
      2 * Real.log (d * r / γ) + 8 * d * Real.sqrt r) :
    m ≤ C d * n / (1 + Real.log n) ^ 2 := by
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  have hγ0 : 0 < γ := by
    have : 0 < 1 / (32 * r ^ 2) := by positivity
    linarith
  have hsmall : 1 ≤ 32 * r ^ 2 * γ := by
    have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < 32 * r ^ 2)).mp hgap
    nlinarith
  have hratio_pos : 0 < d * r / γ := by positivity
  have hratio_le : d * r / γ ≤ 32 * d * r ^ 3 := by
    apply (div_le_iff₀ hγ0).2
    have hmul := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (le_of_lt hd0) (le_of_lt hr0))
    nlinarith
  have hlog_ratio : Real.log (d * r / γ) ≤ Real.log (32 * d * r ^ 3) := by
    exact Real.log_le_log hratio_pos hratio_le
  have hlog_expand : Real.log (32 * d * r ^ 3) =
      Real.log (32 * d) + 3 * Real.log r := by
    rw [show 32 * d * r ^ 3 = (32 * d) * r ^ 3 by ring]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    ring
  have hlogr : Real.log r ≤ Real.sqrt r := log_le_sqrt hr
  have hLbound : Real.log n ≤ K d * Real.sqrt r := by
    calc
      Real.log n ≤ Real.log (4 * ((d + 1 : ℕ) : ℝ)) +
          2 * Real.log (d * r / γ) + 8 * d * Real.sqrt r := htrade
      _ ≤ Real.log (4 * ((d + 1 : ℕ) : ℝ)) +
          2 * Real.log (32 * d * r ^ 3) + 8 * d * Real.sqrt r := by
        gcongr
      _ = Real.log (4 * ((d + 1 : ℕ) : ℝ)) + 2 * Real.log (32 * d) +
          6 * Real.log r + 8 * d * Real.sqrt r := by rw [hlog_expand]; ring
      _ ≤ K d * Real.sqrt r := by
        have hsqrt1 : 1 ≤ Real.sqrt r := by
          exact (Real.one_le_sqrt).2 hr
        have hc : 0 ≤ Real.log (4 * ((d + 1 : ℕ) : ℝ)) +
            2 * Real.log (32 * d) := by
          have h₁ : 0 ≤ Real.log (4 * ((d + 1 : ℕ) : ℝ)) := by
            apply Real.log_nonneg
            have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
            norm_num
            nlinarith
          have h₂ : 0 ≤ Real.log (32 * (d : ℝ)) := by
            apply Real.log_nonneg
            have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
            nlinarith
          positivity
        have hc_le : Real.log (4 * ((d + 1 : ℕ) : ℝ)) +
              2 * Real.log (32 * d) ≤
            (Real.log (4 * ((d + 1 : ℕ) : ℝ)) +
              2 * Real.log (32 * d)) * Real.sqrt r := by
          nlinarith [mul_nonneg hc (sub_nonneg.mpr hsqrt1)]
        have hlog_le : 6 * Real.log r ≤ 6 * Real.sqrt r := by gcongr
        calc
          Real.log (4 * ((d + 1 : ℕ) : ℝ)) + 2 * Real.log (32 * d) +
              6 * Real.log r + 8 * d * Real.sqrt r ≤
              (Real.log (4 * ((d + 1 : ℕ) : ℝ)) + 2 * Real.log (32 * d)) *
                Real.sqrt r + 6 * Real.sqrt r + 8 * d * Real.sqrt r := by
            gcongr
          _ = K d * Real.sqrt r := by dsimp [K]; ring
  have hL : 0 < Real.log n := Real.log_pos (by linarith)
  have hK : 0 ≤ K d := by linarith [K_ge_two hd]
  have hC : 4 * (K d) ^ 2 ≤ C d := four_K_sq_le_C d
  have hlog_one : 1 ≤ Real.log n := by
    have hlog3 : 1 < Real.log (3 : ℝ) := by
      have h := Real.log_three_gt_d9
      norm_num at h ⊢
      linarith
    have hmon : Real.log (3 : ℝ) ≤ Real.log n :=
      Real.log_le_log (by norm_num) hn
    linarith
  exact large_multiplicity_arithmetic
    (le_of_lt hm0) (lt_of_lt_of_le zero_lt_one hr) hL hK hratio hLbound hC
    (by linarith)

end MainTheorem
