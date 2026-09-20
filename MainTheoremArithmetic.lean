import MainTheorem

set_option autoImplicit false

namespace MainTheorem

/-!
## Verified arithmetic endgame

The paper's spectral lemmas reduce the last part of the proof to inequalities of
the following form.  The lemmas in this file are proved in Lean, independently
of the still-unformalized graph-analytic input.
-/

lemma four_K_sq_le_C (d : ℕ) : 4 * (K d) ^ 2 ≤ C d := by
  exact le_max_left _ _

lemma eight_le_C (d : ℕ) : (8 : ℝ) ≤ C d := by
  exact le_trans (le_max_left _ _) (le_max_right _ _)

lemma log_constant_sq_le_C (d : ℕ) :
    (1 + Real.log (2 * (d : ℝ))) ^ 2 ≤ C d := by
  exact le_trans (le_max_right _ _) (le_max_right _ _)

lemma K_ge_two {d : ℕ} (hd : 2 ≤ d) : (2 : ℝ) ≤ K d := by
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h32 : (1 : ℝ) ≤ 32 * (d : ℝ) := by nlinarith
  have h4 : (1 : ℝ) ≤ 4 * ((d + 1 : ℕ) : ℝ) := by
    norm_num
    have : (0 : ℝ) ≤ d := by positivity
    nlinarith
  have hlog32 : 0 ≤ Real.log (32 * (d : ℝ)) := Real.log_nonneg h32
  have hlog4 : 0 ≤ Real.log (4 * ((d + 1 : ℕ) : ℝ)) := Real.log_nonneg h4
  dsimp [K]
  nlinarith

lemma log_le_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let t : ℝ := Real.sqrt (Real.sqrt x)
  have ht0 : 0 < t := by
    dsimp [t]
    positivity
  have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht0
  have hlogt' : Real.log t = Real.log x / 4 := by
    dsimp [t]
    rw [Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt (le_of_lt hx0)]
    ring
  have hquad : 4 * (t - 1) ≤ t ^ 2 := by
    nlinarith [sq_nonneg (t - 2)]
  have ht_sq : t ^ 2 = Real.sqrt x := by
    dsimp [t]
    exact Real.sq_sqrt (Real.sqrt_nonneg x)
  rw [hlogt'] at hlogt
  nlinarith

lemma one_add_log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) :
    (1 + Real.log x) ^ 2 ≤ 4 * x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have ht0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have ht_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx0)
  have hroot : 1 ≤ Real.sqrt x := by
    nlinarith [sq_nonneg (Real.sqrt x - 1)]
  have hlog_sqrt : Real.log x ≤ 2 * Real.sqrt x - 1 := by
    have h := log_le_sqrt hx
    nlinarith
  have hbound : 0 ≤ 2 * Real.sqrt x - (1 + Real.log x) := by
    nlinarith
  have hsum : 0 ≤ 2 * Real.sqrt x + (1 + Real.log x) := by
    nlinarith
  have hprod := mul_nonneg hbound hsum
  nlinarith

lemma bound_of_product_le
    {n m A C₀ : ℝ}
    (hA : 0 < A)
    (hprod : m * A ≤ C₀ * n) :
    m ≤ C₀ * n / A := by
  exact (le_div_iff₀ hA).2 hprod

lemma large_multiplicity_arithmetic
    {n m r L K C₀ : ℝ}
    (hm : 0 ≤ m)
    (hr : 0 < r)
    (hL : 0 < L)
    (hK : 0 ≤ K)
    (hratio : r * m = n)
    (htrade : L ≤ K * Real.sqrt r)
    (hC : 4 * K ^ 2 ≤ C₀)
    (hdouble : 1 + L ≤ 2 * L) :
    m ≤ C₀ * n / (1 + L) ^ 2 := by
  have hsqrt : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsqrt_sq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt (le_of_lt hr)
  have hKR : 0 ≤ K * Real.sqrt r := mul_nonneg hK hsqrt
  have hLsq : L ^ 2 ≤ (K * Real.sqrt r) ^ 2 := by
    nlinarith
  have hLsq' : L ^ 2 ≤ K ^ 2 * r := by
    nlinarith [hsqrt_sq]
  have hmul : m * L ^ 2 ≤ m * (K ^ 2 * r) :=
    mul_le_mul_of_nonneg_left hLsq' hm
  have hn : 0 ≤ n := by
    rw [← hratio]
    positivity
  have hmr : m * L ^ 2 ≤ K ^ 2 * n := by
    calc
      m * L ^ 2 ≤ m * (K ^ 2 * r) := hmul
      _ = K ^ 2 * n := by rw [← hratio]; ring
  have hden : 0 < (1 + L) ^ 2 := by positivity
  have hden_le : (1 + L) ^ 2 ≤ (2 * L) ^ 2 := by
    nlinarith
  have hmul_den : m * (1 + L) ^ 2 ≤ m * (2 * L) ^ 2 :=
    mul_le_mul_of_nonneg_left hden_le hm
  have hprod : m * (1 + L) ^ 2 ≤ C₀ * n := by
    calc
      m * (1 + L) ^ 2 ≤ m * (2 * L) ^ 2 := hmul_den
      _ = 4 * (m * L ^ 2) := by ring
      _ ≤ 4 * (K ^ 2 * n) := by gcongr
      _ ≤ C₀ * n := by
        simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hC hn)
  exact bound_of_product_le hden hprod

lemma positive_gap_arithmetic
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
    have hmul := mul_le_mul_of_nonneg_left hsmall
      (mul_nonneg (le_of_lt hd0) (le_of_lt hr0))
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
        have hsqrt1 : 1 ≤ Real.sqrt r := (Real.one_le_sqrt).2 hr
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

lemma small_multiplicity_branch_arithmetic
    {n m : ℝ} {d : ℕ}
    (hd : 2 ≤ d) (hn : 1 ≤ n) (hm : m ≤ 4) :
    m ≤ C d * n / (1 + Real.log n) ^ 2 := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn
  have hden : 0 < (1 + Real.log n) ^ 2 := by positivity
  have hlogsq : (1 + Real.log n) ^ 2 ≤ 4 * n := one_add_log_sq_le_four_mul hn
  have hprod : m * (1 + Real.log n) ^ 2 ≤ 16 * n := by
    calc
      m * (1 + Real.log n) ^ 2 ≤ 4 * (1 + Real.log n) ^ 2 := by
        gcongr
      _ ≤ 16 * n := by nlinarith
  have hK : (2 : ℝ) ≤ K d := K_ge_two hd
  have hC : (16 : ℝ) ≤ C d := by
    have h4K := four_K_sq_le_C d
    nlinarith [sq_nonneg (K d - 2)]
  apply bound_of_product_le hden
  calc
    m * (1 + Real.log n) ^ 2 ≤ 16 * n := hprod
    _ ≤ C d * n := by gcongr
    

lemma bound_of_product_le_after
    {n m A C₀ : ℝ}
    (hA : 0 < A)
    (hprod : m * A ≤ C₀ * n) :
    m ≤ C₀ * n / A := by
  exact (le_div_iff₀ hA).2 hprod

/-- The large-multiplicity branch after Proposition 2.4 and Lemma 3.1. -/
lemma large_multiplicity_arithmetic_after
    {n m r L K C₀ : ℝ}
    (hm : 0 ≤ m)
    (hr : 0 < r)
    (hL : 0 < L)
    (hK : 0 ≤ K)
    (hratio : r * m = n)
    (htrade : L ≤ K * Real.sqrt r)
    (hC : 4 * K ^ 2 ≤ C₀)
    (hdouble : 1 + L ≤ 2 * L) :
    m ≤ C₀ * n / (1 + L) ^ 2 := by
  have hsqrt : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsqrt_sq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt (le_of_lt hr)
  have hKR : 0 ≤ K * Real.sqrt r := mul_nonneg hK hsqrt
  have hLsq : L ^ 2 ≤ (K * Real.sqrt r) ^ 2 := by
    nlinarith
  have hLsq' : L ^ 2 ≤ K ^ 2 * r := by
    nlinarith [hsqrt_sq]
  have hmul : m * L ^ 2 ≤ m * (K ^ 2 * r) :=
    mul_le_mul_of_nonneg_left hLsq' hm
  have hn : 0 ≤ n := by
    rw [← hratio]
    positivity
  have hmr : m * L ^ 2 ≤ K ^ 2 * n := by
    calc
      m * L ^ 2 ≤ m * (K ^ 2 * r) := hmul
      _ = K ^ 2 * n := by rw [← hratio]; ring
  have hden : 0 < (1 + L) ^ 2 := by positivity
  have hden_le : (1 + L) ^ 2 ≤ (2 * L) ^ 2 := by
    nlinarith
  have hmul_den : m * (1 + L) ^ 2 ≤ m * (2 * L) ^ 2 :=
    mul_le_mul_of_nonneg_left hden_le hm
  have hprod : m * (1 + L) ^ 2 ≤ C₀ * n := by
    calc
      m * (1 + L) ^ 2 ≤ m * (2 * L) ^ 2 := hmul_den
      _ = 4 * (m * L ^ 2) := by ring
      _ ≤ 4 * (K ^ 2 * n) := by gcongr
      _ ≤ C₀ * n := by
        simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hC hn)
  exact bound_of_product_le hden hprod

/-- The small-multiplicity branch, with the elementary estimate already supplied. -/
lemma small_multiplicity_arithmetic_from_product
    {n m L C₀ : ℝ}
    (hn : 0 ≤ n)
    (hprod : m * (1 + L) ^ 2 ≤ 8 * n)
    (hC : 8 ≤ C₀)
    (hden : 0 < (1 + L) ^ 2) :
    m ≤ C₀ * n / (1 + L) ^ 2 := by
  apply bound_of_product_le hden
  calc
    m * (1 + L) ^ 2 ≤ 8 * n := hprod
    _ ≤ C₀ * n := mul_le_mul_of_nonneg_right hC hn

/-- The `λ₂ ≤ 0` branch, once the logarithm comparison is supplied. -/
lemma nonpositive_second_eigenvalue_arithmetic
    {n m L U C₀ : ℝ}
    (hn : 0 ≤ n)
    (hm : 0 ≤ m)
    (hmn : m ≤ n)
    (hL : 0 ≤ 1 + L)
    (hU : 0 ≤ 1 + U)
    (hlog : 1 + L ≤ 1 + U)
    (hC : (1 + U) ^ 2 ≤ C₀)
    (hden : 0 < (1 + L) ^ 2) :
    m ≤ C₀ * n / (1 + L) ^ 2 := by
  have hsquares : (1 + L) ^ 2 ≤ (1 + U) ^ 2 := by
    nlinarith
  have h₁ : m * (1 + L) ^ 2 ≤ m * (1 + U) ^ 2 :=
    mul_le_mul_of_nonneg_left hsquares hm
  have h₂ : m * (1 + U) ^ 2 ≤ n * (1 + U) ^ 2 := by
    exact mul_le_mul_of_nonneg_right hmn (sq_nonneg (1 + U))
  have h₃ : n * (1 + U) ^ 2 ≤ C₀ * n := by
    calc
      n * (1 + U) ^ 2 ≤ n * C₀ := mul_le_mul_of_nonneg_left hC hn
      _ = C₀ * n := by ring
  apply bound_of_product_le hden
  exact h₁.trans (h₂.trans h₃)

/-!
The elementary trace argument used in the `λ₂ ≤ 0` branch.  This is stated
for a finite list of real eigenvalues so that the spectral theorem can feed it
directly once the multiplicity of the top eigenvalue has been identified.
-/
lemma nonpositive_spectrum_card_bound
    {n d : ℕ} (hd : 0 < d) (θ : Fin n → ℝ) (i₀ : Fin n)
    (hθbottom : ∀ i, - (d : ℝ) ≤ θ i)
    (hθnonpos : ∀ i, i ≠ i₀ → θ i ≤ 0)
    (hθi₀ : θ i₀ = d)
    (htrace : ∑ i, θ i = 0)
    (htrace_sq : ∑ i, (θ i) ^ 2 = (n : ℝ) * d) :
    n ≤ 2 * d := by
  have hsq : ∀ i ∈ Finset.univ.erase i₀, (θ i) ^ 2 ≤ (d : ℝ) * (-θ i) := by
    intro i hi
    have hne : i ≠ i₀ := by simpa using (Finset.mem_erase.mp hi).1
    have hnonpos := hθnonpos i hne
    have hbottom := hθbottom i
    nlinarith
  have hsum_sq :
      ∑ i ∈ Finset.univ.erase i₀, (θ i) ^ 2 ≤
        (d : ℝ) * ∑ i ∈ Finset.univ.erase i₀, (-θ i) := by
    calc
      ∑ i ∈ Finset.univ.erase i₀, (θ i) ^ 2 ≤
        ∑ i ∈ Finset.univ.erase i₀, (d : ℝ) * (-θ i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hsq i hi
      _ = (d : ℝ) * ∑ i ∈ Finset.univ.erase i₀, (-θ i) := by
        rw [Finset.mul_sum]
  have hsum : ∑ i ∈ Finset.univ.erase i₀, θ i = -(d : ℝ) := by
    have hdecomp := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) θ
      (a := i₀) (Finset.mem_univ i₀)
    rw [hθi₀] at hdecomp
    linarith
  have hsum_neg : ∑ i ∈ Finset.univ.erase i₀, (-θ i) = (d : ℝ) := by
    rw [Finset.sum_neg_distrib θ]
    rw [hsum]
    ring
  have hsq_decomp := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun i => (θ i) ^ 2) (a := i₀) (Finset.mem_univ i₀)
  rw [hθi₀] at hsq_decomp
  have htotal : (n : ℝ) * d ≤ 2 * (d : ℝ) ^ 2 := by
    calc
      (n : ℝ) * d = ∑ i, (θ i) ^ 2 := htrace_sq.symm
      _ = (d : ℝ) ^ 2 + ∑ i ∈ Finset.univ.erase i₀, (θ i) ^ 2 := by
        linarith [hsq_decomp]
      _ ≤ (d : ℝ) ^ 2 + (d : ℝ) *
          ∑ i ∈ Finset.univ.erase i₀, (-θ i) := by
        gcongr
      _ = 2 * (d : ℝ) ^ 2 := by rw [hsum_neg]; ring
  have hdn : (0 : ℝ) < d := by exact_mod_cast hd
  have hreal : (n : ℝ) ≤ 2 * d := by nlinarith
  exact_mod_cast hreal

end MainTheorem
