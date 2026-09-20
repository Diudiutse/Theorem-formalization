import CheckLemma22
import CheckLemma21

set_option autoImplicit false

namespace TheoremOnePointOne

open scoped InnerProductSpace BigOperators Pointwise

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma adjacency_apply_coord
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (f : EuclideanSpace ℝ V) (x : V) :
    (Matrix.toEuclideanLin (adjacencyMatrix G) f).ofLp x =
      ∑ y : V, if G.Adj x y then f.ofLp y else 0 := by
  rw [Matrix.toLpLin_apply]
  simp only [Matrix.mulVec, adjacencyMatrix, SimpleGraph.adjMatrix_apply]
  rw [dotProduct]
  simp

noncomputable def positivePart (f : EuclideanSpace ℝ V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun x => max (f.ofLp x) 0)

noncomputable def cutoffScalar (T a : ℝ) : ℝ :=
  if 0 < a then min 1 (max 0 (1 + Real.log a / T)) else 0

noncomputable def cutoffVector (T : ℝ) (p : EuclideanSpace ℝ V) :
    EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun x => p.ofLp x * cutoffScalar T (p.ofLp x))

omit [Fintype V] [DecidableEq V] in
lemma positivePart_coord (f : EuclideanSpace ℝ V) (x : V) :
    (positivePart f).ofLp x = max (f.ofLp x) 0 := by
  rfl

omit [Fintype V] [DecidableEq V] in
lemma cutoffVector_coord (T : ℝ) (p : EuclideanSpace ℝ V) (x : V) :
    (cutoffVector T p).ofLp x =
      p.ofLp x * cutoffScalar T (p.ofLp x) := by
  rfl

omit [DecidableEq V] in
lemma norm_sq_eq_sum_coord (f : EuclideanSpace ℝ V) :
    ‖f‖ ^ 2 = ∑ x : V, (f.ofLp x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp

omit [DecidableEq V] in
lemma degree_sum_real
    {G : SimpleGraph V} {d : ℕ} [DecidableRel G.Adj]
    (hreg : IsRegularFinite G d) (x : V) :
    (∑ y : V, (if G.Adj x y then (1 : ℝ) else 0)) = d := by
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
    (∑ y : V, (if G.Adj x y then (1 : ℝ) else 0)) =
        (finiteDegree G x : ℝ) := by exact_mod_cast hsumNat
    _ = d := by exact_mod_cast finiteDegree_eq_of_regular hreg x

lemma dirichletEnergy_eq_half_sum
    {G : SimpleGraph V} {d : ℕ} [DecidableRel G.Adj]
    (hreg : IsRegularFinite G d) (f : EuclideanSpace ℝ V) :
    dirichletEnergy G d f =
      (1 / 2 : ℝ) * ∑ x : V, ∑ y : V,
        (if G.Adj x y then (f.ofLp x - f.ofLp y) ^ 2 else 0) := by
  have hdeg (x : V) := degree_sum_real hreg x
  have hfirst :
      ∑ x : V, ∑ y : V, (if G.Adj x y then (f.ofLp x) ^ 2 else 0) =
        (d : ℝ) * ∑ x : V, (f.ofLp x) ^ 2 := by
    calc
      _ = ∑ x : V, (f.ofLp x) ^ 2 *
          (∑ y : V, (if G.Adj x y then (1 : ℝ) else 0)) := by
        apply Fintype.sum_congr
        intro x
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hxy : G.Adj x y
        · simp [hxy]
        · simp [hxy]
      _ = ∑ x : V, (f.ofLp x) ^ 2 * (d : ℝ) := by
        apply Fintype.sum_congr
        intro x
        rw [hdeg]
      _ = (d : ℝ) * ∑ x : V, (f.ofLp x) ^ 2 := by
        rw [Finset.mul_sum]
        apply Fintype.sum_congr
        intro x
        ring
  have hsecond :
      ∑ x : V, ∑ y : V, (if G.Adj x y then (f.ofLp y) ^ 2 else 0) =
        (d : ℝ) * ∑ x : V, (f.ofLp x) ^ 2 := by
    calc
      _ = ∑ y : V, ∑ x : V,
          (if G.Adj x y then (f.ofLp y) ^ 2 else 0) := by
        rw [Finset.sum_comm]
      _ = ∑ y : V, (f.ofLp y) ^ 2 *
          (∑ x : V, (if G.Adj y x then (1 : ℝ) else 0)) := by
        apply Fintype.sum_congr
        intro y
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxy : G.Adj y x
        · simp [hxy, SimpleGraph.adj_comm]
        · simp [hxy, SimpleGraph.adj_comm]
      _ = (d : ℝ) * ∑ x : V, (f.ofLp x) ^ 2 := by
        simp_rw [hdeg]
        rw [Finset.mul_sum]
        apply Fintype.sum_congr
        intro x
        ring
  have hcross :
      ∑ x : V, ∑ y : V,
          (if G.Adj x y then f.ofLp x * f.ofLp y else 0) =
        ⟪Matrix.toEuclideanLin (adjacencyMatrix G) f, f⟫_ℝ := by
    simpa [mul_comm] using (adjacency_inner_expand (G := G) f f).symm
  have hexpand :
      (∑ x : V, ∑ y : V,
        (if G.Adj x y then (f.ofLp x - f.ofLp y) ^ 2 else 0)) =
      (d : ℝ) * ∑ x : V, (f.ofLp x) ^ 2 +
        (d : ℝ) * ∑ x : V, (f.ofLp x) ^ 2 -
        2 * ⟪Matrix.toEuclideanLin (adjacencyMatrix G) f, f⟫_ℝ := by
    calc
      _ = (∑ x : V, ∑ y : V,
          (if G.Adj x y then (f.ofLp x) ^ 2 else 0)) +
          (∑ x : V, ∑ y : V,
          (if G.Adj x y then (f.ofLp y) ^ 2 else 0)) -
          2 * (∑ x : V, ∑ y : V,
          (if G.Adj x y then f.ofLp x * f.ofLp y else 0)) := by
        have hdistrib (q₁ q₂ q₃ : V → V → ℝ) :
            (∑ x : V, ∑ y : V, (q₁ x y + q₂ x y - 2 * q₃ x y)) =
              (∑ x : V, ∑ y : V, (q₁ x y)) +
                (∑ x : V, ∑ y : V, (q₂ x y)) -
                2 * (∑ x : V, ∑ y : V, (q₃ x y)) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.mul_sum]
        calc
          _ = (∑ x : V, ∑ y : V,
              ((if G.Adj x y then (f.ofLp x) ^ 2 else 0) +
                (if G.Adj x y then (f.ofLp y) ^ 2 else 0) -
                2 * (if G.Adj x y then f.ofLp x * f.ofLp y else 0))) := by
            apply Fintype.sum_congr
            intro x
            apply Fintype.sum_congr
            intro y
            by_cases hxy : G.Adj x y
            · simp [hxy]
              ring
            · simp [hxy]
          _ = _ := hdistrib _ _ _
      _ = _ := by rw [hfirst, hsecond, hcross]
  rw [dirichletEnergy, inner_sub_left]
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_sq_eq_sum_coord]
  rw [hexpand]
  ring

lemma geom_log_le_abs_sub
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) * |Real.log a - Real.log b| ≤ |a - b| := by
  have hpos : ∀ {a b : ℝ}, 0 < a → 0 < b →
      0 ≤ Real.log a - Real.log b →
      Real.sqrt (a * b) * (Real.log a - Real.log b) ≤ a - b := by
    intro a b ha hb hlog
    have hab : b ≤ a := by
      have hlog' : Real.log b ≤ Real.log a := by linarith
      have h := Real.exp_le_exp.mpr hlog'
      simpa [Real.exp_log ha, Real.exp_log hb] using h
    have hrootmul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
      exact Real.sqrt_mul (le_of_lt ha) b
    have hxdiv :
        (Real.log a - Real.log b) / 2 = Real.log (a / b) / 2 := by
      rw [Real.log_div ha.ne' hb.ne']
    have hexphalf :
        Real.exp ((Real.log a - Real.log b) / 2) = Real.sqrt (a / b) := by
      calc
        Real.exp ((Real.log a - Real.log b) / 2) =
            Real.exp (Real.log (a / b) / 2) := by rw [hxdiv]
        _ = Real.sqrt (Real.exp (Real.log (a / b))) := Real.exp_half _
        _ = Real.sqrt (a / b) := by rw [Real.exp_log (div_pos ha hb)]
    have hxnegdiv :
        -(Real.log a - Real.log b) / 2 = Real.log (b / a) / 2 := by
      rw [Real.log_div hb.ne' ha.ne']
      ring_nf
    have hexpneg :
        Real.exp (-(Real.log a - Real.log b) / 2) = Real.sqrt (b / a) := by
      calc
        Real.exp (-(Real.log a - Real.log b) / 2) =
            Real.exp (Real.log (b / a) / 2) := by rw [hxnegdiv]
        _ = Real.sqrt (Real.exp (Real.log (b / a))) := Real.exp_half _
        _ = Real.sqrt (b / a) := by rw [Real.exp_log (div_pos hb ha)]
    have hroot_exp :
        Real.sqrt (a * b) * Real.exp ((Real.log a - Real.log b) / 2) = a := by
      rw [hexphalf, hrootmul, Real.sqrt_div (le_of_lt ha)]
      have hsa : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (le_of_lt ha)
      have hsbpos : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
      field_simp [ne_of_gt hsbpos]
      nlinarith
    have hroot_exp_neg :
        Real.sqrt (a * b) * Real.exp (-(Real.log a - Real.log b) / 2) = b := by
      rw [hexpneg, hrootmul, Real.sqrt_div (le_of_lt hb)]
      have hsb : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (le_of_lt hb)
      have hsapos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
      field_simp [ne_of_gt hsapos]
      nlinarith
    have hsinh :
        Real.log a - Real.log b ≤
          2 * Real.sinh ((Real.log a - Real.log b) / 2) := by
      have hhalf : 0 ≤ (Real.log a - Real.log b) / 2 := by linarith
      have h := (Real.self_le_sinh_iff).2 hhalf
      nlinarith
    have hid :
        Real.sqrt (a * b) *
            (2 * Real.sinh ((Real.log a - Real.log b) / 2)) = a - b := by
      calc
        Real.sqrt (a * b) *
            (2 * Real.sinh ((Real.log a - Real.log b) / 2)) =
            Real.sqrt (a * b) *
              (Real.exp ((Real.log a - Real.log b) / 2) -
                Real.exp (-(Real.log a - Real.log b) / 2)) := by
          rw [Real.sinh_eq]
          ring_nf
        _ = a - b := by rw [mul_sub, hroot_exp, hroot_exp_neg]
    exact le_trans (mul_le_mul_of_nonneg_left hsinh (Real.sqrt_nonneg _))
      (le_of_eq hid)
  let x : ℝ := Real.log a - Real.log b
  by_cases hx : 0 ≤ x
  · have hxa : 0 ≤ Real.log a - Real.log b := by simpa [x] using hx
    have hba : b ≤ a := by
      have hlog : Real.log b ≤ Real.log a := by linarith
      have h := Real.exp_le_exp.mpr hlog
      simpa [Real.exp_log ha, Real.exp_log hb] using h
    rw [abs_of_nonneg hxa, abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hpos ha hb hxa
  ·
    have hcomm : Real.sqrt (b * a) = Real.sqrt (a * b) := by rw [mul_comm]
    have hxa : Real.log a - Real.log b < 0 := by
      simpa [x] using lt_of_not_ge hx
    have hxb : 0 ≤ Real.log b - Real.log a := by linarith
    have hba' : b - a ≥ 0 := by
      have hlog : Real.log a ≤ Real.log b := by linarith
      have h := Real.exp_le_exp.mpr hlog
      have : a ≤ b := by simpa [Real.exp_log ha, Real.exp_log hb] using h
      linarith
    calc
      Real.sqrt (a * b) * |Real.log a - Real.log b| =
          Real.sqrt (b * a) * (Real.log b - Real.log a) := by
            rw [abs_of_neg hxa, hcomm]
            ring
      _ ≤ b - a := hpos hb ha hxb
      _ = |a - b| := by rw [abs_of_nonpos (by linarith : a - b ≤ 0)]; ring

lemma geom_log_sq_le_sub_sq
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * b * (Real.log a - Real.log b) ^ 2 ≤ (a - b) ^ 2 := by
  have h := geom_log_le_abs_sub ha hb
  have hsqrt : (Real.sqrt (a * b)) ^ 2 = a * b :=
    Real.sq_sqrt (le_of_lt (mul_pos ha hb))
  have hnonneg₁ : 0 ≤ Real.sqrt (a * b) *
      |Real.log a - Real.log b| := by positivity
  have hnonneg₂ : 0 ≤ |a - b| := abs_nonneg _
  have hsq :
      (Real.sqrt (a * b) * |Real.log a - Real.log b|) ^ 2 ≤
        |a - b| ^ 2 := by
    nlinarith
  rw [sq_abs] at hsq
  calc
    a * b * (Real.log a - Real.log b) ^ 2 =
        (Real.sqrt (a * b)) ^ 2 *
          (Real.log a - Real.log b) ^ 2 := by rw [hsqrt]
    _ = (Real.sqrt (a * b) * |Real.log a - Real.log b|) ^ 2 := by
          have habs : |Real.log a - Real.log b| ^ 2 =
              (Real.log a - Real.log b) ^ 2 := sq_abs _
          calc
            (Real.sqrt (a * b)) ^ 2 *
                (Real.log a - Real.log b) ^ 2 =
                (Real.sqrt (a * b)) ^ 2 *
                  |Real.log a - Real.log b| ^ 2 := by rw [habs]
            _ = (Real.sqrt (a * b) *
                |Real.log a - Real.log b|) ^ 2 := by ring
    _ ≤ (a - b) ^ 2 := hsq

lemma cutoff_scalar_edge_bound
    {T a b : ℝ} (hT : 0 < T) (ha : 0 < a) (hb : 0 < b) :
    a * b * (cutoffScalar T a - cutoffScalar T b) ^ 2 ≤
      (a - b) ^ 2 / T ^ 2 := by
  have hclip : LipschitzWith 1 (fun z : ℝ => min 1 (max 0 z)) := by
    simpa only [id_eq] using (LipschitzWith.id.const_max 0).const_min 1
  have hclip' := hclip.dist_le_mul
    (1 + Real.log a / T) (1 + Real.log b / T)
  have hclip'' :
      |min 1 (max 0 (1 + Real.log a / T)) -
          min 1 (max 0 (1 + Real.log b / T))| ≤
        |(1 + Real.log a / T) - (1 + Real.log b / T)| := by
    simpa [Real.dist_eq] using hclip'
  have hq :
      |cutoffScalar T a - cutoffScalar T b| ≤
        |Real.log a - Real.log b| / T := by
    calc
      |cutoffScalar T a - cutoffScalar T b| ≤
          |(1 + Real.log a / T) - (1 + Real.log b / T)| := by
            simpa [cutoffScalar, ha, hb] using hclip''
      _ = |Real.log a - Real.log b| / T := by
        rw [show (1 + Real.log a / T) - (1 + Real.log b / T) =
            (Real.log a - Real.log b) / T by ring]
        rw [abs_div, abs_of_pos hT]
  have hqnonneg : 0 ≤ |cutoffScalar T a - cutoffScalar T b| := abs_nonneg _
  have hrightnonneg : 0 ≤ |Real.log a - Real.log b| / T := by positivity
  have hq_sq :
      |cutoffScalar T a - cutoffScalar T b| ^ 2 ≤
        (|Real.log a - Real.log b| / T) ^ 2 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hq_sq
    (mul_nonneg (le_of_lt ha) (le_of_lt hb))
  have hlog := geom_log_sq_le_sub_sq ha hb
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
  calc
    a * b * (cutoffScalar T a - cutoffScalar T b) ^ 2 =
        a * b * |cutoffScalar T a - cutoffScalar T b| ^ 2 := by rw [sq_abs]
    _ ≤ a * b * (|Real.log a - Real.log b| / T) ^ 2 := hmul
    _ = (a * b * (Real.log a - Real.log b) ^ 2) / T ^ 2 := by
      rw [div_pow, sq_abs]
      ring
    _ ≤ (a - b) ^ 2 / T ^ 2 := by
      exact div_le_div_of_nonneg_right hlog (le_of_lt hT2)

lemma positive_part_eigen_ineq
    {G : SimpleGraph V} {lam : ℝ} {f : EuclideanSpace ℝ V}
    [DecidableRel G.Adj]
    (_hlam : 0 < lam)
    (heig : Matrix.toEuclideanLin (adjacencyMatrix G) f = lam • f) :
    ∀ x : V,
      lam * (positivePart f).ofLp x ≤
        (Matrix.toEuclideanLin (adjacencyMatrix G) (positivePart f)).ofLp x := by
  intro x
  have hcoord :
      (∑ y : V, if G.Adj x y then f.ofLp y else 0) = lam * f.ofLp x := by
    have h := congrArg (fun z : EuclideanSpace ℝ V => z.ofLp x) heig
    rw [adjacency_apply_coord] at h
    simpa using h
  by_cases hfx : 0 ≤ f.ofLp x
  · rw [adjacency_apply_coord]
    rw [positivePart_coord, max_eq_left hfx]
    simp_rw [positivePart_coord]
    calc
      lam * f.ofLp x = ∑ y : V, if G.Adj x y then f.ofLp y else 0 := hcoord.symm
      _ ≤ ∑ y : V, if G.Adj x y then max (f.ofLp y) 0 else 0 := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hxy : G.Adj x y
        · simp [hxy]
        · simp [hxy]
  · have hfx' : f.ofLp x ≤ 0 := le_of_not_ge hfx
    rw [adjacency_apply_coord]
    rw [positivePart_coord, max_eq_right hfx']
    simp_rw [positivePart_coord]
    have hnonneg : ∀ y : V, 0 ≤ if G.Adj x y then max (f.ofLp y) 0 else 0 := by
      intro y
      by_cases hxy : G.Adj x y
      · simp [hxy]
      · simp [hxy]
    have hsum : 0 ≤ ∑ y : V, if G.Adj x y then max (f.ofLp y) 0 else 0 := by
      exact Finset.sum_nonneg (fun y hy => hnonneg y)
    simpa using hsum

omit [Fintype V] [DecidableEq V] in
lemma positive_part_edge_sq_le
    {f : EuclideanSpace ℝ V} (x y : V) :
    ((positivePart f).ofLp x - (positivePart f).ofLp y) ^ 2 ≤
      (f.ofLp x - f.ofLp y) ^ 2 := by
  have hclip : LipschitzWith 1 (fun z : ℝ => max 0 z) := by
    simpa only [id_eq] using LipschitzWith.id.const_max 0
  have h := hclip.dist_le_mul (f.ofLp x) (f.ofLp y)
  have habs :
      |(positivePart f).ofLp x - (positivePart f).ofLp y| ≤
        |f.ofLp x - f.ofLp y| := by
    simpa [positivePart_coord, max_comm, Real.dist_eq] using h
  have hsquare :
      |(positivePart f).ofLp x - (positivePart f).ofLp y| ^ 2 ≤
        |f.ofLp x - f.ofLp y| ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 habs
  simpa [sq_abs] using hsquare

lemma ground_state_identity
    {G : SimpleGraph V} {lam : ℝ} [DecidableRel G.Adj]
    (p c : V → ℝ) (u : EuclideanSpace ℝ V)
    (hu : ∀ x : V, u.ofLp x = p x * c x) :
    ⟪Matrix.toEuclideanLin (adjacencyMatrix G) u, u⟫_ℝ -
        lam * ‖u‖ ^ 2 =
      ∑ x : V, c x ^ 2 * p x *
          ((Matrix.toEuclideanLin (adjacencyMatrix G)
            (WithLp.toLp 2 p)).ofLp x - lam * p x) -
        (1 / 2 : ℝ) * ∑ x : V, ∑ y : V,
          (if G.Adj x y then p x * p y * (c x - c y) ^ 2 else 0) := by
  have hA_u := adjacency_inner_expand (G := G) u u
  have hnorm_u := norm_sq_eq_sum_coord u
  have hfirst :
      ∑ x : V, c x ^ 2 * p x *
          ((Matrix.toEuclideanLin (adjacencyMatrix G)
            (WithLp.toLp 2 p)).ofLp x - lam * p x) =
        (∑ x : V, ∑ y : V,
          (if G.Adj x y then c x ^ 2 * p x * p y else 0)) -
          lam * ∑ x : V, (p x * c x) ^ 2 := by
    calc
      _ = ∑ x : V, c x ^ 2 * p x *
          ((∑ y : V, if G.Adj x y then p y else 0) - lam * p x) := by
            apply Fintype.sum_congr
            intro x
            simp only [adjacency_apply_coord]
      _ = (∑ x : V, ∑ y : V,
          (if G.Adj x y then c x ^ 2 * p x * p y else 0)) -
          lam * ∑ x : V, (p x * c x) ^ 2 := by
            calc
              _ = ∑ x : V,
                  (c x ^ 2 * p x *
                    (∑ y : V, if G.Adj x y then p y else 0) -
                    lam * (p x * c x) ^ 2) := by
                apply Fintype.sum_congr
                intro x
                ring
              _ = (∑ x : V, c x ^ 2 * p x *
                    (∑ y : V, if G.Adj x y then p y else 0)) -
                    ∑ x : V, lam * (p x * c x) ^ 2 := by
                rw [Finset.sum_sub_distrib]
              _ = (∑ x : V, ∑ y : V,
                  (if G.Adj x y then c x ^ 2 * p x * p y else 0)) -
                    lam * ∑ x : V, (p x * c x) ^ 2 := by
                congr 1
                · apply Fintype.sum_congr
                  intro x
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro y hy
                  by_cases hxy : G.Adj x y
                  · simp [hxy]
                  · simp [hxy]
                · rw [Finset.mul_sum]
  have hswap :
      (∑ x : V, ∑ y : V,
          (if G.Adj x y then p x * p y * c y ^ 2 else 0)) =
        ∑ x : V, ∑ y : V,
          (if G.Adj x y then p x * p y * c x ^ 2 else 0) := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro x
    apply Fintype.sum_congr
    intro y
    by_cases hxy : G.Adj y x
    · have hxy' : G.Adj x y := (G.adj_comm x y).mpr hxy
      rw [if_pos hxy, if_pos hxy']
      ring
    · have hxy' : ¬ G.Adj x y := by
        intro h
        exact hxy ((G.adj_comm x y).mp h)
      rw [if_neg hxy, if_neg hxy']
  have hedge :
      ∑ x : V, ∑ y : V,
          (if G.Adj x y then p x * p y * (c x - c y) ^ 2 else 0) =
        (∑ x : V, ∑ y : V,
          (if G.Adj x y then p x * p y * c x ^ 2 else 0)) +
          (∑ x : V, ∑ y : V,
          (if G.Adj x y then p x * p y * c y ^ 2 else 0)) -
          2 * (∑ x : V, ∑ y : V,
          (if G.Adj x y then p x * p y * c x * c y else 0)) := by
    calc
      _ = ∑ x : V, ∑ y : V,
          ((if G.Adj x y then p x * p y * c x ^ 2 else 0) +
            (if G.Adj x y then p x * p y * c y ^ 2 else 0) -
            2 * (if G.Adj x y then p x * p y * c x * c y else 0)) := by
        apply Fintype.sum_congr
        intro x
        apply Fintype.sum_congr
        intro y
        by_cases hxy : G.Adj x y
        · simp [hxy]
          ring
        · simp [hxy]
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.mul_sum]
  have hcross :
      (∑ x : V, ∑ y : V,
          (if G.Adj x y then p y * c y else 0) * (p x * c x)) =
        ∑ x : V, ∑ y : V,
          (if G.Adj x y then p x * p y * c x * c y else 0) := by
    apply Fintype.sum_congr
    intro x
    apply Fintype.sum_congr
    intro y
    by_cases hxy : G.Adj x y
    · simp [hxy]
      ring
    · simp [hxy]
  have hcomm :
      (∑ x : V, ∑ y : V,
          (if G.Adj x y then c x ^ 2 * p x * p y else 0)) =
        ∑ x : V, ∑ y : V,
          (if G.Adj x y then p x * p y * c x ^ 2 else 0) := by
    apply Fintype.sum_congr
    intro x
    apply Fintype.sum_congr
    intro y
    by_cases hxy : G.Adj x y
    · simp [hxy]
      ring
    · simp [hxy]
  rw [hA_u, hnorm_u]
  simp only [hu]
  rw [hcross, hfirst, hedge, hswap, hcomm]
  ring

lemma cutoff_quadratic_lower_bound
    {G : SimpleGraph V} {d : ℕ} {lam T : ℝ}
    [DecidableRel G.Adj]
    (hreg : IsRegularFinite G d) (hT : 0 < T)
    (p c : V → ℝ) (u f : EuclideanSpace ℝ V)
    (hu : ∀ x : V, u.ofLp x = p x * c x)
    (hp : ∀ x : V, 0 ≤ p x)
    (hres : ∀ x : V,
      lam * p x ≤
        (Matrix.toEuclideanLin (adjacencyMatrix G)
          (WithLp.toLp 2 p)).ofLp x)
    (hcut : ∀ x y : V,
      (if G.Adj x y then p x * p y * (c x - c y) ^ 2 else 0) ≤
        (if G.Adj x y then (f.ofLp x - f.ofLp y) ^ 2 / T ^ 2 else 0)) :
    lam * ‖u‖ ^ 2 - dirichletEnergy G d f / T ^ 2 ≤
      ⟪Matrix.toEuclideanLin (adjacencyMatrix G) u, u⟫_ℝ := by
  have hfirst :
      0 ≤ ∑ x : V, c x ^ 2 * p x *
        ((Matrix.toEuclideanLin (adjacencyMatrix G)
          (WithLp.toLp 2 p)).ofLp x - lam * p x) := by
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (mul_nonneg (sq_nonneg (c x)) (hp x))
      (sub_nonneg.mpr (hres x))
  have hcut_sum :
      (∑ x : V, ∑ y : V,
        (if G.Adj x y then p x * p y * (c x - c y) ^ 2 else 0)) ≤
      (1 / T ^ 2 : ℝ) *
        (∑ x : V, ∑ y : V,
          (if G.Adj x y then (f.ofLp x - f.ofLp y) ^ 2 else 0)) := by
    calc
      _ ≤ ∑ x : V, ∑ y : V,
          (if G.Adj x y then (f.ofLp x - f.ofLp y) ^ 2 / T ^ 2 else 0) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        exact hcut x y
      _ = _ := by
        rw [Finset.mul_sum]
        apply Fintype.sum_congr
        intro x
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hxy : G.Adj x y
        · simp [hxy, div_eq_mul_inv, mul_comm]
        · simp [hxy]
  have hdir := dirichletEnergy_eq_half_sum hreg f
  have hhalf :
      (1 / 2 : ℝ) *
          (∑ x : V, ∑ y : V,
            (if G.Adj x y then p x * p y * (c x - c y) ^ 2 else 0)) ≤
        dirichletEnergy G d f / T ^ 2 := by
    have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
    have := mul_le_mul_of_nonneg_left hcut_sum (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [hdir]
    calc
      (1 / 2 : ℝ) *
          (∑ x : V, ∑ y : V,
            (if G.Adj x y then p x * p y * (c x - c y) ^ 2 else 0)) ≤
          (1 / 2 : ℝ) * ((1 / T ^ 2 : ℝ) *
            (∑ x : V, ∑ y : V,
              (if G.Adj x y then (f.ofLp x - f.ofLp y) ^ 2 else 0))) := this
      _ = ((1 / 2 : ℝ) *
          (∑ x : V, ∑ y : V,
            (if G.Adj x y then (f.ofLp x - f.ofLp y) ^ 2 else 0))) /
            T ^ 2 := by ring
  have hid := ground_state_identity (G := G) (lam := lam) p c u hu
  nlinarith [hid, hfirst, hhalf]

lemma cutoff_data_ready
    (G : SimpleGraph V) (d : ℕ) (lam T : ℝ)
    (_hconn : G.Connected) (hreg : IsRegularFinite G d)
    (_hvt : IsVertexTransitive G)
    (hlam_pos : 0 < lam)
    (o w : V) (φ : EuclideanSpace ℝ V)
    (how : G.Adj o w)
    (hφeig : Matrix.toEuclideanLin (adjacencyMatrix G) φ = lam • φ)
    (hφo : φ.ofLp o = 1) (hφw : φ.ofLp w ≤ 0)
    (hTpos : 0 < T)
    (_hT : lam * dirichletEnergy G d φ < T ^ 2) :
    ∃ F : Finset V, ∃ u : EuclideanSpace ℝ V,
      F.Nonempty ∧ supportedOn F u ∧ u.ofLp w = 0 ∧
      1 ≤ (Matrix.toEuclideanLin (adjacencyMatrix G) u).ofLp w ∧
      lam * ‖u‖ ^ 2 - dirichletEnergy G d φ / T ^ 2 ≤
        ⟪Matrix.toEuclideanLin (adjacencyMatrix G) u, u⟫_ℝ ∧
      (F.card : ℝ) ≤ Real.exp (2 * T) * ‖φ‖ ^ 2 := by
  classical
  let p : EuclideanSpace ℝ V := positivePart φ
  let c : V → ℝ := fun x => cutoffScalar T (p.ofLp x)
  let u : EuclideanSpace ℝ V := cutoffVector T p
  let F : Finset V := Finset.univ.filter (fun x => Real.exp (-T) < p.ofLp x)
  have hp (x : V) : 0 ≤ p.ofLp x := by
    dsimp [p]
    rw [positivePart_coord]
    exact le_max_right _ _
  have hc (a : ℝ) : 0 ≤ cutoffScalar T a := by
    unfold cutoffScalar
    split
    · exact le_min (by norm_num) (le_max_left _ _)
    · norm_num
  have hu (x : V) : u.ofLp x = p.ofLp x * c x := by
    dsimp [u, c]
    exact cutoffVector_coord T p x
  have hres (x : V) :
      lam * p.ofLp x ≤
        (Matrix.toEuclideanLin (adjacencyMatrix G)
          (WithLp.toLp 2 (fun y => p.ofLp y))).ofLp x := by
    simpa [p] using (positive_part_eigen_ineq hlam_pos hφeig x)
  have hcut (x y : V) :
      (if G.Adj x y then p.ofLp x * p.ofLp y * (c x - c y) ^ 2 else 0) ≤
        (if G.Adj x y then (φ.ofLp x - φ.ofLp y) ^ 2 / T ^ 2 else 0) := by
    by_cases hxy : G.Adj x y
    · simp only [if_pos hxy]
      by_cases hpx : 0 < p.ofLp x
      · by_cases hpy : 0 < p.ofLp y
        · have h₁ := cutoff_scalar_edge_bound hTpos hpx hpy
          have h₂ := positive_part_edge_sq_le (f := φ) x y
          dsimp [c] at h₁
          calc
            p.ofLp x * p.ofLp y * (c x - c y) ^ 2 ≤
                (p.ofLp x - p.ofLp y) ^ 2 / T ^ 2 := h₁
            _ ≤ (φ.ofLp x - φ.ofLp y) ^ 2 / T ^ 2 := by
              exact div_le_div_of_nonneg_right h₂
                (le_of_lt (sq_pos_of_pos hTpos))
        · have hpy0 : p.ofLp y = 0 := le_antisymm (le_of_not_gt hpy) (hp y)
          simp [hpy0]
          positivity
      · have hpx0 : p.ofLp x = 0 := le_antisymm (le_of_not_gt hpx) (hp x)
        simp [hpx0]
        positivity
    · simp [hxy]
  have hquad :
      lam * ‖u‖ ^ 2 - dirichletEnergy G d φ / T ^ 2 ≤
        ⟪Matrix.toEuclideanLin (adjacencyMatrix G) u, u⟫_ℝ := by
    apply cutoff_quadratic_lower_bound hreg hTpos
      (fun x => p.ofLp x) c u φ hu hp hres hcut
  have hpo : p.ofLp o = 1 := by
    dsimp [p]
    rw [positivePart_coord, hφo]
    norm_num
  have hpw : p.ofLp w = 0 := by
    dsimp [p]
    rw [positivePart_coord]
    exact max_eq_right hφw
  have hco : c o = 1 := by
    dsimp [c]
    simp [hpo, cutoffScalar, Real.log_one]
  have huo : u.ofLp o = 1 := by
    rw [hu, hpo, hco]
    norm_num
  have huw : u.ofLp w = 0 := by
    rw [hu, hpw]
    ring
  have huneg (x : V) : 0 ≤ u.ofLp x := by
    rw [hu]
    exact mul_nonneg (hp x) (hc (p.ofLp x))
  have hwo : G.Adj w o := G.symm.symm o w how
  have hsum :
      (if G.Adj w o then u.ofLp o else 0) ≤
        ∑ y : V, if G.Adj w y then u.ofLp y else 0 := by
    have hsum0 : u.ofLp o ≤
        ∑ y : V, if G.Adj w y then u.ofLp y else 0 := by
      have hs := Finset.single_le_sum (s := (Finset.univ : Finset V))
        (f := fun y : V => if G.Adj w y then u.ofLp y else 0)
        (fun y hy => by
          by_cases hwy : G.Adj w y
          · simp [hwy, huneg y]
          · simp [hwy])
        (a := o) (by simp)
      calc
        u.ofLp o = (if G.Adj w o then u.ofLp o else 0) := by rw [if_pos hwo]
        _ ≤ _ := hs
    calc
      (if G.Adj w o then u.ofLp o else 0) = u.ofLp o := by rw [if_pos hwo]
      _ ≤ _ := hsum0
  have hAu : 1 ≤
      (Matrix.toEuclideanLin (adjacencyMatrix G) u).ofLp w := by
    rw [adjacency_apply_coord]
    simpa [hwo, huo] using hsum
  have hF : supportedOn F u := by
    intro x hx
    have hxnot : ¬ Real.exp (-T) < p.ofLp x := by
      simpa [F] using hx
    have hple : p.ofLp x ≤ Real.exp (-T) := le_of_not_gt hxnot
    by_cases hpx : 0 < p.ofLp x
    · have hlog : Real.log (p.ofLp x) ≤ Real.log (Real.exp (-T)) :=
      Real.log_le_log hpx hple
      have harg : 1 + Real.log (p.ofLp x) / T ≤ 0 := by
        rw [Real.log_exp] at hlog
        have hdiv : Real.log (p.ofLp x) / T ≤ -1 :=
          (div_le_iff₀ hTpos).2 (by linarith)
        linarith
      rw [hu]
      dsimp [c]
      simp [cutoffScalar, hpx, max_eq_left harg]
    · have hpx0 : p.ofLp x = 0 := le_antisymm (le_of_not_gt hpx) (hp x)
      rw [hu]
      simp [hpx0]
  have hp_norm : ‖p‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
    rw [norm_sq_eq_sum_coord, norm_sq_eq_sum_coord]
    apply Finset.sum_le_sum
    intro x hx
    rw [positivePart_coord]
    by_cases h : 0 ≤ φ.ofLp x
    · rw [max_eq_left h]
    · have h' : φ.ofLp x ≤ 0 := le_of_not_ge h
      rw [max_eq_right h']
      nlinarith [sq_nonneg (φ.ofLp x)]
  have hterm (x : V) (hx : x ∈ F) :
      (1 : ℝ) ≤ Real.exp (2 * T) * (p.ofLp x) ^ 2 := by
    have hpx : Real.exp (-T) < p.ofLp x := by
      simpa [F] using hx
    have hsq : (Real.exp (-T)) ^ 2 < (p.ofLp x) ^ 2 := by
      apply sq_lt_sq'
      · linarith [Real.exp_pos (-T)]
      · exact hpx
    have hmul := mul_lt_mul_of_pos_left hsq (Real.exp_pos (2 * T))
    have hexp : Real.exp (2 * T) * (Real.exp (-T)) ^ 2 = 1 := by
      calc
        Real.exp (2 * T) * (Real.exp (-T)) ^ 2 =
            (Real.exp (2 * T) * Real.exp (-T)) * Real.exp (-T) := by ring
        _ = Real.exp (2 * T + (-T) + (-T)) := by
          rw [← Real.exp_add, ← Real.exp_add]
        _ = 1 := by ring_nf; rw [Real.exp_zero]
    nlinarith
  have hcardF : (F.card : ℝ) ≤ Real.exp (2 * T) * ‖φ‖ ^ 2 := by
    calc
      (F.card : ℝ) = ∑ x ∈ F, (1 : ℝ) := by
        rw [Finset.card_eq_sum_ones]
        norm_num
      _ ≤ ∑ x ∈ F, Real.exp (2 * T) * (p.ofLp x) ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        exact hterm x hx
      _ ≤ ∑ x : V, Real.exp (2 * T) * (p.ofLp x) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · simp
        · intro x hx hxF
          positivity
      _ = Real.exp (2 * T) * ‖p‖ ^ 2 := by
        rw [norm_sq_eq_sum_coord, ← Finset.mul_sum]
      _ ≤ Real.exp (2 * T) * ‖φ‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hp_norm (by positivity)
  have hFo : o ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hpo]
    exact (Real.exp_lt_one_iff.mpr (by linarith))
  exact ⟨F, u, ⟨o, hFo⟩, hF, huw, hAu, hquad, hcardF⟩

lemma supercritical_of_cutoff_data
    {G : SimpleGraph V} {lam T E B : ℝ}
    [DecidableRel G.Adj]
    (hlam : 0 < lam) (hTpos : 0 < T) (hT : lam * E < T ^ 2)
    (F : Finset V) (u : EuclideanSpace ℝ V) (w : V)
    (hF : supportedOn F u)
    (huw : u.ofLp w = 0)
    (hAu : 1 ≤ (Matrix.toEuclideanLin (adjacencyMatrix G) u).ofLp w)
    (hquad : lam * ‖u‖ ^ 2 - E / T ^ 2 ≤
      ⟪Matrix.toEuclideanLin (adjacencyMatrix G) u, u⟫_ℝ)
    (hcard : (F.card : ℝ) ≤ Real.exp (2 * T) * B) :
    ∃ F' : Finset V, F'.Nonempty ∧ IsSupercritical G lam F' ∧
      (F'.card : ℝ) ≤ 1 + Real.exp (2 * T) * B := by
  classical
  let A := Matrix.toEuclideanLin (adjacencyMatrix G)
  let e : EuclideanSpace ℝ V := EuclideanSpace.basisFun V ℝ w
  let h : ℝ := (A u).ofLp w
  let c : ℝ := h / lam
  let v : EuclideanSpace ℝ V := u + c • e
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hecoord : e.ofLp w = 1 := by
    dsimp [e]
    simp [EuclideanSpace.basisFun_apply]
  have hnorme : ‖e‖ ^ 2 = 1 := by
    dsimp [e]
    have hnorm := (EuclideanSpace.basisFun V ℝ).orthonormal.norm_eq_one w
    nlinarith [hnorm]
  have hue : ⟪u, e⟫_ℝ = 0 := by
    rw [inner_basis]
    exact huw
  have hAe : ⟪A e, e⟫_ℝ = 0 := by
    dsimp [A, e]
    rw [adjacency_inner_expand]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases h : G.Adj w x
    · have hne : x ≠ w := by
        intro hxeq
        rw [hxeq] at h
        exact G.loopless.irrefl w h
      simp [hne]
    · apply Finset.sum_eq_zero
      intro y hy
      by_cases hxy : G.Adj x y
      · by_cases hyw : y = w
        · subst y
          exfalso
          exact h (G.symm.symm x w hxy)
        · simp [hxy, hyw]
      · simp [hxy]
  have hcross : ⟪A u, e⟫_ℝ = h := by
    dsimp [h]
    rw [inner_basis]
  have hcross' : ⟪A e, u⟫_ℝ = h := by
    have hsym : A.IsSymmetric :=
      (Matrix.isSymmetric_toEuclideanLin_iff).2 (adjacencyMatrix_isHermitian G)
    calc
      ⟪A e, u⟫_ℝ = ⟪e, A u⟫_ℝ := hsym _ _
      _ = ⟪A u, e⟫_ℝ := real_inner_comm _ _
      _ = h := hcross
  have hvnorm : ‖v‖ ^ 2 = ‖u‖ ^ 2 + c ^ 2 := by
    dsimp [v]
    rw [norm_add_sq_real, real_inner_smul_right, hue,
      norm_smul_sq_real, hnorme]
    ring
  have hvquad : ⟪A v, v⟫_ℝ =
      ⟪A u, u⟫_ℝ + 2 * c * h := by
    dsimp [v]
    rw [map_add, map_smul]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hcross, hcross', hAe]
    ring
  have hpositive : lam * ‖v‖ ^ 2 < ⟪A v, v⟫_ℝ := by
    rw [hvnorm, hvquad]
    have hhnonneg : 0 ≤ h := by
      dsimp [h]
      exact le_trans (by norm_num) hAu
    have hT2 : 0 < T ^ 2 := sq_pos_of_pos hTpos
    have hterm0 : E / T ^ 2 < 1 / lam := by
      apply (div_lt_div_iff₀ hT2 hlam).2
      nlinarith [hT]
    have hhsq : 1 ≤ h ^ 2 := by
      nlinarith [sq_nonneg (h - 1)]
    have hterm : E / T ^ 2 < h ^ 2 / lam := by
      exact hterm0.trans_le (by
        gcongr)
    have hcrossc : 2 * c * h = 2 * h ^ 2 / lam := by
      dsimp [c]
      field_simp [hlamne]
    have hnormc : lam * c ^ 2 = h ^ 2 / lam := by
      dsimp [c]
      field_simp [hlamne]
    rw [mul_add, hnormc, hcrossc]
    have hbase : lam * ‖u‖ ^ 2 - h ^ 2 / lam < ⟪A u, u⟫_ℝ := by
      exact lt_of_lt_of_le (sub_lt_sub_left hterm _) hquad
    calc
      lam * ‖u‖ ^ 2 + h ^ 2 / lam =
          (lam * ‖u‖ ^ 2 - h ^ 2 / lam) + 2 * (h ^ 2 / lam) := by ring
      _ < ⟪A u, u⟫_ℝ + 2 * (h ^ 2 / lam) := by
        simpa [add_comm] using add_lt_add_right hbase (2 * (h ^ 2 / lam))
      _ = ⟪A u, u⟫_ℝ + 2 * h ^ 2 / lam := by ring
  refine ⟨insert w F, ?_, ?_, ?_⟩
  · exact ⟨w, Finset.mem_insert_self w F⟩
  · refine ⟨v, ?_, hpositive⟩
    intro x hx
    have hxw : x ≠ w := by
      intro hxeq
      apply hx
      simp [hxeq]
    have hxF : x ∉ F := by
      intro hxf
      apply hx
      simp [hxf]
    dsimp [v]
    change u.ofLp x + c * e.ofLp x = 0
    have hu0 := hF x hxF
    have he0 : e.ofLp x = 0 := by
      dsimp [e]
      simp [EuclideanSpace.basisFun_apply, hxw]
    simp [hu0, he0]
  · have hnat := Finset.card_insert_le w F
    have hreal : ((insert w F).card : ℝ) ≤ (F.card : ℝ) + 1 := by
      exact_mod_cast hnat
    calc
      ((insert w F).card : ℝ) ≤ (F.card : ℝ) + 1 := hreal
      _ ≤ Real.exp (2 * T) * B + 1 := by
        simpa [add_comm] using add_le_add_right hcard 1
      _ = 1 + Real.exp (2 * T) * B := by ring

lemma lemma_2_3
    (G : SimpleGraph V) (d : ℕ) (lam T : ℝ)
    (hconn : G.Connected) (hreg : IsRegularFinite G d)
    (hvt : IsVertexTransitive G)
    (hlam_pos : 0 < lam)
    (o w : V) (φ : EuclideanSpace ℝ V)
    (how : G.Adj o w)
    (hφeig : Matrix.toEuclideanLin (adjacencyMatrix G) φ = lam • φ)
    (hφo : φ.ofLp o = 1) (hφw : φ.ofLp w ≤ 0)
    (hTpos : 0 < T)
    (hT : lam * dirichletEnergy G d φ < T ^ 2) :
    ∃ F : Finset V, F.Nonempty ∧ IsSupercritical G lam F ∧
      (F.card : ℝ) ≤ 1 + Real.exp (2 * T) * ‖φ‖ ^ 2 := by
  classical
  obtain ⟨F, u, hFne, hF, huw, hAu, hquad, hcard⟩ :=
    cutoff_data_ready G d lam T hconn hreg hvt hlam_pos o w φ how hφeig
      hφo hφw hTpos hT
  obtain ⟨F', hF'ne, hF'super, hF'card⟩ :=
    supercritical_of_cutoff_data hlam_pos hTpos hT F u w hF huw hAu hquad hcard
  exact ⟨F', hF'ne, hF'super, by linarith⟩

end TheoremOnePointOne
