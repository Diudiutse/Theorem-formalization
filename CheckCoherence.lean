import MainTheoremSpectral

set_option autoImplicit false

namespace MainTheorem

open scoped InnerProductSpace BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma norm_sub_le_walk'
    {E : Type*} [NormedAddCommGroup E]
    {G : SimpleGraph V} (Φ : V → E) (B : ℝ)
    (hstep : ∀ {u v : V}, G.Adj u v → ‖Φ u - Φ v‖ ≤ B)
    {u v : V} (p : G.Walk u v) :
    ‖Φ v - Φ u‖ ≤ (p.length : ℝ) * B := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have hs : ‖Φ u - Φ v‖ ≤ B := by
      simpa [norm_sub_rev] using hstep h
    have hsrev : ‖Φ v - Φ u‖ ≤ B := by
      simpa [norm_sub_rev] using hs
    have htri : ‖Φ w - Φ u‖ ≤ ‖Φ w - Φ v‖ + ‖Φ v - Φ u‖ := by
      calc
        ‖Φ w - Φ u‖ = ‖(Φ w - Φ v) + (Φ v - Φ u)‖ := by
          congr 1
          abel
        _ ≤ ‖Φ w - Φ v‖ + ‖Φ v - Φ u‖ := norm_add_le _ _
    have hlen : ((p.length + 1 : ℕ) : ℝ) * B =
        (p.length : ℝ) * B + B := by push_cast; ring
    rw [SimpleGraph.Walk.length_cons, hlen]
    exact htri.trans (add_le_add ih hsrev)

lemma coherence_ball_bound
    {G : SimpleGraph V} (hconn : G.Connected)
    (Φ : V → EuclideanSpace ℝ V) (α γ r : ℝ) (s : ℕ) (o : V)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hr : 0 ≤ r)
    (hαr : α * r = 1)
    (hnorm : ∀ x, ‖Φ x‖ ^ 2 = α)
    (hframe : ∀ x, ∑ z : V, (⟪Φ x, Φ z⟫_ℝ) ^ 2 = α)
    (hedge : ∀ {x y}, G.Adj x y → ‖Φ x - Φ y‖ ^ 2 ≤ 2 * γ * α)
    (hs : γ * (s : ℝ) ^ 2 ≤ 1 / 2) :
    (Set.ncard {x : V | G.dist x o ≤ s} : ℝ) ≤ 4 * r := by
  let B : ℝ := Real.sqrt (2 * γ * α)
  have hBsq : B ^ 2 = 2 * γ * α := by
    dsimp [B]
    exact Real.sq_sqrt (by positivity)
  have hB : 0 ≤ B := by dsimp [B]; exact Real.sqrt_nonneg _
  have hstep : ∀ {x y}, G.Adj x y → ‖Φ x - Φ y‖ ≤ B := by
    intro x y hxy
    apply (sq_le_sq₀ (norm_nonneg _) hB).mp
    rw [hBsq]
    exact hedge hxy
  let S : Finset V := (Set.toFinite {x : V | G.dist x o ≤ s}).toFinset
  have hS_mem : ∀ x ∈ S, G.dist x o ≤ s := by
    intro x hx
    simpa [S] using hx
  have hinner : ∀ x ∈ S, (α / 2 : ℝ) ≤ ⟪Φ o, Φ x⟫_ℝ := by
    intro x hx
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x o
    have hdist : (G.dist x o : ℝ) ≤ s := by
      exact_mod_cast hS_mem x hx
    have hbound : ‖Φ o - Φ x‖ ≤ (s : ℝ) * B := by
      have h₁ := norm_sub_le_walk' Φ B hstep p
      rw [hp] at h₁
      exact h₁.trans (mul_le_mul_of_nonneg_right hdist hB)
    have hsq : ‖Φ o - Φ x‖ ^ 2 ≤ ((s : ℝ) * B) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbound
    have hmul : γ * (s : ℝ) ^ 2 * α ≤ α / 2 := by
      have := mul_le_mul_of_nonneg_right hs (le_of_lt hα)
      nlinarith
    have hsq' : ‖Φ o - Φ x‖ ^ 2 ≤ α := by
      have hsquare : ((s : ℝ) * B) ^ 2 =
          2 * γ * α * (s : ℝ) ^ 2 := by
        rw [mul_pow, hBsq]
        ring
      rw [hsquare] at hsq
      nlinarith [hsq, hmul]
    rw [norm_sub_sq_real, hnorm o, hnorm x] at hsq'
    nlinarith
  have hlow : (S.card : ℝ) * (α ^ 2 / 4) ≤
      (Finset.sum S (fun x => (⟪Φ o, Φ x⟫_ℝ) ^ 2)) := by
    calc
      (S.card : ℝ) * (α ^ 2 / 4) = (∑ _x ∈ S, (α ^ 2 / 4)) := by simp
      _ ≤ (∑ x ∈ S, (⟪Φ o, Φ x⟫_ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro x hx
        have hi := hinner x hx
        nlinarith [sq_nonneg (⟪Φ o, Φ x⟫_ℝ - α / 2)]
  have hupper : (∑ x ∈ S, (⟪Φ o, Φ x⟫_ℝ) ^ 2) ≤ α := by
    have hsub : S ⊆ Finset.univ := Finset.subset_univ S
    have hnonneg : ∀ x ∈ (Finset.univ : Finset V), x ∉ S →
        0 ≤ (⟪Φ o, Φ x⟫_ℝ) ^ 2 := by
      intro x hx hxs
      exact sq_nonneg _
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg).trans_eq (hframe o)
  have hcard : (S.card : ℝ) ≤ 4 * r := by
    have hdiv : (S.card : ℝ) ≤ 4 / α := by
      apply (le_div_iff₀ hα).2
      nlinarith [hlow, hupper]
    calc
      (S.card : ℝ) ≤ 4 / α := hdiv
      _ = 4 * r := by
        field_simp
        nlinarith [hαr]
  have hScard : Set.ncard {x : V | G.dist x o ≤ s} = S.card := by
    simp [S, Set.ncard_eq_toFinset_card']
  calc
    (Set.ncard {x : V | G.dist x o ≤ s} : ℝ) = (S.card : ℝ) := by
      rw [hScard]
    _ ≤ 4 * r := hcard

end MainTheorem
