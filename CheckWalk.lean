import MainTheoremSpectral

set_option autoImplicit false

namespace MainTheorem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E]

lemma norm_sub_le_walk
    {G : SimpleGraph V} (Φ : V → E) (B : ℝ)
    (hB : 0 ≤ B)
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

end MainTheorem
