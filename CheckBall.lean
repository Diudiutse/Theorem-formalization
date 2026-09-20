import CheckCoherenceFull

set_option autoImplicit false

namespace TheoremOnePointOne

open scoped InnerProductSpace BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma ball_card_ge_of_path
    {G : SimpleGraph V} {o v : V} (p : G.Walk o v)
    (hp : p.IsPath) (R : ℕ) (hR : R ≤ p.length) :
    (R + 1 : ℝ) ≤ (Set.ncard {x : V | G.dist x o ≤ R} : ℝ) := by
  classical
  let S : Finset V := (Finset.range (R + 1)).image p.getVert
  have hinj : Set.InjOn p.getVert
      (↑(Finset.range (R + 1)) : Set ℕ) := by
    intro i hi j hj hij
    have hiR : i < R + 1 := by simpa using hi
    have hjR : j < R + 1 := by simpa using hj
    have hi_lt : i < p.support.length := by
      rw [p.length_support]
      omega
    have hj_lt : j < p.support.length := by
      rw [p.length_support]
      omega
    have hi_eq : p.getVert i = p.support.get ⟨i, hi_lt⟩ := by
      simpa [Function.comp_def] using
        congrFun p.getVert_comp_val_eq_get_support ⟨i, hi_lt⟩
    have hj_eq : p.getVert j = p.support.get ⟨j, hj_lt⟩ := by
      simpa [Function.comp_def] using
        congrFun p.getVert_comp_val_eq_get_support ⟨j, hj_lt⟩
    have hsupp : p.support.get ⟨i, hi_lt⟩ =
        p.support.get ⟨j, hj_lt⟩ := hi_eq.symm.trans (hij.trans hj_eq)
    have hfin : (⟨i, hi_lt⟩ : Fin p.support.length) =
        ⟨j, hj_lt⟩ := (p.isPath_iff_injective_get_support.mp hp) hsupp
    exact Fin.ext_iff.mp hfin
  have hScard : S.card = R + 1 := by
    dsimp [S]
    simpa using (Finset.card_image_iff.mpr hinj)
  have hsub : (↑S : Set V) ⊆ {x : V | G.dist x o ≤ R} := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hiR : i < R + 1 := Finset.mem_range.mp hi
    have hi_le : i ≤ p.length := by omega
    have hdist : G.dist o (p.getVert i) ≤ i := by
      have htake := G.dist_le (p.take i)
      have hlen : (p.take i).length = i := by
        rw [SimpleGraph.Walk.take_length]
        exact Nat.min_eq_left hi_le
      simpa [hlen] using htake
    change G.dist (p.getVert i) o ≤ R
    rw [G.dist_comm]
    exact le_trans hdist (Nat.cast_le.mpr (Nat.le_of_lt_succ hiR))
  have hcard : (S.card : ℝ) ≤
      (Set.ncard {x : V | G.dist x o ≤ R} : ℝ) := by
    have hcard' := Set.ncard_le_ncard hsub
    simpa [Set.ncard_coe_finset] using hcard'
  rw [hScard] at hcard
  simpa [Nat.cast_add, Nat.cast_one] using hcard

end TheoremOnePointOne
