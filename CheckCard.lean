import Theorem11Spectral
set_option autoImplicit false
namespace TheoremOnePointOne
variable {V : Type*} [Fintype V] [DecidableEq V]
lemma card_ge_three
    (G : SimpleGraph V) (d : ℕ) (hd : 2 ≤ d)
    (hG : IsMainGraph G d) :
    (3 : ℝ) ≤ Fintype.card V := by
  rcases hG with ⟨hconn, hreg, hvt⟩
  letI : G.LocallyFinite := finiteNeighbor G
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨v⟩ := hconn.nonempty
  have hdeg : G.degree v = d := hreg v
  have hlt : G.degree v < Fintype.card V := G.degree_lt_card_verts v
  rw [hdeg] at hlt
  have hn : 3 ≤ Fintype.card V := by omega
  exact_mod_cast hn
end TheoremOnePointOne
