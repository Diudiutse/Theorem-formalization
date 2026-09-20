import Theorem11Spectral
set_option autoImplicit false
namespace TheoremOnePointOne
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
#check @SimpleGraph.neighborFinset
lemma test_neighbor
    {G : SimpleGraph V} {d : ℕ}
    (hreg : IsRegularFinite G d) (o : V)
    [Fintype (G.neighborSet o)] :
    (@SimpleGraph.neighborFinset V G o inferInstance).card = d := by
  classical
  have hsource : @SimpleGraph.degree V G o (finiteNeighbor G o) =
      @Fintype.card (G.neighborSet o) (finiteNeighbor G o) := by
    letI : Fintype (G.neighborSet o) := finiteNeighbor G o
    exact (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := o)).symm
  have hcard' : @Fintype.card (G.neighborSet o) (finiteNeighbor G o) =
      @Fintype.card (G.neighborSet o) inferInstance := by
    exact @Fintype.card_congr (G.neighborSet o) (G.neighborSet o)
      (finiteNeighbor G o) inferInstance (Equiv.refl _)
  have hdeg : G.degree o = d := by
    calc
      G.degree o = @Fintype.card (G.neighborSet o) inferInstance :=
        (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := o)).symm
      _ = @Fintype.card (G.neighborSet o) (finiteNeighbor G o) := hcard'.symm
      _ = @SimpleGraph.degree V G o (finiteNeighbor G o) := hsource.symm
      _ = d := hreg o
  rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
end TheoremOnePointOne
