import Theorem11Spectral
set_option autoImplicit false
namespace TheoremOnePointOne
open scoped InnerProductSpace BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
structure GraphAut (G : SimpleGraph V) where
  toEquiv : V ≃ V
  map_adj : ∀ x y : V, G.Adj (toEquiv x) (toEquiv y) ↔ G.Adj x y
noncomputable def permIso (e : V ≃ V) : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
lemma permIso_single (e : V ≃ V) (x : V) :
    permIso e (EuclideanSpace.single x 1) = EuclideanSpace.single (e x) 1 := by
  ext y
  change (permIso e (EuclideanSpace.single x 1)).ofLp y = _
  dsimp [permIso]
  simp only [Pi.single_apply]
  by_cases h : e.symm y = x
  · have hy : y = e x := by simpa using congrArg e h
    simp [h, hy]
  · have hy : y ≠ e x := by
      intro hy
      apply h
      simpa [hy]
    simp [h, hy]

#check SimpleGraph.adjMatrix_apply
#check Matrix.mulVec
#check Matrix.mulVec_eq_sum
#check dotProduct
#check Fintype.sum_equiv

lemma adjacency_perm_commute (G : SimpleGraph V) (e : GraphAut G) (v : EuclideanSpace ℝ V) :
    permIso e.toEquiv (Matrix.toEuclideanLin (adjacencyMatrix G) v) =
      Matrix.toEuclideanLin (adjacencyMatrix G) (permIso e.toEquiv v) := by
  ext y
  change (permIso e.toEquiv (Matrix.toEuclideanLin (adjacencyMatrix G) v)).ofLp y = _
  dsimp [permIso]
  simp only [Equiv.piCongrLeft'_apply]
  simp only [Matrix.mulVec]
  simp [adjacencyMatrix, SimpleGraph.adjMatrix_apply]
  rw [dotProduct, dotProduct]
  apply Fintype.sum_equiv e.toEquiv
  intro j
  have hadj : G.Adj y (e.toEquiv j) ↔ G.Adj (e.toEquiv.symm y) j := by
    simpa using e.map_adj (e.toEquiv.symm y) j
  by_cases h : G.Adj (e.toEquiv.symm y) j
  · rw [if_pos h, if_pos (hadj.mpr h)]
    simp
  · rw [if_neg h, if_neg (fun h' => h (hadj.mp h'))]
    simp
end TheoremOnePointOne
