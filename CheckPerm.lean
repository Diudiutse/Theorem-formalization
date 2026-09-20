import MainTheoremSpectral
open scoped InnerProductSpace
#check LinearIsometryEquiv.piLpCongrLeft
#check LinearIsometryEquiv.piLpCongrRight
#check LinearIsometryEquiv.piLpCongrLeft_apply
#check EuclideanSpace.single
#check EuclideanSpace.single_apply
#check Matrix.toEuclideanLin
#check Matrix.toEuclideanLin_apply
#check Matrix.toLin'_apply
#check Matrix.toLin'_mul
#check LinearMap.toMatrix_toLin
#check Fintype.sum_equiv
#check Equiv.piCongrLeft'

namespace MainTheorem
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def permIso (e : V ≃ V) :
    EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V :=
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

end MainTheorem
