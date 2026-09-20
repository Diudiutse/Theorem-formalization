import Theorem11Spectral
open scoped InnerProductSpace
namespace TheoremOnePointOne
open ContinuousLinearMap
#check LinearMap.IsIdempotentElem.isProj_range
#check LinearMap.IsProj.trace
#check LinearMap.IsProj
#check ContinuousLinearMap.range_toLinearMap
variable {V : Type*} [Fintype V] [DecidableEq V]
example (U : Submodule ℝ (EuclideanSpace ℝ V)) :
    LinearMap.trace ℝ (EuclideanSpace ℝ V) U.starProjection.toLinearMap =
      (Module.finrank ℝ U : ℝ) := by
  have hp := LinearMap.IsIdempotentElem.isProj_range
    U.starProjection.toLinearMap U.isIdempotentElem_starProjection.toLinearMap
  have hrange : LinearMap.range U.starProjection.toLinearMap = U := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact U.starProjection_apply_mem y
    · intro hx
      refine ⟨x, ?_⟩
      exact Submodule.starProjection_eq_self_iff.mpr hx
  rw [hrange] at hp
  exact hp.trace
end TheoremOnePointOne
