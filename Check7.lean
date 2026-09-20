import Theorem11Spectral

set_option autoImplicit false

namespace TheoremOnePointOne

open scoped BigOperators InnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma check_conjugacy (G : SimpleGraph V) :
    let A := adjacencyMatrix G
    let T := Matrix.toEuclideanLin A
    let e := WithLp.linearEquiv 2 ℝ (V → ℝ)
    e.toLinearMap.comp T = (adjacencyOperator G).comp e.toLinearMap := by
  classical
  dsimp
  ext x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [Matrix.toEuclideanLin_apply]
  rfl

lemma check_eigenspace_map (G : SimpleGraph V) (μ : ℝ) :
    let A := adjacencyMatrix G
    let T := Matrix.toEuclideanLin A
    let e := WithLp.linearEquiv 2 ℝ (V → ℝ)
    Submodule.map e.toLinearMap (Module.End.eigenspace T μ) =
      Module.End.eigenspace (adjacencyOperator G) μ := by
  classical
  dsimp
  let e := WithLp.linearEquiv 2 ℝ (V → ℝ)
  let T := Matrix.toEuclideanLin (adjacencyMatrix G)
  have hconj : e.toLinearMap.comp T =
      (adjacencyOperator G).comp e.toLinearMap := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [Matrix.toEuclideanLin_apply]
    rfl
  apply le_antisymm
  · intro y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← hxy]
    have hconj_x := congrArg (fun f => f x) hconj
    calc
      adjacencyOperator G (e x) = e (T x) := hconj_x.symm
      _ = e (μ • x) := by rw [hx]
      _ = μ • e x := e.map_smul μ x
  · intro y hy
    rw [Submodule.mem_map]
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    have hconj_y := congrArg (fun f => f (e.symm y)) hconj
    calc
      T (e.symm y) = e.symm (adjacencyOperator G y) := by
        apply e.injective
        simpa [e] using hconj_y
      _ = e.symm (μ • y) := by rw [hy]
      _ = μ • e.symm y := e.symm.map_smul μ y

lemma check_eigenspace_finrank (G : SimpleGraph V) (μ : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace (Matrix.toEuclideanLin (adjacencyMatrix G)) μ) =
      adjacencyEigenvalueMultiplicity G μ := by
  classical
  let e := WithLp.linearEquiv 2 ℝ (V → ℝ)
  let T := Matrix.toEuclideanLin (adjacencyMatrix G)
  have hmap : Submodule.map e.toLinearMap (Module.End.eigenspace T μ) =
      Module.End.eigenspace (adjacencyOperator G) μ := by
    simpa [e, T] using check_eigenspace_map G μ
  have heq : Module.finrank ℝ (Module.End.eigenspace T μ) =
      Module.finrank ℝ (Module.End.eigenspace (adjacencyOperator G) μ) := by
    rw [← hmap]
    exact (LinearEquiv.submoduleMap e (Module.End.eigenspace T μ)).finrank_eq
  rw [heq]
  unfold adjacencyEigenvalueMultiplicity
  have hk : Module.End.eigenspace (adjacencyOperator G) μ =
      LinearMap.ker (adjacencyOperator G -
        μ • (LinearMap.id : (V → ℝ) →ₗ[ℝ] (V → ℝ))) := by
    ext x
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · intro h
      rw [h]
      exact sub_self _
    · intro h
      exact sub_eq_zero.mp h
  rw [hk]

end TheoremOnePointOne
