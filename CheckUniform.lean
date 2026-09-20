import MainTheoremSpectral

set_option autoImplicit false

namespace MainTheorem

open scoped InnerProductSpace BigOperators
open ContinuousLinearMap

variable {V : Type*} [Fintype V] [DecidableEq V]

structure GraphAut (G : SimpleGraph V) where
  toEquiv : V ≃ V
  map_adj : ∀ x y : V, G.Adj (toEquiv x) (toEquiv y) ↔ G.Adj x y

namespace GraphAut

instance (G : SimpleGraph V) : CoeFun (GraphAut G) (fun _ => V → V) :=
  ⟨fun e => e.toEquiv⟩

omit [Fintype V] [DecidableEq V] in
@[ext]
lemma ext {G : SimpleGraph V} {e f : GraphAut G} (h : ∀ x, e x = f x) : e = f := by
  cases e with
  | mk e he =>
    cases f with
    | mk f hf =>
      simp only at h
      have : e = f := Equiv.ext h
      subst this
      rfl

instance (G : SimpleGraph V) : One (GraphAut G) :=
  ⟨⟨Equiv.refl V, by simp⟩⟩

instance (G : SimpleGraph V) : Mul (GraphAut G) :=
  ⟨fun e f => ⟨f.toEquiv.trans e.toEquiv, by
    intro x y
    rw [Equiv.trans_apply, Equiv.trans_apply]
    rw [e.map_adj, f.map_adj]⟩⟩

instance (G : SimpleGraph V) : Inv (GraphAut G) :=
  ⟨fun e => ⟨e.toEquiv.symm, by
    intro x y
    constructor
    · intro h
      have he := e.map_adj (e.toEquiv.symm x) (e.toEquiv.symm y)
      rw [e.toEquiv.apply_symm_apply, e.toEquiv.apply_symm_apply] at he
      exact he.mpr h
    · intro h
      have he := e.map_adj (e.toEquiv.symm x) (e.toEquiv.symm y)
      rw [e.toEquiv.apply_symm_apply, e.toEquiv.apply_symm_apply] at he
      exact he.mp h⟩⟩

instance (G : SimpleGraph V) : Group (GraphAut G) where
  mul_assoc a b c := by
    apply GraphAut.ext
    intro x
    rfl
  one_mul a := by
    apply GraphAut.ext
    intro x
    rfl
  mul_one a := by
    apply GraphAut.ext
    intro x
    rfl
  inv_mul_cancel a := by
    apply GraphAut.ext
    intro x
    change a.toEquiv.symm (a.toEquiv x) = x
    simp

noncomputable instance (G : SimpleGraph V) : Fintype (GraphAut G) :=
  Fintype.ofInjective (fun e => e.toEquiv) (by intro e f h; cases e; cases f; simp_all)

instance (G : SimpleGraph V) : MulAction (GraphAut G) V where
  smul e x := e x
  one_smul x := rfl
  mul_smul e f x := by rfl

omit [Fintype V] [DecidableEq V] in
lemma smul_def {G : SimpleGraph V} (e : GraphAut G) (x : V) : e • x = e x := rfl

end GraphAut

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
    simp [hy]
  · have hy : y ≠ e x := by
      intro hy
      apply h
      simp [hy]
    simp [h, hy]

lemma adjacency_perm_commute (G : SimpleGraph V) (e : GraphAut G)
    (v : EuclideanSpace ℝ V) :
    permIso e.toEquiv (Matrix.toEuclideanLin (adjacencyMatrix G) v) =
      Matrix.toEuclideanLin (adjacencyMatrix G) (permIso e.toEquiv v) := by
  classical
  ext y
  change (permIso e.toEquiv
      (Matrix.toEuclideanLin (adjacencyMatrix G) v)).ofLp y = _
  dsimp [permIso]
  simp only [Equiv.piCongrLeft'_apply]
  simp only [Matrix.mulVec]
  simp [adjacencyMatrix, SimpleGraph.adjMatrix_apply]
  rw [dotProduct, dotProduct]
  apply Fintype.sum_equiv e.toEquiv
  intro j
  have hadj : G.Adj y (e.toEquiv j) ↔ G.Adj (e.toEquiv.symm y) j := by
    simpa using e.map_adj (e.toEquiv.symm y) j
  simp only [Equiv.piCongrLeft'_apply]
  rw [e.toEquiv.symm_apply_apply]
  change (if G.Adj (e.toEquiv.symm y) j then 1 else 0) * v.ofLp j =
    (if G.Adj y (e.toEquiv j) then 1 else 0) * v.ofLp j
  by_cases h : G.Adj (e.toEquiv.symm y) j
  · rw [if_pos h, if_pos (hadj.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hadj.mp h'))]

def IsVertexTransitive' (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ e : GraphAut G, e.toEquiv u = v

omit [Fintype V] [DecidableEq V] in
lemma vertexTransitive'_of_original {G : SimpleGraph V}
    (h : IsVertexTransitive G) : IsVertexTransitive' G := by
  intro u v
  obtain ⟨e, he, huv⟩ := h u v
  exact ⟨⟨e, he⟩, huv⟩

lemma spectral_projector_uniform_norm
    (G : SimpleGraph V) (lam : ℝ)
    (hvt : IsVertexTransitive' G)
    (hUpos : 0 < Module.finrank ℝ
      (Module.End.eigenspace (Matrix.toEuclideanLin (adjacencyMatrix G)) lam)) :
    let T := Matrix.toEuclideanLin (adjacencyMatrix G)
    let U := Module.End.eigenspace T lam
    let P := U.starProjection
    let b := EuclideanSpace.basisFun V ℝ
    ∃ α : ℝ, 0 < α ∧
      (∀ x : V, ‖P (b x)‖ ^ 2 = α) ∧
      α = (Module.finrank ℝ U : ℝ) / (Fintype.card V : ℝ) := by
  let T := Matrix.toEuclideanLin (adjacencyMatrix G)
  let U := Module.End.eigenspace T lam
  let P := U.starProjection
  let b := EuclideanSpace.basisFun V ℝ
  have hUpos' : 0 < Module.finrank ℝ U := by simpa [U, T] using hUpos
  have hV : Nonempty V := by
    classical
    by_contra hV
    letI : IsEmpty V := not_nonempty_iff.mp hV
    have hz : Module.finrank ℝ U = 0 := by
      exact Module.finrank_zero_of_subsingleton
    omega
  letI : Nonempty V := hV
  have hcard : (0 : ℝ) < Fintype.card V := by positivity
  have hmap_mem : ∀ (e : GraphAut G) (x : EuclideanSpace ℝ V),
      x ∈ U → permIso e.toEquiv x ∈ U := by
    intro e x hx
    apply Module.End.mem_eigenspace_iff.mpr
    have hcomm := adjacency_perm_commute G e x
    rw [← hcomm, Module.End.mem_eigenspace_iff.mp hx, map_smul]
  have hmap_mem_inv : ∀ (e : GraphAut G) (x : EuclideanSpace ℝ V),
      x ∈ U → (permIso e.toEquiv).symm x ∈ U := by
    intro e x hx
    apply Module.End.mem_eigenspace_iff.mpr
    have hcomm := adjacency_perm_commute G e ((permIso e.toEquiv).symm x)
    have hT : Matrix.toEuclideanLin (adjacencyMatrix G) x = lam • x :=
      Module.End.mem_eigenspace_iff.mp hx
    have hinv : T ((permIso e.toEquiv).symm x) =
        (permIso e.toEquiv).symm (T x) := by
      calc
        T ((permIso e.toEquiv).symm x) =
            (permIso e.toEquiv).symm
              (permIso e.toEquiv (T ((permIso e.toEquiv).symm x))) := by simp
        _ = (permIso e.toEquiv).symm
              (T (permIso e.toEquiv ((permIso e.toEquiv).symm x))) := by
          rw [hcomm]
        _ = (permIso e.toEquiv).symm (T x) := by simp
    rw [hinv, hT, map_smul]
  have hUmap (e : GraphAut G) :
      U.map ((permIso e.toEquiv).toLinearIsometry :
        EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V) = U := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hmap_mem e x hx
    · intro y hy
      refine ⟨(permIso e.toEquiv).symm y, hmap_mem_inv e y hy, ?_⟩
      simp
  have hPcomm (e : GraphAut G) (x : EuclideanSpace ℝ V) :
      permIso e.toEquiv (P x) = P (permIso e.toEquiv x) := by
      change (permIso e.toEquiv).toLinearIsometry (U.starProjection x) =
        U.starProjection ((permIso e.toEquiv).toLinearIsometry x)
      have h := (permIso e.toEquiv).toLinearIsometry.map_starProjection' U x
      simpa only [hUmap e] using h
  let q : V → ℝ := fun x => ‖P (b x)‖ ^ 2
  have hq_uniform : ∀ x y : V, q x = q y := by
    intro x y
    obtain ⟨e, he⟩ := hvt x y
    have hsingle : permIso e.toEquiv (b x) = b y := by
      simpa [b, EuclideanSpace.basisFun_apply, he] using permIso_single e.toEquiv x
    dsimp [q]
    rw [← hsingle, ← hPcomm]
    simp
  obtain ⟨o⟩ := (inferInstance : Nonempty V)
  let α : ℝ := q o
  have hqα : ∀ x, q x = α := by
    intro x
    exact (hq_uniform x o).trans rfl
  have htraceP : LinearMap.trace ℝ (EuclideanSpace ℝ V) P.toLinearMap =
      (Module.finrank ℝ U : ℝ) := by
    have hp := LinearMap.IsIdempotentElem.isProj_range
      P.toLinearMap U.isIdempotentElem_starProjection.toLinearMap
    have hrange : LinearMap.range P.toLinearMap = U := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact U.starProjection_apply_mem y
      · intro hx
        refine ⟨x, ?_⟩
        exact Submodule.starProjection_eq_self_iff.mpr hx
    rw [hrange] at hp
    exact hp.trace
  have hinner_norm (x : V) :
      ⟪b x, P (b x)⟫_ℝ = q x := by
    have hmem : P (b x) ∈ U := U.starProjection_apply_mem _
    have hproj := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (K := U) ⟨P (b x), hmem⟩ (b x)
    calc
      ⟪b x, P (b x)⟫_ℝ = ⟪P (b x), b x⟫_ℝ := real_inner_comm _ _
      _ = ⟪P (b x), P (b x)⟫_ℝ := hproj.symm
      _ = ‖P (b x)‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = q x := rfl
  have hsum : (Fintype.card V : ℝ) * α =
      (Module.finrank ℝ U : ℝ) := by
    calc
      (Fintype.card V : ℝ) * α = ∑ x : V, q x := by simp [hqα]
      _ = ∑ x : V, ⟪b x, P (b x)⟫_ℝ := by
        apply Fintype.sum_congr
        intro x
        exact (hinner_norm x).symm
      _ = LinearMap.trace ℝ (EuclideanSpace ℝ V) P.toLinearMap := by
        symm
        exact LinearMap.trace_eq_sum_inner P.toLinearMap b
      _ = (Module.finrank ℝ U : ℝ) := htraceP
  refine ⟨α, ?_, hqα, ?_⟩
  · have : 0 < (Module.finrank ℝ U : ℝ) := by exact_mod_cast hUpos'
    nlinarith
  · have hcardne : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt hcard
    field_simp [hcardne]
    nlinarith [hsum]

end MainTheorem
