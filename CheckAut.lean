import MainTheorem

set_option autoImplicit false

namespace MainTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

structure GraphAut (G : SimpleGraph V) where
  toEquiv : V ≃ V
  map_adj : ∀ x y : V, G.Adj (toEquiv x) (toEquiv y) ↔ G.Adj x y

namespace GraphAut

instance (G : SimpleGraph V) : CoeFun (GraphAut G) (fun _ => V → V) :=
  ⟨fun e => e.toEquiv⟩

@[ext]
lemma ext {e f : GraphAut G} (h : ∀ x, e x = f x) : e = f := by
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
  ⟨fun e f => ⟨e.toEquiv.trans f.toEquiv, by
    intro x y
    rw [Equiv.trans_apply, Equiv.trans_apply]
    rw [e.map_adj, f.map_adj]⟩⟩

instance (G : SimpleGraph V) : Inv (GraphAut G) :=
  ⟨fun e => ⟨e.toEquiv.symm, by
    intro x y
    constructor
    · intro h
      have := e.map_adj (e.toEquiv.symm x) (e.toEquiv.symm y)
      rw [e.toEquiv.apply_symm_apply, e.toEquiv.apply_symm_apply] at this
      exact this.mp h
    · intro h
      have := e.map_adj (e.toEquiv.symm x) (e.toEquiv.symm y)
      rw [e.toEquiv.apply_symm_apply, e.toEquiv.apply_symm_apply] at this
      exact this.mpr h⟩⟩

instance (G : SimpleGraph V) : Group (GraphAut G) where
  mul_assoc a b c := by ext x; simp [Mul.mul]
  one_mul a := by ext x; simp [Mul.mul]
  mul_one a := by ext x; simp [Mul.mul]
  inv_mul_cancel a := by ext x; simp [Mul.mul]

instance (G : SimpleGraph V) : Fintype (GraphAut G) :=
  Fintype.ofInjective (fun e => e.toEquiv) (by intro e f h; cases e; cases f; simp_all)

instance (G : SimpleGraph V) : MulAction (GraphAut G) V where
  smul e x := e x
  one_smul x := by simp
  mul_smul e f x := by simp [Mul.mul]

lemma smul_def (e : GraphAut G) (x : V) : e • x = e x := rfl

end GraphAut

def IsVertexTransitive' (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ e : GraphAut G, e • u = v

lemma vertexTransitive'_of_original {G : SimpleGraph V}
    (h : IsVertexTransitive G) : IsVertexTransitive' G := by
  intro u v
  obtain ⟨e, he, huv⟩ := h u v
  exact ⟨⟨e, he⟩, huv⟩

lemma eval_surjective (G : SimpleGraph V) (h : IsVertexTransitive' G) (b : V) :
    Function.Surjective (fun e : GraphAut G => e • b) := by
  intro x
  obtain ⟨e, he⟩ := h b x
  exact ⟨e, he⟩

end MainTheorem
