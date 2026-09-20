import Mathlib

/-!
# A formal statement of Theorem 1.1

This file formalizes the objects occurring in Theorem 1.1 of
`vertex_transitive_log_squared_multiplicity.pdf`.

The graph is represented by `SimpleGraph`.  The adjacency operator is the
linear operator induced by the adjacency matrix, and the multiplicity of an
eigenvalue is the finite dimension of its eigenspace.  The analytic and
spectral ingredients are proved in the companion files and assembled in
`theorem_one_one`.
-/

set_option autoImplicit false

namespace TheoremOnePointOne

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph automorphism witness sending one vertex to another. -/
def IsVertexTransitive (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ e : Equiv V V,
    (∀ x y : V, G.Adj (e x) (e y) ↔ G.Adj x y) ∧ e u = v

/-- The graph hypotheses from the statement of Theorem 1.1.

`SimpleGraph` already encodes finiteness-independent simplicity, undirectedness,
and absence of loops; `Fintype V` supplies finiteness. -/
@[reducible]
noncomputable def finiteNeighbor (G : SimpleGraph V) : G.LocallyFinite :=
  by
    classical
    exact fun _ ↦ Subtype.fintype _

noncomputable def finiteDegree (G : SimpleGraph V) (v : V) : ℕ :=
  @SimpleGraph.degree V G v (finiteNeighbor G v)

def IsRegularFinite (G : SimpleGraph V) (d : ℕ) : Prop :=
  @SimpleGraph.IsRegularOfDegree V G (finiteNeighbor G) d

def IsMainGraph (G : SimpleGraph V) (d : ℕ) : Prop :=
  G.Connected ∧ IsRegularFinite G d ∧ IsVertexTransitive G

/-- The real adjacency operator on the space of functions `V → ℝ`. -/
noncomputable def adjacencyMatrix (G : SimpleGraph V) : Matrix V V ℝ :=
  by
    classical
    exact G.adjMatrix ℝ

/-- The real adjacency operator on the space of functions `V → ℝ`. -/
noncomputable def adjacencyOperator (G : SimpleGraph V) :
    (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
  by
    exact Matrix.toLin' (adjacencyMatrix G)

/-- `λ` is an adjacency eigenvalue of `G`. -/
def IsAdjacencyEigenvalue (G : SimpleGraph V) (lam : ℝ) : Prop :=
  ∃ f : V → ℝ, f ≠ 0 ∧ adjacencyOperator G f = lam • f

/-- The multiplicity of an adjacency eigenvalue, as the dimension of its eigenspace. -/
noncomputable def adjacencyEigenvalueMultiplicity
    (G : SimpleGraph V) (lam : ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.ker (adjacencyOperator G - lam • LinearMap.id))

/-- `λ` is the largest adjacency eigenvalue strictly below the degree `d`.

For a connected regular graph this is the usual second adjacency eigenvalue.
This definition avoids depending on a particular ordering API for the finite
multiset of eigenvalues. -/
def IsSecondAdjacencyEigenvalue
    (G : SimpleGraph V) (d lam : ℝ) : Prop :=
  IsAdjacencyEigenvalue G lam ∧ lam < d ∧
    (∀ μ : ℝ, IsAdjacencyEigenvalue G μ → μ ≤ d) ∧
    ∀ μ : ℝ, IsAdjacencyEigenvalue G μ → μ < d → μ ≤ lam

/-- The constant `K_d` from the PDF. -/
noncomputable def K (d : ℕ) : ℝ :=
  8 * (d : ℝ) + 6 + 2 * Real.log (32 * (d : ℝ)) +
    Real.log (4 * ((d + 1 : ℕ) : ℝ))

/-- The explicit constant `C_d` from the PDF. -/
noncomputable def C (d : ℕ) : ℝ :=
  max (4 * (K d) ^ 2)
    (max 8 ((1 + Real.log (2 * (d : ℝ))) ^ 2))

/-- The exact inequality asserted by Theorem 1.1 for a graph and its `λ₂`. -/
def Theorem11Claim (G : SimpleGraph V) (d : ℕ) (lam : ℝ) : Prop :=
  (adjacencyEigenvalueMultiplicity G lam : ℝ) ≤
    C d * (Fintype.card V : ℝ) /
      (1 + Real.log (Fintype.card V : ℝ)) ^ 2

end TheoremOnePointOne
