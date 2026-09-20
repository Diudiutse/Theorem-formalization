# Formalization of the Main Theorem

This repository contains the Lean 4 formalization of the main theorem together with [`paper.tex`](paper.tex). In the paper source, the corresponding result is numbered **Theorem 1.2**; `paper.tex` is the source to use for the mathematical statement.

## Requirements

- Lean `v4.32.2`
- Lake
- Mathlib `v4.32.2`

The required Lean version is recorded in [`lean-toolchain`](lean-toolchain). Mathlib is declared in [`lakefile.lean`](lakefile.lean), so the project can be rebuilt after cloning without copying the local `.lake` directory.

## Build

From the repository root, run:

```powershell
lake update
lake build
```

A successful build checks the Lean proofs with the Lean kernel.

## Main theorem

### Mathematical statement in `paper.tex`

The main theorem, numbered Theorem 1.2 in [`paper.tex`](paper.tex), states that for every integer \(d\geq 2\), there is a finite constant \(C_d\) such that every finite, connected, simple, \(d\)-regular, vertex-transitive graph \(X\) on \(n\) vertices satisfies

\[
m(X)\leq C_d\frac{n}{(1+\log n)^2},
\]

where \(m(X)\) is the multiplicity of the second adjacency eigenvalue. The explicit constants are

\[
K_d=8d+6+2\log(32d)+\log(4(d+1)),
\qquad
C_d=\max\{4K_d^2,\,8,\,(1+\log(2d))^2\}.
\]

The source theorem is the theorem environment labelled `thm:main` in `paper.tex`.

### Lean statement and proof location

The Lean definitions for the main theorem are in [`MainTheorem.lean`](MainTheorem.lean):

- `IsMainGraph` is defined at [`MainTheorem.lean#L45-L46`](MainTheorem.lean#L45-L46) and packages connectedness, \(d\)-regularity, and vertex-transitivity;
- `IsSecondAdjacencyEigenvalue` is defined at [`MainTheorem.lean#L74-L78`](MainTheorem.lean#L74-L78);
- the constants `K`, `C`, and the target inequality `MainTheoremClaim` are defined at [`MainTheorem.lean#L81-L94`](MainTheorem.lean#L81-L94).

The completed theorem is `MainTheorem.main_theorem`, located at [`MainTheoremProof.lean#L119-L124`](MainTheoremProof.lean#L119-L124):

```lean
theorem main_theorem
    (G : SimpleGraph V) (d : ℕ) (lam : ℝ)
    (hd : 2 ≤ d)
    (hG : IsMainGraph G d)
    (hlam : IsSecondAdjacencyEigenvalue G (d : ℝ) lam) :
    MainTheoremClaim G d lam := by
  ...
```

Here `Fintype.card V` represents \(n\), `lam` represents the second adjacency eigenvalue, and `adjacencyEigenvalueMultiplicity G lam` represents \(m(X)\). Thus `MainTheoremClaim G d lam` is the formal version of the inequality in the paper's Theorem 1.2.

The main supporting files are:

- [`MainTheoremArithmetic.lean`](MainTheoremArithmetic.lean): arithmetic and combinatorial lemmas;
- [`MainTheoremSpectral.lean`](MainTheoremSpectral.lean): spectral and graph-theoretic setup;
- [`CheckUniform.lean`](CheckUniform.lean), [`CheckEdge.lean`](CheckEdge.lean), and related files: intermediate lemmas used by the proof;
- [`CheckProp24.lean`](CheckProp24.lean): the final proposition-level assembly.

The remaining `Check*.lean` files record auxiliary formalization and API-checking steps and are retained for reproducibility.

## Contribution and assistance

The primary contributor to the mathematical result is **Jiasheng Zeng**. The result and its Lean formalization were developed with assistance from **GPT-6 Astra**.

## Provenance

[`PRIORITY_RECORD.md`](PRIORITY_RECORD.md) records the UTC preparation time and a SHA-256 digest of the uploadable content. For provenance, retain that record together with the first Git commit and the private GitHub push timestamp.

## Axiom audit

The file [`MainTheoremAxiomAudit.lean`](MainTheoremAxiomAudit.lean) can be checked with:

```powershell
lake env lean .\MainTheoremAxiomAudit.lean
```

This prints the axioms used by the main theorem. Standard Lean foundations such as `propext`, `Classical.choice`, and `Quot.sound` may appear in the output; `sorryAx` would indicate an unfinished proof.

## Search for unfinished or nonstandard declarations

In PowerShell, from the repository root:

```powershell
Get-ChildItem -Path . -Recurse -File -Filter *.lean |
  Where-Object { $_.FullName -notmatch '\\.lake\\' } |
  Select-String -Pattern '\\b(sorry|admit|axiom|unsafe)\\b' -CaseSensitive:$false
```

No output means that these words were not found in the Lean source files, although comments and strings should still be checked manually if there is a match.
