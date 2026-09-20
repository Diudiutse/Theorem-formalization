import Lake

open Lake DSL

package theoremFormalization

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.2"

@[default_target]
lean_lib Formalization where
  roots := #[`Theorem11, `Theorem11Arithmetic, `Theorem11Spectral, `CheckUniform, `CheckEdge, `CheckCoherenceFull, `CheckBall, `CheckGap, `CheckRayleigh, `CheckCounting, `CheckLemma21, `CheckLemma22, `CheckLemma23, `CheckProp24, `Theorem11Proof]
