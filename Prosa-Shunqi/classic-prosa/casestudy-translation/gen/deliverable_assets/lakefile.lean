import Lake
open Lake DSL

package lean_prosa_v06 where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "0df444a360eaa60ab8c11dca51a86af692955474"

/-- Prosa v0.6 (`Prosa/**`, except `Prosa/Classic`) and classic Prosa (`Prosa/Classic/**`). -/
@[default_target]
lean_lib Prosa where
  srcDir := "."
  roots := #[`Prosa]
  globs := #[.submodules `Prosa]

/-- The case-study benchmark: one folder per task, `CaseStudies/<G>/<F>/` with the read-only `Statement.lean`,
the hint `proof.tex` and the workspace `Solution.lean`.  `lake build` compiles the statements (the root
module `CaseStudies` imports them); a solution is built on request: `lake build CaseStudies.<G>.<F>.Solution`. -/
@[default_target]
lean_lib CaseStudies where
  srcDir := "."
  roots := #[`CaseStudies]

/-- Usage example; built only on request (`lake build Examples`). -/
lean_lib Examples where
  srcDir := "."
  roots := #[`Examples.RTSExample]
