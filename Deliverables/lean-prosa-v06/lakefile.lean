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

/-- The 22 case-study statements of the benchmark (read-only). -/
@[default_target]
lean_lib CaseStudies where
  srcDir := "."
  roots := #[`CaseStudies]
  globs := #[.andSubmodules `CaseStudies]

/-- Benchmark workspace: one `solution` per case study (templates end in `sorry`). -/
lean_lib Solutions where
  srcDir := "."
  roots := #[`Solutions]
  globs := #[.submodules `Solutions]

/-- Usage example; built only on request (`lake build Examples`). -/
lean_lib Examples where
  srcDir := "."
  roots := #[`Examples.RTSExample]
