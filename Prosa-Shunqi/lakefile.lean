import Lake
open Lake DSL

package prosa_v06_translation where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib Prosa where
  srcDir := "."
  roots := #[`Prosa]
  globs := #[.submodules `Prosa]

/-- Lean translations (and proofs) of the 22 RTS_Papers case studies over the classic Lean Prosa
(`classic-prosa/casestudy-translation/lean`, see that folder's README). -/
lean_lib CaseStudies where
  srcDir := "classic-prosa/casestudy-translation/lean"
  roots := #[`CaseStudies]
  globs := #[.andSubmodules `CaseStudies]
