import CaseStudies.BOOK2015.Theorem18_6.Statement

/-!
Benchmark task `2015-book-Theorem18_6`: prove `CaseStudies.BOOK2015.Theorem18_6.Theorem18_6_statement`
(defined in `Statement.lean` in this folder, which also contains the case study's definitions).

The paper's statement and proof sketch (LaTeX) are in `proof.tex` in this folder.

Replace `sorry` with a proof.  You may add `import`s of modules of this package (`Prosa.*`, `Mathlib.*`),
helper definitions and lemmas, and new `.lean` files under `CaseStudies/` (for example next to this file).
Do not edit `Statement.lean`, `proof.tex` or anything outside `CaseStudies/`, and keep the name and type of
`solution`.  Check with `python3 benchmark/check.py 2015-book-Theorem18_6`.
-/

set_option linter.unusedVariables false

namespace CaseStudies.BOOK2015.Theorem18_6

open CaseStudies.BOOK2015.Theorem18_6
open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Util.Sum (sumSeq)

universe u

theorem solution : Theorem18_6_statement.{u} := by
  sorry

end CaseStudies.BOOK2015.Theorem18_6
