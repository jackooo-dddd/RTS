import CaseStudies.ECRTS2005.Lemma4.Statement

/-!
Benchmark task `2005-ECRTS-Lemma4`: prove `CaseStudies.ECRTS2005.Lemma4.ResponseTimeAnalysisEDF.Lemma4_05_statement`
(defined in `Statement.lean` in this folder, which also contains the case study's definitions).

The paper's statement and proof sketch (LaTeX) are in `proof.tex` in this folder.

Replace `sorry` with a proof.  You may add `import`s of modules of this package (`Prosa.*`, `Mathlib.*`),
helper definitions and lemmas, and new `.lean` files under `CaseStudies/` (for example next to this file).
Do not edit `Statement.lean`, `proof.tex` or anything outside `CaseStudies/`, and keep the name and type of
`solution`.  Check with `python3 benchmark/check.py 2005-ECRTS-Lemma4`.
-/

set_option linter.unusedVariables false

namespace CaseStudies.ECRTS2005.Lemma4

open CaseStudies.ECRTS2005.Lemma4.ResponseTimeAnalysisEDF
open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Util.Sum (sumFiltered)

universe u v

theorem solution : Lemma4_05_statement.{u, v} := by
  sorry

end CaseStudies.ECRTS2005.Lemma4
