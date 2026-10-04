-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/suspension.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 31)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence

/-!
Job self-suspensions (Rocq module `Suspension`).

Representation notes:
* `job_suspension Job := Job -> time -> duration` is a reducible type definition (`abbrev`); `Job` is an
  explicit `eqType` parameter, as in the source section `SuspensionTimes`.
* `\sum_(0 <= t < job_cost j) F t` is `∑ t ∈ Finset.Ico 0 (job_cost j), F t`.
* The section-local `Let total_job_suspension` is unfolded.
-/

namespace Prosa.Classic.Model.Suspension.Suspension

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence

universe u v

abbrev job_suspension (Job : Type u) [DecidableEq Job] := Job → time → duration

def total_suspension {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (next_suspension : job_suspension Job) (j : Job) : Nat :=
  ∑ t ∈ Finset.Ico 0 (job_cost j), next_suspension j t

def dynamic_suspension_model {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → Task) (next_suspension : job_suspension Job)
    (suspension_bound : Task → duration) : Prop :=
  ∀ j, total_suspension job_cost next_suspension j ≤ suspension_bound (job_task j)

end Prosa.Classic.Model.Suspension.Suspension
