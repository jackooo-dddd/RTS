import Prosa.Model.Schedule.PreemptionTime
import Validation.fixtures.translation_order.PreemptionParameterComputationInterface

/-!
Export root for `model/schedule/preemption_time.v`: the production
declaration, the accepted preemption-parameter export root, and
kernel-checked case equations for the `Option` match in the body and for
`List.head?`.  Every equation is proved in Lean and exported with its proof.
-/

namespace Prosa.Validation.PreemptionTimeInterface

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Schedule.PreemptionTime

theorem production_preemption_time_some {Job : JobType} [DecidableEq Job] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job}
    (sched : schedule PState) (t : Nat) (j : Job)
    (h : scheduled_job_at arr_seq sched t = some j) :
    preemption_time arr_seq sched t = job_preemptable j (service sched j t) := by
  unfold preemption_time; rw [h]

theorem production_preemption_time_none {Job : JobType} [DecidableEq Job] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job}
    (sched : schedule PState) (t : Nat)
    (h : scheduled_job_at arr_seq sched t = none) :
    preemption_time arr_seq sched t = true := by
  unfold preemption_time; rw [h]

theorem production_scheduled_job_at_eq {Job : JobType} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job}
    (sched : schedule PState) (t : Nat) :
    scheduled_job_at arr_seq sched t =
      ((arrivals_up_to arr_seq t).filter fun j => scheduled_at sched j t).head? := rfl

theorem production_head_nil {T : Type} : ([] : List T).head? = none := rfl

theorem production_head_cons {T : Type} (x : T) (xs : List T) : (x :: xs).head? = some x := rfl

end Prosa.Validation.PreemptionTimeInterface
