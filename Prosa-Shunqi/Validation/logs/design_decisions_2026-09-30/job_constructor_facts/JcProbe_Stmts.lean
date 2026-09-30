import Prosa.Implementation.Definitions.JobConstructor
/-! Scratch probe (not a translation, not exported for validation): the six statements of
`implementation/facts/job_constructor.v` as `Prop` definitions at the concrete carriers, used only to list the
universe-specialised constants their import would need. -/
open Prosa.Behavior.Arrival_sequence Prosa.Behavior.Job Prosa.Model.Task.Concept
open Prosa.Implementation.Definitions.Task Prosa.Implementation.Definitions.JobConstructor
open Prosa.Implementation.Definitions.MaximalArrivalSequence
namespace JcProbe
def arr (ts : List concrete_task) : arrival_sequence concrete_job :=
  concrete_arrival_sequence generate_jobs_at ts
def s1 (ts : List concrete_task) : Prop := ∀ tsk n t, tsk ∈ ts → (generate_jobs_at tsk n t).length = n
def s2 : Prop := ∀ tsk n t, (generate_jobs_at tsk n t).Nodup
def s3 (ts : List concrete_task) : Prop := ∀ j t, j ∈ arrivals_at (arr ts) t → job_arrival j = t
def s4 (ts : List concrete_task) : Prop := ∀ t, (arrivals_at (arr ts) t).Nodup
def s5 (ts : List concrete_task) : Prop := ∀ t1 t2, (arrivals_between (arr ts) t1 t2).Nodup
def s6 : Prop := ∀ tsk n t j, j ∈ generate_jobs_at tsk n t →
  job_task j = tsk ∧ job_arrival j = t ∧ job_cost j ≤ task_cost tsk
end JcProbe
