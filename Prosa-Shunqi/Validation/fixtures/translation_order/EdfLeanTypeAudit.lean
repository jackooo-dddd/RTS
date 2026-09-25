import Prosa.Model.Schedule.Edf

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Schedule.Edf

#check @EDF_at
#check @EDF_schedule
#print EDF_at
#print EDF_schedule
#print axioms EDF_at
#print axioms EDF_schedule

example {Job : JobType} [DecidableEq Job]
    [JobDeadline Job] [JobArrival Job]
    {PState : ProcessorState Job} (sched : schedule PState) (t : instant) :
    EDF_at sched t =
      (∀ (j : Job), scheduled_at sched j t = true →
        ∀ (t' : instant) (j' : Job),
          t ≤ t' → scheduled_at sched j' t' = true →
          job_arrival j' ≤ t → job_deadline j ≤ job_deadline j') := by
  rfl

example {Job : JobType} [DecidableEq Job]
    [JobDeadline Job] [JobArrival Job]
    {PState : ProcessorState Job} (sched : schedule PState) :
    EDF_schedule sched = (∀ t : instant, EDF_at sched t) := by
  rfl
