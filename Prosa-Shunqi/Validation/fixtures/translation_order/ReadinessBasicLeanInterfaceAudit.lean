import Prosa.Model.Readiness.Basic

open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service

#check @Prosa.Model.Readiness.Basic.basic_ready_instance
#print axioms Prosa.Model.Readiness.Basic.basic_ready_instance

example {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} [JobArrival Job] [JobCost Job]
    (sched : schedule PState) (j : Job) (t : Nat) :
    (Prosa.Model.Readiness.Basic.basic_ready_instance
      (PState := PState)).job_ready sched j t = pending sched j t := by
  rfl

-- The source instance is local; importing the target module must not register
-- an ambient JobReady instance either.
example {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} [JobArrival Job] [JobCost Job] : True := by
  fail_if_success exact (inferInstance : JobReady Job PState)
  trivial
