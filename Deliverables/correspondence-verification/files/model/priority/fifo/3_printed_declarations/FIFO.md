# `FIFO`

- Kind (Rocq): Instance
- Rocq: `prosa.model.priority.fifo.FIFO`
- Lean: `Prosa.Model.Priority.Fifo.FIFO`
- Certificate: `FIFO_correspondence`

## Official Rocq

```coq
FIFO : forall Job : JobType, JobArrival Job -> JLFP_policy Job

FIFO is not universe polymorphic
Arguments FIFO Job {H} _ _
FIFO is transparent
Expands to: Constant prosa.model.priority.fifo.FIFO
Declared in library prosa.model.priority.fifo, line 8, characters 0-143
FIFO
     : forall Job : JobType, JobArrival Job -> JLFP_policy Job
```

Body:

```coq
FIFO =
fun (Job : JobType) (H : JobArrival Job) (j1 j2 : Equality.sort Job) =>
@job_arrival Job H j1 <= @job_arrival Job H j2
     : forall Job : JobType, JobArrival Job -> JLFP_policy Job

Arguments FIFO Job {H} _ _
```

## Lean

```lean
Prosa.Model.Priority.Fifo.FIFO : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobArrival Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job
```

Body:

```lean
@[instance_reducible] def Prosa.Model.Priority.Fifo.FIFO.{u_1} : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobArrival Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job :=
fun Job [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] =>
  { hep_job := fun j1 j2 => decide (Prosa.Behavior.Job.job_arrival j1 ≤ Prosa.Behavior.Job.job_arrival j2) }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Fifo_FIFO
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3
```

Body:

```coq
Prosa_Model_Priority_Fifo_FIFO@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                      inst_3) =>
Prosa_Model_Priority_Definitions_JLFP_policy_mk Job
  inst_3
  (fun j1 j2 : Job =>
   Decidable_decide
     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j1)
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j2))
     (Nat_decLe
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j1)
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j2)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3

Arguments Prosa_Model_Priority_Fifo_FIFO Job inst_3
  inst_6
```
