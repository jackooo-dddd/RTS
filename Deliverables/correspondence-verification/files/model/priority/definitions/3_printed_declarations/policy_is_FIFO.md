# `policy_is_FIFO`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.policy_is_FIFO`
- Lean: `Prosa.Model.Priority.Definitions.policy_is_FIFO`
- Certificate: `pd_policy_is_FIFO_certificate`

## Official Rocq

```coq
policy_is_FIFO : forall {Job : JobType}, JobArrival Job -> JLFP_policy Job -> Prop

policy_is_FIFO is not universe polymorphic
Arguments policy_is_FIFO {Job H1} JLFP
policy_is_FIFO is transparent
Expands to: Constant prosa.model.priority.definitions.policy_is_FIFO
Declared in library prosa.model.priority.definitions, line 117, characters 15-29
@policy_is_FIFO
     : forall Job : JobType, JobArrival Job -> JLFP_policy Job -> Prop
```

Body:

```coq
policy_is_FIFO =
fun (Job : JobType) (H1 : JobArrival Job) (JLFP : JLFP_policy Job) =>
forall j1 j2 : Equality.sort Job,
@hep_job Job JLFP j1 j2 = (@job_arrival Job H1 j1 <= @job_arrival Job H1 j2)
     : forall {Job : JobType}, JobArrival Job -> JLFP_policy Job -> Prop

Arguments policy_is_FIFO {Job H1} JLFP
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.policy_is_FIFO : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job → Prop
def Prosa.Model.Priority.Definitions.policy_is_FIFO.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] JLFP =>
  ∀ (j1 j2 : Job),
    Prosa.Model.Priority.Definitions.hep_job j1 j2 =
      decide (Prosa.Behavior.Job.job_arrival j1 ≤ Prosa.Behavior.Job.job_arrival j2)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_policy_is_FIFO
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Priority_Definitions_policy_is_FIFO@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                             inst_3)
  (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3) =>
forall j1 j2 : Job,
@eq Bool
  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_3 JLFP j1 j2)
  (Decidable_decide
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
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Priority_Definitions_policy_is_FIFO Job
  inst_3
  inst_6 JLFP
```
