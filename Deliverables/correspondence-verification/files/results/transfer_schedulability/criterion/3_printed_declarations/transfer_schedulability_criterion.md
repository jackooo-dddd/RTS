# `transfer_schedulability_criterion`

- Kind (Rocq): Definition
- Rocq: `prosa.results.transfer_schedulability.criterion.transfer_schedulability_criterion`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.transfer_schedulability_criterion`
- Certificate: `transfer_schedulability_criterion_correspondence`

## Official Rocq

```coq
transfer_schedulability_criterion :
forall {Job : JobType},
@schedule Job (ideal.processor_state Job) ->
@schedule Job (ideal.processor_state Job) ->
JobCost Job -> JobCost Job -> arrival_sequence Job -> JobCost Job -> Prop

transfer_schedulability_criterion is not universe polymorphic
Arguments transfer_schedulability_criterion {Job} ref_sched online_sched ref_job_cost 
  online_job_cost arr_seq job_cost_bound
transfer_schedulability_criterion is transparent
Expands to: Constant prosa.results.transfer_schedulability.criterion.transfer_schedulability_criterion
Declared in library prosa.results.transfer_schedulability.criterion, line 569, characters 15-48
@transfer_schedulability_criterion
     : forall Job : JobType,
       @schedule Job (ideal.processor_state Job) ->
       @schedule Job (ideal.processor_state Job) ->
       JobCost Job -> JobCost Job -> arrival_sequence Job -> JobCost Job -> Prop
```

Body:

```coq
transfer_schedulability_criterion =
fun Job : JobType =>
let PState := ideal.processor_state Job in
fun (ref_sched online_sched : @schedule Job PState) (ref_job_cost online_job_cost : JobCost Job) =>
let ref_completed_by := @completed_by Job PState ref_sched ref_job_cost in
let online_completed_by := @completed_by Job PState online_sched online_job_cost in
fun (arr_seq : arrival_sequence Job) (job_cost_bound : JobCost Job) =>
forall t1 t2 : nat,
is_true
  (@slackless_interval Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2) ->
exists j : Equality.sort Job,
  is_true
    (@scheduled_at Job PState online_sched j t1 &&
     (j \in @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2))
     : forall {Job : JobType},
       @schedule Job (ideal.processor_state Job) ->
       @schedule Job (ideal.processor_state Job) ->
       JobCost Job -> JobCost Job -> arrival_sequence Job -> JobCost Job -> Prop

Arguments transfer_schedulability_criterion {Job} ref_sched online_sched ref_job_cost 
  online_job_cost arr_seq job_cost_bound
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.transfer_schedulability_criterion : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
        Prosa.Behavior.Job.JobCost Job →
          Prosa.Behavior.Job.JobCost Job →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Job.JobCost Job → Prop
```

Body:

```lean
def Prosa.Results.TransferSchedulability.Criterion.transfer_schedulability_criterion.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
        Prosa.Behavior.Job.JobCost Job →
          Prosa.Behavior.Job.JobCost Job →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Job.JobCost Job → Prop :=
fun {Job} [DecidableEq Job] ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound =>
  ∀ (t1 t2 : ℕ),
    Prosa.Results.TransferSchedulability.Criterion.slackless_interval ref_sched online_sched ref_job_cost
          online_job_cost arr_seq job_cost_bound t1 t2 =
        true →
      ∃ j,
        (Prosa.Behavior.Service.scheduled_at online_sched j t1 &&
            decide
              (j ∈
                Prosa.Results.TransferSchedulability.Criterion.critical_jobs ref_sched online_sched ref_job_cost
                  online_job_cost arr_seq t1 t2)) =
          true
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_transfer_schedulability_criterion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Results_TransferSchedulability_Criterion_transfer_schedulability_criterion@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (ref_sched
   online_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
  (ref_job_cost
   online_job_cost : Prosa_Behavior_Job_JobCost Job
                       inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (job_cost_bound : Prosa_Behavior_Job_JobCost Job
                      inst_3) =>
forall t1 t2 : Nat,
@eq Bool
  (Prosa_Results_TransferSchedulability_Criterion_slackless_interval Job
     inst_3 ref_sched
     online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2)
  Bool_true ->
Exists Job
  (fun j : Job =>
   Bool_and
     (Prosa_Behavior_Service_scheduled_at_inst4 Job
        inst_3
        (Prosa_Model_Processor_Ideal_processor_state Job
           inst_3)
        online_sched j t1)
     (Decidable_decide
        (Membership_mem Job (List Job) (List_instMembership Job)
           (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
              inst_3 ref_sched
              online_sched ref_job_cost online_job_cost arr_seq t1 t2)
           j)
        (List_instDecidableMemOfLawfulBEq Job
           (instBEqOfDecidableEq Job
              inst_3)
           (instLawfulBEq Job
              inst_3)
           j
           (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
              inst_3 ref_sched
              online_sched ref_job_cost online_job_cost arr_seq t1 t2))) =
   Bool_true)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       SProp

Arguments Prosa_Results_TransferSchedulability_Criterion_transfer_schedulability_criterion 
  Job inst_3 
  ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
```
