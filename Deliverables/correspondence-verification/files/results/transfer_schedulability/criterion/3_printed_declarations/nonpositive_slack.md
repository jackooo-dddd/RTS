# `nonpositive_slack`

- Kind (Rocq): Definition
- Rocq: `prosa.results.transfer_schedulability.criterion.nonpositive_slack`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.nonpositive_slack`
- Certificate: `nonpositive_slack_correspondence`

## Official Rocq

```coq
nonpositive_slack :
forall {Job : JobType},
@schedule Job (ideal.processor_state Job) ->
@schedule Job (ideal.processor_state Job) ->
JobCost Job -> JobCost Job -> arrival_sequence Job -> JobCost Job -> nat -> nat -> bool

nonpositive_slack is not universe polymorphic
Arguments nonpositive_slack {Job} ref_sched online_sched ref_job_cost online_job_cost 
  arr_seq job_cost_bound (t1 t2)%nat_scope
nonpositive_slack is transparent
Expands to: Constant prosa.results.transfer_schedulability.criterion.nonpositive_slack
Declared in library prosa.results.transfer_schedulability.criterion, line 667, characters 15-32
@nonpositive_slack
     : forall Job : JobType,
       @schedule Job (ideal.processor_state Job) ->
       @schedule Job (ideal.processor_state Job) ->
       JobCost Job -> JobCost Job -> arrival_sequence Job -> JobCost Job -> nat -> nat -> bool
```

Body:

```coq
nonpositive_slack =
fun Job : JobType =>
let PState := ideal.processor_state Job in
fun (ref_sched online_sched : @schedule Job PState) (ref_job_cost online_job_cost : JobCost Job) =>
let ref_completed_by := @completed_by Job PState ref_sched ref_job_cost in
let online_completed_by := @completed_by Job PState online_sched online_job_cost in
fun (arr_seq : arrival_sequence Job) (job_cost_bound : JobCost Job) (t1 t2 : nat) =>
t2 - t1 <=
\sum_(j <- @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2)
   @remaining_cost_bound Job online_sched job_cost_bound j t1
     : forall {Job : JobType},
       @schedule Job (ideal.processor_state Job) ->
       @schedule Job (ideal.processor_state Job) ->
       JobCost Job -> JobCost Job -> arrival_sequence Job -> JobCost Job -> nat -> nat -> bool

Arguments nonpositive_slack {Job} ref_sched online_sched ref_job_cost online_job_cost 
  arr_seq job_cost_bound (t1 t2)%nat_scope
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.nonpositive_slack : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
        Prosa.Behavior.Job.JobCost Job →
          Prosa.Behavior.Job.JobCost Job →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Job.JobCost Job → ℕ → ℕ → Bool
```

Body:

```lean
def Prosa.Results.TransferSchedulability.Criterion.nonpositive_slack.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
        Prosa.Behavior.Job.JobCost Job →
          Prosa.Behavior.Job.JobCost Job →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Job.JobCost Job → ℕ → ℕ → Bool :=
fun {Job} [DecidableEq Job] ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 =>
  decide
    (t2 - t1 ≤
      Prosa.Util.Sum.sumSeq
        (Prosa.Results.TransferSchedulability.Criterion.critical_jobs ref_sched online_sched ref_job_cost
          online_job_cost arr_seq t1 t2)
        fun j => Prosa.Results.TransferSchedulability.Criterion.remaining_cost_bound online_sched job_cost_bound j t1)
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_nonpositive_slack
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
       Nat -> Nat -> Bool
```

Body:

```coq
Prosa_Results_TransferSchedulability_Criterion_nonpositive_slack@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
                      inst_3)
  (t1 t2 : Nat) =>
Decidable_decide
  (LE_le_inst1 Nat instLENat (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) t2 t1)
     (Prosa_Util_Sum_sumSeq Job
        (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
           inst_3 ref_sched
           online_sched ref_job_cost online_job_cost arr_seq t1 t2)
        (fun j : Job =>
         Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job
           inst_3 online_sched
           job_cost_bound j t1)))
  (Nat_decLe (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) t2 t1)
     (Prosa_Util_Sum_sumSeq Job
        (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
           inst_3 ref_sched
           online_sched ref_job_cost online_job_cost arr_seq t1 t2)
        (fun j : Job =>
         Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job
           inst_3 online_sched
           job_cost_bound j t1)))
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
       Nat -> Nat -> Bool

Arguments Prosa_Results_TransferSchedulability_Criterion_nonpositive_slack Job
  inst_3 
  ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
  (t1 x____at___Init_Prelude2408276647__hygCtx__hyg14)%_Nat_scope
```
