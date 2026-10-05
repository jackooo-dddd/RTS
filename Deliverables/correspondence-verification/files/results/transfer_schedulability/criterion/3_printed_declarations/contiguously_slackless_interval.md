# `contiguously_slackless_interval`

- Kind (Rocq): Definition
- Rocq: `prosa.results.transfer_schedulability.criterion.contiguously_slackless_interval`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.contiguously_slackless_interval`
- Certificate: `contiguously_slackless_interval_correspondence`

## Official Rocq

```coq
contiguously_slackless_interval :
forall {Job : JobType},
@schedule Job (ideal.processor_state Job) ->
@schedule Job (ideal.processor_state Job) ->
JobCost Job -> JobCost Job -> arrival_sequence Job -> JobCost Job -> nat -> nat -> bool

contiguously_slackless_interval is not universe polymorphic
Arguments contiguously_slackless_interval {Job} ref_sched online_sched ref_job_cost 
  online_job_cost arr_seq job_cost_bound (t1 t2)%nat_scope
contiguously_slackless_interval is transparent
Expands to: Constant prosa.results.transfer_schedulability.criterion.contiguously_slackless_interval
Declared in library prosa.results.transfer_schedulability.criterion, line 541, characters 15-46
@contiguously_slackless_interval
     : forall Job : JobType,
       @schedule Job (ideal.processor_state Job) ->
       @schedule Job (ideal.processor_state Job) ->
       JobCost Job -> JobCost Job -> arrival_sequence Job -> JobCost Job -> nat -> nat -> bool
```

Body:

```coq
contiguously_slackless_interval =
fun Job : JobType =>
let PState := ideal.processor_state Job in
fun (ref_sched online_sched : @schedule Job PState) (ref_job_cost online_job_cost : JobCost Job) =>
let ref_completed_by := @completed_by Job PState ref_sched ref_job_cost in
let online_completed_by := @completed_by Job PState online_sched online_job_cost in
fun (arr_seq : arrival_sequence Job) (job_cost_bound : JobCost Job) (t1 t2 : nat) =>
@slackless_interval Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 &&
   @slackless_interval Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
     (t1 + @nat_of_ord (t2 - t1) delta) t2]
     : forall {Job : JobType},
       @schedule Job (ideal.processor_state Job) ->
       @schedule Job (ideal.processor_state Job) ->
       JobCost Job -> JobCost Job -> arrival_sequence Job -> JobCost Job -> nat -> nat -> bool

Arguments contiguously_slackless_interval {Job} ref_sched online_sched ref_job_cost 
  online_job_cost arr_seq job_cost_bound (t1 t2)%nat_scope
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.contiguously_slackless_interval : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
        Prosa.Behavior.Job.JobCost Job →
          Prosa.Behavior.Job.JobCost Job →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Job.JobCost Job → ℕ → ℕ → Bool
```

Body:

```lean
def Prosa.Results.TransferSchedulability.Criterion.contiguously_slackless_interval.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
        Prosa.Behavior.Job.JobCost Job →
          Prosa.Behavior.Job.JobCost Job →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Job.JobCost Job → ℕ → ℕ → Bool :=
fun {Job} [DecidableEq Job] ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 =>
  Prosa.Results.TransferSchedulability.Criterion.slackless_interval ref_sched online_sched ref_job_cost online_job_cost
      arr_seq job_cost_bound t1 t2 &&
    (List.range' 0 (t2 - t1)).all fun delta =>
      Prosa.Results.TransferSchedulability.Criterion.slackless_interval ref_sched online_sched ref_job_cost
        online_job_cost arr_seq job_cost_bound (t1 + delta) t2
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_contiguously_slackless_interval
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
Prosa_Results_TransferSchedulability_Criterion_contiguously_slackless_interval@{u_1 Lean.u_1+1.0
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
                      inst_3)
  (t1 t2 : Nat) =>
Bool_and
  (Prosa_Results_TransferSchedulability_Criterion_slackless_interval Job
     inst_3 ref_sched
     online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2)
  (List_all_inst1 Nat
     (List_range' (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
        (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) t2 t1)
        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     (fun delta : Nat =>
      Prosa_Results_TransferSchedulability_Criterion_slackless_interval Job
        inst_3 ref_sched
        online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
        (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t1 delta) t2))
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

Arguments Prosa_Results_TransferSchedulability_Criterion_contiguously_slackless_interval 
  Job inst_3 
  ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
  (t1 x____at___Init_Prelude2408276647__hygCtx__hyg14)%_Nat_scope
```
