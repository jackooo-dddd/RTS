# `allocation_at`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.ideal_uni_scheduler.allocation_at`
- Lean: `Prosa.Implementation.Definitions.IdealUniScheduler.allocation_at`
- Certificate: `allocation_at_correspondence`

## Official Rocq

```coq
allocation_at :
forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job},
arrival_sequence Job ->
@JobReady Job (processor_state Job) JC JA ->
JobPreemptable Job ->
(instant -> seq (Equality.sort Job) -> option (Equality.sort Job)) ->
@schedule Job (processor_state Job) -> instant -> option (Equality.sort Job)

allocation_at is not universe polymorphic
Arguments allocation_at {Job JC JA} arr_seq {RM H} choose_job%function_scope sched_prefix t
allocation_at is transparent
Expands to: Constant prosa.implementation.definitions.ideal_uni_scheduler.allocation_at
Declared in library prosa.implementation.definitions.ideal_uni_scheduler, line 71, characters 17-30
@allocation_at
     : forall (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job),
       arrival_sequence Job ->
       @JobReady Job (processor_state Job) JC JA ->
       JobPreemptable Job ->
       (instant -> seq (Equality.sort Job) -> option (Equality.sort Job)) ->
       @schedule Job (processor_state Job) -> instant -> option (Equality.sort Job)
```

Body:

```coq
allocation_at =
fun (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job) (arr_seq : arrival_sequence Job)
  (RM : @JobReady Job (processor_state Job) JC JA) (H : JobPreemptable Job)
  (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job))
  (sched_prefix : @schedule Job (processor_state Job)) (t : instant) =>
if @prev_job_nonpreemptive Job JC JA RM H sched_prefix t
then sched_prefix t.-1
else choose_job t (@jobs_backlogged_at Job JA JC (processor_state Job) RM arr_seq sched_prefix t)
     : forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job},
       arrival_sequence Job ->
       @JobReady Job (processor_state Job) JC JA ->
       JobPreemptable Job ->
       (instant -> seq (Equality.sort Job) -> option (Equality.sort Job)) ->
       @schedule Job (processor_state Job) -> instant -> option (Equality.sort Job)

Arguments allocation_at {Job JC JA} arr_seq {RM H} choose_job%function_scope sched_prefix t
```

## Lean

```lean
@Prosa.Implementation.Definitions.IdealUniScheduler.allocation_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          [Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)] →
            [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
              (Prosa.Behavior.Time.instant → List Job → Option Job) →
                Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
                  Prosa.Behavior.Time.instant → Option Job
```

Body:

```lean
def Prosa.Implementation.Definitions.IdealUniScheduler.allocation_at.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          [Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)] →
            [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
              (Prosa.Behavior.Time.instant → List Job → Option Job) →
                Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
                  Prosa.Behavior.Time.instant → Option Job :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job] arr_seq
    [Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)]
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] choose_job sched_prefix t =>
  bif Prosa.Implementation.Definitions.IdealUniScheduler.prev_job_nonpreemptive sched_prefix t then sched_prefix (t - 1)
  else choose_job t (Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at arr_seq sched_prefix t)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Ready_JobReady_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         inst_6
         inst_9 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       (Prosa_Behavior_Time_instant -> List Job -> Option Job) ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Option Job
```

Body:

```coq
Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (inst_9 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (inst_14 : 
   Prosa_Behavior_Ready_JobReady_inst4 Job
     inst_3
     (Prosa_Model_Processor_Ideal_processor_state Job
        inst_3)
     inst_6
     inst_9)
  (inst_21 : 
   Prosa_Model_Preemption_Parameter_JobPreemptable Job
     inst_3)
  (choose_job : Prosa_Behavior_Time_instant -> List Job -> Option Job)
  (sched_prefix : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
  (t : Prosa_Behavior_Time_instant) =>
cond (Option Job)
  (Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive Job
     inst_3
     inst_6
     inst_9
     inst_14
     inst_21 sched_prefix t)
  (sched_prefix
     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t
        (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
  (choose_job t
     (Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at_inst4 Job
        inst_3
        inst_9
        inst_6
        (Prosa_Model_Processor_Ideal_processor_state Job
           inst_3)
        inst_14 arr_seq
        sched_prefix t))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Ready_JobReady_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         inst_6
         inst_9 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       (Prosa_Behavior_Time_instant -> List Job -> Option Job) ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Option Job

Arguments Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at Job
  inst_3
  inst_6
  inst_9 
  arr_seq inst_14
  inst_21
  choose_job%_function_scope sched_prefix t
```
