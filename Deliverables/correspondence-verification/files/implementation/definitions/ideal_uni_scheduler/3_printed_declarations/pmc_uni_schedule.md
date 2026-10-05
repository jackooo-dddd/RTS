# `pmc_uni_schedule`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.ideal_uni_scheduler.pmc_uni_schedule`
- Lean: `Prosa.Implementation.Definitions.IdealUniScheduler.pmc_uni_schedule`
- Certificate: `pmc_uni_schedule_correspondence`

## Official Rocq

```coq
pmc_uni_schedule :
forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job},
arrival_sequence Job ->
@JobReady Job (processor_state Job) JC JA ->
JobPreemptable Job ->
(instant -> seq (Equality.sort Job) -> option (Equality.sort Job)) -> @schedule Job (processor_state Job)

pmc_uni_schedule is not universe polymorphic
Arguments pmc_uni_schedule {Job JC JA} arr_seq {RM H} choose_job%function_scope _
pmc_uni_schedule is transparent
Expands to: Constant prosa.implementation.definitions.ideal_uni_scheduler.pmc_uni_schedule
Declared in library prosa.implementation.definitions.ideal_uni_scheduler, line 80, characters 15-31
@pmc_uni_schedule
     : forall (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job),
       arrival_sequence Job ->
       @JobReady Job (processor_state Job) JC JA ->
       JobPreemptable Job ->
       (instant -> seq (Equality.sort Job) -> option (Equality.sort Job)) ->
       @schedule Job (processor_state Job)
```

Body:

```coq
pmc_uni_schedule =
fun (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job) =>
let PState := processor_state Job in
let idle_state := @None (Equality.sort Job) in
fun (arr_seq : arrival_sequence Job) (RM : @JobReady Job (processor_state Job) JC JA)
  (H : JobPreemptable Job) (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)) =>
@generic_schedule Job (processor_state Job) (@allocation_at Job JC JA arr_seq RM H choose_job) idle_state
     : forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job},
       arrival_sequence Job ->
       @JobReady Job (processor_state Job) JC JA ->
       JobPreemptable Job ->
       (instant -> seq (Equality.sort Job) -> option (Equality.sort Job)) ->
       @schedule Job (processor_state Job)

Arguments pmc_uni_schedule {Job JC JA} arr_seq {RM H} choose_job%function_scope _
```

## Lean

```lean
@Prosa.Implementation.Definitions.IdealUniScheduler.pmc_uni_schedule : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          [Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)] →
            [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
              (Prosa.Behavior.Time.instant → List Job → Option Job) →
                Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)
```

Body:

```lean
def Prosa.Implementation.Definitions.IdealUniScheduler.pmc_uni_schedule.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          [Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)] →
            [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
              (Prosa.Behavior.Time.instant → List Job → Option Job) →
                Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job] arr_seq
    [Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)]
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] choose_job =>
  Prosa.Implementation.Definitions.GenericScheduler.generic_schedule
    (Prosa.Implementation.Definitions.IdealUniScheduler.allocation_at arr_seq choose_job) none
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule
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
            inst_3)
```

Body:

```coq
Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
  (choose_job : Prosa_Behavior_Time_instant -> List Job -> Option Job) =>
Prosa_Implementation_Definitions_GenericScheduler_generic_schedule_inst2 Job
  inst_3
  (Prosa_Model_Processor_Ideal_processor_state Job
     inst_3)
  (Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at Job
     inst_3
     inst_6
     inst_9 arr_seq
     inst_14
     inst_21 choose_job)
  (Option_none Job)
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
            inst_3)

Arguments Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule Job
  inst_3
  inst_6
  inst_9 
  arr_seq inst_14
  inst_21
  choose_job%_function_scope a____at____internal__hyg0
```
