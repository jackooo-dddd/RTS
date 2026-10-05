# `uni_schedule`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.ideal_uni_scheduler.uni_schedule`
- Lean: `Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule`
- Certificate: `uni_schedule_correspondence`

## Official Rocq

```coq
uni_schedule :
forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job},
arrival_sequence Job ->
@JobReady Job (processor_state Job) JC JA ->
JobPreemptable Job -> JLDP_policy Job -> @schedule Job (processor_state Job)

uni_schedule is not universe polymorphic
Arguments uni_schedule {Job JC JA} arr_seq {RM H H0} _
uni_schedule is transparent
Expands to: Constant prosa.implementation.definitions.ideal_uni_scheduler.uni_schedule
Declared in library prosa.implementation.definitions.ideal_uni_scheduler, line 97, characters 15-27
@uni_schedule
     : forall (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job),
       arrival_sequence Job ->
       @JobReady Job (processor_state Job) JC JA ->
       JobPreemptable Job -> JLDP_policy Job -> @schedule Job (processor_state Job)
```

Body:

```coq
uni_schedule =
fun (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job) =>
let PState := processor_state Job in
let idle_state := @None (Equality.sort Job) in
fun (arr_seq : arrival_sequence Job) (RM : @JobReady Job (processor_state Job) JC JA)
  (H : JobPreemptable Job) (H0 : JLDP_policy Job) =>
@pmc_uni_schedule Job JC JA arr_seq RM H (@choose_highest_prio_job Job H0)
     : forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job},
       arrival_sequence Job ->
       @JobReady Job (processor_state Job) JC JA ->
       JobPreemptable Job -> JLDP_policy Job -> @schedule Job (processor_state Job)

Arguments uni_schedule {Job JC JA} arr_seq {RM H H0} _
```

## Lean

```lean
@Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          [Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)] →
            [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
              [Prosa.Model.Priority.Definitions.JLDP_policy Job] →
                Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)
```

Body:

```lean
def Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          [Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)] →
            [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
              [Prosa.Model.Priority.Definitions.JLDP_policy Job] →
                Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job] arr_seq
    [Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)]
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] [Prosa.Model.Priority.Definitions.JLDP_policy Job] =>
  Prosa.Implementation.Definitions.IdealUniScheduler.pmc_uni_schedule arr_seq
    Prosa.Implementation.Definitions.IdealUniScheduler.choose_highest_prio_job
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule
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
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
```

Body:

```coq
Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
  (inst_24 : 
   Prosa_Model_Priority_Definitions_JLDP_policy Job
     inst_3) =>
Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule Job
  inst_3
  inst_6
  inst_9 arr_seq
  inst_14
  inst_21
  (Prosa_Implementation_Definitions_IdealUniScheduler_choose_highest_prio_job Job
     inst_3
     inst_24)
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
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)

Arguments Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule Job
  inst_3
  inst_6
  inst_9 
  arr_seq inst_14
  inst_21
  inst_24
  a____at____internal__hyg0
```
