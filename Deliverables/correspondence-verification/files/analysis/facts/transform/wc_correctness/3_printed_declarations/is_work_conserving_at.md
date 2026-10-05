# `is_work_conserving_at`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.transform.wc_correctness.is_work_conserving_at`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.is_work_conserving_at`
- Certificate: `is_work_conserving_at_correspondence`

## Official Rocq

```coq
is_work_conserving_at :
forall {Job : JobType},
JobArrival Job ->
JobCost Job -> arrival_sequence Job -> @schedule Job (processor_state Job) -> instant -> Prop

is_work_conserving_at is not universe polymorphic
Arguments is_work_conserving_at {Job H H0} arr_seq sched t
is_work_conserving_at is transparent
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.is_work_conserving_at
Declared in library prosa.analysis.facts.transform.wc_correctness, line 42, characters 13-34
@is_work_conserving_at
     : forall Job : JobType,
       JobArrival Job ->
       JobCost Job -> arrival_sequence Job -> @schedule Job (processor_state Job) -> instant -> Prop
```

Body:

```coq
is_work_conserving_at =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (processor_state Job)) (t : instant) =>
(exists j : Equality.sort Job,
   @arrives_in Job arr_seq j /\
   is_true
     (@job_ready Job (processor_state Job) H0 H (@basic.basic_ready_instance Job (processor_state Job) H H0)
        sched j t)) ->
exists j : Equality.sort Job, sched t = @Some (Equality.sort Job) j
     : forall {Job : JobType},
       JobArrival Job ->
       JobCost Job -> arrival_sequence Job -> @schedule Job (processor_state Job) -> instant -> Prop

Arguments is_work_conserving_at {Job H H0} arr_seq sched t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.is_work_conserving_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
            Prosa.Behavior.Time.instant → Prop
```

Body:

```lean
def Prosa.Analysis.Facts.Transform.WcCorrectness.is_work_conserving_at.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
            Prosa.Behavior.Time.instant → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] arr_seq sched t =>
  (∃ j, Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j ∧ Prosa.Behavior.Ready.job_ready sched j t = true) →
    ∃ j, sched t = some j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_is_work_conserving_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> SProp
```

Body:

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_is_work_conserving_at@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (inst_9 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Ideal_processor_state Job
                inst_3))
  (t : Prosa_Behavior_Time_instant) =>
Exists Job
  (fun j : Job =>
   And
     (Prosa_Behavior_Arrival_sequence_arrives_in Job
        inst_3 arr_seq j)
     (@eq Bool
        (Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job
           inst_3
           (Prosa_Model_Processor_Ideal_processor_state Job
              inst_3)
           inst_9
           inst_6
           (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
              inst_3
              (Prosa_Model_Processor_Ideal_processor_state Job
                 inst_3)
              inst_6
              inst_9)
           sched j t)
        Bool_true)) ->
Exists Job (fun j : Job => sched t = Option_some Job j)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> SProp

Arguments Prosa_Analysis_Facts_Transform_WcCorrectness_is_work_conserving_at Job
  inst_3
  inst_6
  inst_9 
  arr_seq sched t
```
