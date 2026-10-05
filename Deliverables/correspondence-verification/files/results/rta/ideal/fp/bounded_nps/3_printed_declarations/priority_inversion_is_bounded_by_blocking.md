# `priority_inversion_is_bounded_by_blocking`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded_by_blocking`
- Lean: `Prosa.Results.Rta.Ideal.Fp.BoundedNps.priority_inversion_is_bounded_by_blocking`
- Certificate: `priority_inversion_is_bounded_by_blocking_correspondence`

## Official Rocq

```coq
priority_inversion_is_bounded_by_blocking :
forall {Task : TaskType} {H1 : TaskMaxNonpreemptiveSegment Task} {Job : JobType} 
  {H2 : JobTask Job Task} {Arrival : JobArrival Job} {Cost : JobCost Job} {FP : FP_policy Task}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (ideal.processor_state Job))
  {H4 : JobPreemptable Job},
@valid_model_with_bounded_nonpreemptive_segments Task Job H2 Cost H1 H4 (ideal.processor_state Job) arr_seq
  sched ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H2 arr_seq ts ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job) (t1 t2 : instant),
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H2 tsk j) ->
@busy_interval_prefix Job Arrival Cost (ideal.processor_state Job) arr_seq sched 
  (@FP_to_JLFP Job Task H2 FP) j t1 t2 ->
is_true
  (@max_lp_nonpreemptive_segment Job Cost arr_seq (@FP_to_JLFP Job Task H2 FP) H4 j t1 <=
   @blocking_bound Task H1 FP ts tsk)

priority_inversion_is_bounded_by_blocking is not universe polymorphic
Arguments priority_inversion_is_bounded_by_blocking {Task H1 Job H2 Arrival Cost FP} 
  arr_seq sched {H4} H_valid_model_with_bounded_nonpreemptive_segments ts%seq_scope 
  H_all_jobs_from_taskset tsk j t1 t2 _ _ _
priority_inversion_is_bounded_by_blocking is opaque
Expands to: Constant prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded_by_blocking
Declared in library prosa.results.rta.ideal.fp.bounded_nps, line 118, characters 8-49
@priority_inversion_is_bounded_by_blocking
     : forall (Task : TaskType) (H1 : TaskMaxNonpreemptiveSegment Task) (Job : JobType)
         (H2 : JobTask Job Task) (Arrival : JobArrival Job) (Cost : JobCost Job) 
         (FP : FP_policy Task) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job (ideal.processor_state Job)) (H4 : JobPreemptable Job),
       @valid_model_with_bounded_nonpreemptive_segments Task Job H2 Cost H1 H4 (ideal.processor_state Job)
         arr_seq sched ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H2 arr_seq ts ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job) (t1 t2 : instant),
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H2 tsk j) ->
       @busy_interval_prefix Job Arrival Cost (ideal.processor_state Job) arr_seq sched
         (@FP_to_JLFP Job Task H2 FP) j t1 t2 ->
       is_true
         (@max_lp_nonpreemptive_segment Job Cost arr_seq (@FP_to_JLFP Job Task H2 FP) H4 j t1 <=
          @blocking_bound Task H1 FP ts tsk)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fp.BoundedNps.priority_inversion_is_bounded_by_blocking : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobArrival Job]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] [FP : Prosa.Model.Priority.Definitions.FP_policy Task]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  [inst_6 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
  Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq sched →
    ∀ (ts : List Task),
      Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
        ∀ (tsk : Task) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
            Prosa.Model.Task.Concept.job_of_task tsk j = true →
              Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
                Prosa.Analysis.Facts.BusyInterval.Pi.max_lp_nonpreemptive_segment arr_seq j t1 ≤
                  Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound ts tsk
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fp_BoundedNps_priority_inversion_is_bounded_by_blocking
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_7
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_7))
         (inst_32 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7),
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments_inst8 Task
         inst_3 Job
         inst_7
         inst_13
         inst_20
         inst_10
         inst_32
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_7
         inst_13 arr_seq ts ->
       forall (tsk : Task) (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_13 tsk j)
         Bool_true ->
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix_inst4 Job
         inst_7
         inst_17
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_7 Task
            inst_3
            inst_13 FP)
         j t1 t2 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job
            inst_7
            inst_20 arr_seq
            (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
               inst_7 Task
               inst_3
               inst_13 FP)
            inst_32 j t1)
         (Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task
            inst_3
            inst_10 FP ts tsk)
```
