# `nonpreemptive_segments_bounded_by_blocking`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.blocking_bound.fp.nonpreemptive_segments_bounded_by_blocking`
- Lean: `Prosa.Analysis.Facts.BlockingBound.Fp.nonpreemptive_segments_bounded_by_blocking`
- Certificate: `nonpreemptive_segments_bounded_by_blocking_correspondence`

## Official Rocq

```coq
nonpreemptive_segments_bounded_by_blocking :
forall {Task : TaskType} {H0 : TaskMaxNonpreemptiveSegment Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H2 : JobCost Job} {PState : ProcessorState Job} {FP : FP_policy Task}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) {H3 : JobPreemptable Job},
@valid_model_with_bounded_nonpreemptive_segments Task Job H1 H2 H0 H3 PState arr_seq sched ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H1 arr_seq ts ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job),
is_true (@job_of_task Job Task H1 tsk j) ->
forall t : instant,
is_true
  (@max_lp_nonpreemptive_segment Job H2 arr_seq (@FP_to_JLFP Job Task H1 FP) H3 j t <=
   @blocking_bound Task H0 FP ts tsk)

nonpreemptive_segments_bounded_by_blocking is not universe polymorphic
Arguments nonpreemptive_segments_bounded_by_blocking {Task H0 Job H1 H2 PState FP} 
  arr_seq sched {H3} H_valid_model_with_bounded_nonpreemptive_segments ts%seq_scope 
  H_all_jobs_from_taskset tsk j H_job_of_tsk t
nonpreemptive_segments_bounded_by_blocking is opaque
Expands to: Constant prosa.analysis.facts.blocking_bound.fp.nonpreemptive_segments_bounded_by_blocking
Declared in library prosa.analysis.facts.blocking_bound.fp, line 60, characters 8-50
@nonpreemptive_segments_bounded_by_blocking
     : forall (Task : TaskType) (H0 : TaskMaxNonpreemptiveSegment Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobCost Job) (PState : ProcessorState Job) 
         (FP : FP_policy Task) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
         (H3 : JobPreemptable Job),
       @valid_model_with_bounded_nonpreemptive_segments Task Job H1 H2 H0 H3 PState arr_seq sched ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H1 arr_seq ts ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job),
       is_true (@job_of_task Job Task H1 tsk j) ->
       forall t : instant,
       is_true
         (@max_lp_nonpreemptive_segment Job H2 arr_seq (@FP_to_JLFP Job Task H1 FP) H3 j t <=
          @blocking_bound Task H0 FP ts tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.BlockingBound.Fp.nonpreemptive_segments_bounded_by_blocking : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (FP : Prosa.Model.Priority.Definitions.FP_policy Task)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  [inst_5 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
  Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq sched →
    ∀ (ts : List Task),
      Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
        ∀ (tsk : Task) (j : Job),
          Prosa.Model.Task.Concept.job_of_task tsk j = true →
            ∀ (t : Prosa.Behavior.Time.instant),
              Prosa.Analysis.Facts.BusyInterval.Pi.max_lp_nonpreemptive_segment arr_seq j t ≤
                Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound ts tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BlockingBound_Fp_nonpreemptive_segments_bounded_by_blocking
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_7)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (inst_28 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3),
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_7 Job
         inst_3
         inst_13
         inst_17
         inst_10
         inst_28 PState arr_seq sched ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_7 Job
         inst_3
         inst_13 arr_seq ts ->
       forall (tsk : Task) (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_3 Task
            inst_7
            inst_13 tsk j)
         Bool_true ->
       forall t : Prosa_Behavior_Time_instant,
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job
            inst_3
            inst_17 arr_seq
            (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
               inst_3 Task
               inst_7
               inst_13 FP)
            inst_28 j t)
         (Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task
            inst_7
            inst_10 FP ts tsk)
```
