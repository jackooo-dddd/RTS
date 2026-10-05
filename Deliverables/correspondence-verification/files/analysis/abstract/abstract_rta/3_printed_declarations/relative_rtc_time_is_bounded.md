# `relative_rtc_time_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.abstract_rta.relative_rtc_time_is_bounded`
- Lean: `Prosa.Analysis.Abstract.AbstractRta.relative_rtc_time_is_bounded`
- Certificate: `relative_rtc_time_is_bounded_correspondence`

## Official Rocq

```coq
relative_rtc_time_is_bounded :
forall {Task : TaskType} {Job : JobType} {H1 : JobTask Job Task} {H2 : JobArrival Job} 
  {jc : JobCost Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (tsk : Equality.sort Task) {H3 : Interference Job}
  {H4 : InterferingWorkload Job} (L : duration),
@busy_intervals_are_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H3 H4 L ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H1 tsk j) ->
is_true (@job_cost_positive Job jc j) ->
forall t1 t2 : instant,
@busy_interval Job H2 jc PState sched H3 H4 j t1 t2 ->
forall F : duration, is_true (t1 + F < t2) -> is_true (F < L)

relative_rtc_time_is_bounded is not universe polymorphic
Arguments relative_rtc_time_is_bounded {Task Job H1 H2 jc PState} arr_seq sched tsk 
  {H3 H4} L H_bounded_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive 
  t1 t2 H_busy_interval F H_small_fixpoint_solution1
relative_rtc_time_is_bounded is opaque
Expands to: Constant prosa.analysis.abstract.abstract_rta.relative_rtc_time_is_bounded
Declared in library prosa.analysis.abstract.abstract_rta, line 350, characters 12-40
@relative_rtc_time_is_bounded
     : forall (Task : TaskType) (Job : JobType) (H1 : JobTask Job Task) (H2 : JobArrival Job)
         (jc : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (tsk : Equality.sort Task) (H3 : Interference Job)
         (H4 : InterferingWorkload Job) (L : duration),
       @busy_intervals_are_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H3 H4 L ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H1 tsk j) ->
       is_true (@job_cost_positive Job jc j) ->
       forall t1 t2 : instant,
       @busy_interval Job H2 jc PState sched H3 H4 j t1 t2 ->
       forall F : duration, is_true (t1 + F < t2) -> is_true (F < L)
```

## Lean

```lean
@Prosa.Analysis.Abstract.AbstractRta.relative_rtc_time_is_bounded : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  (tsk : Task) [inst_5 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_6 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] (L : Prosa.Behavior.Time.duration),
  Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by arr_seq sched tsk L →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Model.Task.Concept.job_of_task tsk j = true →
          Prosa.Model.Job.Properties.job_cost_positive j = true →
            ∀ (t1 t2 : Prosa.Behavior.Time.instant),
              Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
                ∀ (F : Prosa.Behavior.Time.duration), t1 + F < t2 → F < L
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_AbstractRta_relative_rtc_time_is_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (tsk : Task)
         (inst_27 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_7)
         (inst_30 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_7)
         (L : Prosa_Behavior_Time_duration),
       Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by Job
         inst_7
         inst_27
         inst_30
         inst_14
         inst_17 PState arr_seq sched Task
         inst_3
         inst_10 tsk L ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_17 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_7
         inst_27
         inst_30
         inst_14
         inst_17 PState sched j t1 t2 ->
       forall F : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 F)
         t2 ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat F L
```
