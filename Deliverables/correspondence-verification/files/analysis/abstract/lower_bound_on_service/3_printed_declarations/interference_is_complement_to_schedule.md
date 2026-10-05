# `interference_is_complement_to_schedule`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.lower_bound_on_service.interference_is_complement_to_schedule`
- Lean: `Prosa.Analysis.Abstract.LowerBoundOnService.interference_is_complement_to_schedule`
- Certificate: `interference_is_complement_to_schedule_correspondence`

## Official Rocq

```coq
interference_is_complement_to_schedule :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {H2 : JobCost Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (tsk : Equality.sort Task) {H4 : Interference Job}
  {H5 : InterferingWorkload Job},
@work_conserving Job H1 H2 PState arr_seq sched H4 H5 ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) ->
is_true (@job_cost_positive Job H2 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H1 H2 PState sched H4 H5 j t1 t2 ->
forall (t : instant) (δ : duration),
is_true (t1 <= t) ->
is_true (t + δ <= t2) ->
is_true (δ <= @service_during Job PState sched j t (t + δ) + @cumulative_interference Job H4 j t (t + δ))

interference_is_complement_to_schedule is not universe polymorphic
Arguments interference_is_complement_to_schedule {Task Job H0 H1 H2 PState} arr_seq 
  sched tsk {H4 H5} H_work_conserving j H_j_arrives H_job_of_tsk H_job_cost_positive 
  t1 t2 H_busy_interval t δ H_t1_le_t H_tδ_le_t2
interference_is_complement_to_schedule is opaque
Expands to: Constant prosa.analysis.abstract.lower_bound_on_service.interference_is_complement_to_schedule
Declared in library prosa.analysis.abstract.lower_bound_on_service, line 73, characters 10-48
@interference_is_complement_to_schedule
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (H2 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (tsk : Equality.sort Task) (H4 : Interference Job)
         (H5 : InterferingWorkload Job),
       @work_conserving Job H1 H2 PState arr_seq sched H4 H5 ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H0 tsk j) ->
       is_true (@job_cost_positive Job H2 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H1 H2 PState sched H4 H5 j t1 t2 ->
       forall (t : instant) (δ : duration),
       is_true (t1 <= t) ->
       is_true (t + δ <= t2) ->
       is_true
         (δ <= @service_during Job PState sched j t (t + δ) + @cumulative_interference Job H4 j t (t + δ))
```

## Lean

```lean
@Prosa.Analysis.Abstract.LowerBoundOnService.interference_is_complement_to_schedule : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState) (tsk : Task)
  [inst_5 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_6 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
  Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Model.Task.Concept.job_of_task tsk j = true →
          Prosa.Model.Job.Properties.job_cost_positive j = true →
            ∀ (t1 t2 : Prosa.Behavior.Time.instant),
              Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2 →
                ∀ (t : Prosa.Behavior.Time.instant) (δ : Prosa.Behavior.Time.duration),
                  t1 ≤ t →
                    t + δ ≤ t2 →
                      δ ≤
                        Prosa.Behavior.Service.service_during sched j t (t + δ) +
                          Prosa.Analysis.Abstract.Definitions.cumulative_interference j t (t + δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_LowerBoundOnService_interference_is_complement_to_schedule
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
            inst_7),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_7
         inst_27
         inst_30
         inst_14
         inst_17 PState arr_seq
         sched ->
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
       Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
         inst_7
         inst_27
         inst_30
         inst_14
         inst_17 PState sched j t1
         t2 ->
       forall (t : Prosa_Behavior_Time_instant) (_UU03b4_ : Prosa_Behavior_Time_duration),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t _UU03b4_)
         t2 ->
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat _UU03b4_
         (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
            (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
            (Prosa_Behavior_Service_service_during Job
               inst_7 PState sched j
               t
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
                  _UU03b4_))
            (Prosa_Analysis_Abstract_Definitions_cumulative_interference Job
               inst_7
               inst_27 j t
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
                  _UU03b4_)))
```
