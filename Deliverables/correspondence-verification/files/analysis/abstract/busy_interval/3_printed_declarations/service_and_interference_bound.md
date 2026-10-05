# `service_and_interference_bound`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.busy_interval.service_and_interference_bound`
- Lean: `Prosa.Analysis.Abstract.BusyInterval.service_and_interference_bound`
- Certificate: `service_and_interference_bound_correspondence`

## Official Rocq

```coq
service_and_interference_bound :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job}
  {H3 : Interference Job} {H4 : InterferingWorkload Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState),
@work_conserving Job H1 H2 PState arr_seq sched H3 H4 ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H2 j) ->
forall t1 t2 : instant,
@busy_interval Job H1 H2 PState sched H3 H4 j t1 t2 ->
@unit_service_proc_model Job PState ->
forall Δ : nat,
is_true (t1 + Δ <= t2) ->
is_true (@service_during Job PState sched j t1 (t1 + Δ) + @cumulative_interference Job H3 j t1 (t1 + Δ) <= Δ)

service_and_interference_bound is not universe polymorphic
Arguments service_and_interference_bound {Job H1 H2 PState H3 H4} arr_seq sched H_work_conserving 
  j H_from_arrival_sequence H_job_cost_positive t1 t2 H_busy_interval H_unit_service_proc_model 
  Δ%nat_scope _
service_and_interference_bound is opaque
Expands to: Constant prosa.analysis.abstract.busy_interval.service_and_interference_bound
Declared in library prosa.analysis.abstract.busy_interval, line 190, characters 8-38
@service_and_interference_bound
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job)
         (H3 : Interference Job) (H4 : InterferingWorkload Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState),
       @work_conserving Job H1 H2 PState arr_seq sched H3 H4 ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H2 j) ->
       forall t1 t2 : instant,
       @busy_interval Job H1 H2 PState sched H3 H4 j t1 t2 ->
       @unit_service_proc_model Job PState ->
       forall Δ : nat,
       is_true (t1 + Δ <= t2) ->
       is_true
         (@service_during Job PState sched j t1 (t1 + Δ) + @cumulative_interference Job H3 j t1 (t1 + Δ) <= Δ)
```

## Lean

```lean
@Prosa.Analysis.Abstract.BusyInterval.service_and_interference_bound : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [inst_3 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_4 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Model.Job.Properties.job_cost_positive j = true →
          ∀ (t1 t2 : Prosa.Behavior.Time.instant),
            Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
              Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
                ∀ (Δ : ℕ),
                  t1 + Δ ≤ t2 →
                    Prosa.Behavior.Service.service_during sched j t1 (t1 + Δ) +
                        Prosa.Analysis.Abstract.Definitions.cumulative_interference j t1 (t1 + Δ) ≤
                      Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_BusyInterval_service_and_interference_bound
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (inst_14 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_17 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_3
         inst_14
         inst_17
         inst_6
         inst_9 PState arr_seq sched ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_14
         inst_17
         inst_6
         inst_9 PState sched j t1 t2 ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall _UU0394_ : Nat,
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
            (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)
         t2 ->
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
            (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
            (Prosa_Behavior_Service_service_during Job
               inst_3 PState sched j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                  (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_))
            (Prosa_Analysis_Abstract_Definitions_cumulative_interference Job
               inst_3
               inst_14 j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                  (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)))
         _UU0394_
```
