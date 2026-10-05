# `interference_and_service_eq_1`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.abstract.IBF.task.interference_and_service_eq_1`
- Lean: `Prosa.Analysis.Abstract.IBF.Task.interference_and_service_eq_1`
- Certificate: `interference_and_service_eq_1_correspondence`

## Official Rocq

```coq
interference_and_service_eq_1 :
forall {Job : JobType} {H1 : JobArrival Job} {jc : JobCost Job} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) {H3 : Interference Job}
  {H4 : InterferingWorkload Job},
@work_conserving Job H1 jc PState arr_seq sched H3 H4 ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job jc j) ->
forall t1 t2 : instant,
@busy_interval Job H1 jc PState sched H3 H4 j t1 t2 ->
forall x : duration,
is_true (t1 + x < t2) ->
forall t : instant,
is_true (t1 <= t < t1 + x) -> nat_of_bool (@interference Job H3 j t) + @service_at Job PState sched j t = 1

interference_and_service_eq_1 is not universe polymorphic
Arguments interference_and_service_eq_1 {Job H1 jc PState} H_unit_service_proc_model 
  arr_seq sched {H3 H4} H_work_conserving j H_j_arrives H_job_cost_positive t1 t2 
  H_busy_interval x H_inside_busy_interval t H_t_in_interval
interference_and_service_eq_1 is opaque
Expands to: Constant prosa.analysis.abstract.IBF.task.interference_and_service_eq_1
Declared in library prosa.analysis.abstract.IBF.task, line 406, characters 13-42
@interference_and_service_eq_1
     : forall (Job : JobType) (H1 : JobArrival Job) (jc : JobCost Job) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (H3 : Interference Job)
         (H4 : InterferingWorkload Job),
       @work_conserving Job H1 jc PState arr_seq sched H3 H4 ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job jc j) ->
       forall t1 t2 : instant,
       @busy_interval Job H1 jc PState sched H3 H4 j t1 t2 ->
       forall x : duration,
       is_true (t1 + x < t2) ->
       forall t : instant,
       is_true (t1 <= t < t1 + x) ->
       nat_of_bool (@interference Job H3 j t) + @service_at Job PState sched j t = 1
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Task.interference_and_service_eq_1 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
      [inst_3 : Prosa.Analysis.Abstract.Definitions.Interference Job]
      [inst_4 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
      Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
        ∀ (j : Job),
          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
            Prosa.Model.Job.Properties.job_cost_positive j = true →
              ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
                  ∀ (x : Prosa.Behavior.Time.duration),
                    t1 + x < t2 →
                      ∀ (t : Prosa.Behavior.Time.instant),
                        (decide (t1 ≤ t) && decide (t < t1 + x)) = true →
                          (Prosa.Analysis.Abstract.Definitions.interference j t).toNat +
                              Prosa.Behavior.Service.service_at sched j t =
                            1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Task_interference_and_service_eq_1
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_13 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (inst_27 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_30 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_3
         inst_27
         inst_30
         inst_10
         inst_13 PState arr_seq sched ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_13 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_27
         inst_30
         inst_10
         inst_13 PState sched j t1 t2 ->
       forall x : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x)
         t2 ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide
               (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x))
               (Nat_decLt t
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x))))
         Bool_true ->
       @eq Nat
         (HAdd_hAdd_inst7 Nat Prosa_Behavior_Job_work Nat (instHAdd_inst1 Nat instAddNat)
            (Bool_toNat
               (Prosa_Analysis_Abstract_Definitions_Interference_interference Job
                  inst_3
                  inst_27 j t))
            (Prosa_Behavior_Service_service_at Job
               inst_3 PState sched j t))
         (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
```
