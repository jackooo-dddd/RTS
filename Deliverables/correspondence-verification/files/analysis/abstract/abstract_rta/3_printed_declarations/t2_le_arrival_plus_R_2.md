# `t2_le_arrival_plus_R_2`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.abstract_rta.t2_le_arrival_plus_R_2`
- Lean: `Prosa.Analysis.Abstract.AbstractRta.t2_le_arrival_plus_R_2`
- Certificate: `t2_le_arrival_plus_R_2_correspondence`

## Official Rocq

```coq
t2_le_arrival_plus_R_2 :
forall {Job : JobType} {H2 : JobArrival Job} {jc : JobCost Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) {H3 : Interference Job} {H4 : InterferingWorkload Job} 
  (R : duration) (j : Equality.sort Job) (t1 t2 : instant),
@busy_interval Job H2 jc PState sched H3 H4 j t1 t2 ->
forall A_sp : duration,
is_true (A_sp <= @job_arrival Job H2 j - t1) ->
is_true (t2 <= t1 + (A_sp + R)) -> is_true (t2 <= @job_arrival Job H2 j + R)

t2_le_arrival_plus_R_2 is not universe polymorphic
Arguments t2_le_arrival_plus_R_2 {Job H2 jc PState} sched {H3 H4} R j t1 t2 H_busy_interval 
  A_sp H_Asp_le_A H_big_fixpoint_solution
t2_le_arrival_plus_R_2 is opaque
Expands to: Constant prosa.analysis.abstract.abstract_rta.t2_le_arrival_plus_R_2
Declared in library prosa.analysis.abstract.abstract_rta, line 317, characters 12-34
@t2_le_arrival_plus_R_2
     : forall (Job : JobType) (H2 : JobArrival Job) (jc : JobCost Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (H3 : Interference Job) (H4 : InterferingWorkload Job) 
         (R : duration) (j : Equality.sort Job) (t1 t2 : instant),
       @busy_interval Job H2 jc PState sched H3 H4 j t1 t2 ->
       forall A_sp : duration,
       is_true (A_sp <= @job_arrival Job H2 j - t1) ->
       is_true (t2 <= t1 + (A_sp + R)) -> is_true (t2 <= @job_arrival Job H2 j + R)
```

## Lean

```lean
@Prosa.Analysis.Abstract.AbstractRta.t2_le_arrival_plus_R_2 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
  [inst_3 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_4 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] (R : Prosa.Behavior.Time.duration) (j : Job)
  (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
    ∀ A_sp ≤ Prosa.Behavior.Job.job_arrival j - t1, t2 ≤ t1 + (A_sp + R) → t2 ≤ Prosa.Behavior.Job.job_arrival j + R
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_AbstractRta_t2_le_arrival_plus_R_2
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
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (inst_16 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_19 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3)
         (R : Prosa_Behavior_Time_duration) (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_16
         inst_19
         inst_6
         inst_9 PState sched j t1 t2 ->
       forall A_sp : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat A_sp
         (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
            (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
            (Prosa_Behavior_Job_JobArrival_job_arrival Job
               inst_3
               inst_6 j)
            t1) ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t2
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A_sp R)) ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t2
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
            (Prosa_Behavior_Job_JobArrival_job_arrival Job
               inst_3
               inst_6 j)
            R)
```
