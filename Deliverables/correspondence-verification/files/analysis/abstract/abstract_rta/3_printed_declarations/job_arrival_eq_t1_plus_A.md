# `job_arrival_eq_t1_plus_A`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.abstract.abstract_rta.job_arrival_eq_t1_plus_A`
- Lean: `Prosa.Analysis.Abstract.AbstractRta.job_arrival_eq_t1_plus_A`
- Certificate: `job_arrival_eq_t1_plus_A_correspondence`

## Official Rocq

```coq
job_arrival_eq_t1_plus_A :
forall {Job : JobType} {H2 : JobArrival Job} {jc : JobCost Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) {H3 : Interference Job} {H4 : InterferingWorkload Job}
  (j : Equality.sort Job) (t1 t2 : instant),
@busy_interval Job H2 jc PState sched H3 H4 j t1 t2 ->
@job_arrival Job H2 j = t1 + (@job_arrival Job H2 j - t1)

job_arrival_eq_t1_plus_A is not universe polymorphic
Arguments job_arrival_eq_t1_plus_A {Job H2 jc PState} sched {H3 H4} j t1 t2 H_busy_interval
job_arrival_eq_t1_plus_A is opaque
Expands to: Constant prosa.analysis.abstract.abstract_rta.job_arrival_eq_t1_plus_A
Declared in library prosa.analysis.abstract.abstract_rta, line 208, characters 9-33
@job_arrival_eq_t1_plus_A
     : forall (Job : JobType) (H2 : JobArrival Job) (jc : JobCost Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (H3 : Interference Job) (H4 : InterferingWorkload Job)
         (j : Equality.sort Job) (t1 t2 : instant),
       @busy_interval Job H2 jc PState sched H3 H4 j t1 t2 ->
       @job_arrival Job H2 j = t1 + (@job_arrival Job H2 j - t1)
```

## Lean

```lean
@Prosa.Analysis.Abstract.AbstractRta.job_arrival_eq_t1_plus_A : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
  [inst_3 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_4 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] (j : Job)
  (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
    Prosa.Behavior.Job.job_arrival j = t1 + (Prosa.Behavior.Job.job_arrival j - t1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_AbstractRta_job_arrival_eq_t1_plus_A
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
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_16
         inst_19
         inst_6
         inst_9 PState sched j t1 t2 ->
       @eq Prosa_Behavior_Time_instant
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j)
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
            (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
            (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_3
                  inst_6 j)
               t1))
```
