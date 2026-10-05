# `no_progress_equiv`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.definitions.progress.no_progress_equiv`
- Lean: `Prosa.Analysis.Definitions.Progress.no_progress_equiv`
- Certificate: `no_progress_equiv_correspondence`

## Official Rocq

```coq
no_progress_equiv :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : nat),
is_true (t1 <= t2) ->
is_true (~~ @job_has_progressed Job PState sched j t1 t2) <-> is_true (@no_progress Job PState sched j t1 t2)

no_progress_equiv is not universe polymorphic
Arguments no_progress_equiv {Job PState} sched j (t1 t2)%nat_scope H_t1_before_t2
no_progress_equiv is opaque
Expands to: Constant prosa.analysis.definitions.progress.no_progress_equiv
Declared in library prosa.analysis.definitions.progress, line 37, characters 10-27
@no_progress_equiv
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : nat),
       is_true (t1 <= t2) ->
       is_true (~~ @job_has_progressed Job PState sched j t1 t2) <->
       is_true (@no_progress Job PState sched j t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Definitions.Progress.no_progress_equiv : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t1 t2 : ℕ),
  t1 ≤ t2 →
    ((!Prosa.Analysis.Definitions.Progress.job_has_progressed sched j t1 t2) = true ↔
      Prosa.Analysis.Definitions.Progress.no_progress sched j t1 t2 = true)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Progress_no_progress_equiv
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Nat),
       LE_le_inst1 Nat instLENat t1 t2 ->
       Iff
         (@eq Bool
            (Bool_not
               (Prosa_Analysis_Definitions_Progress_job_has_progressed Job
                  inst_3 PState sched j t1
                  t2))
            Bool_true)
         (@eq Bool
            (Prosa_Analysis_Definitions_Progress_no_progress Job
               inst_3 PState sched j t1 t2)
            Bool_true)
```
