# `jitter_ready_to_execute`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.jitter.jitter_ready_to_execute`
- Lean: `Prosa.Analysis.Facts.Jitter.jitter_ready_to_execute`
- Certificate: `jitter_ready_to_execute_correspondence`

## Official Rocq

```coq
jitter_ready_to_execute :
forall {Job : JobType} {original_arrival : JobArrival Job} {H1 : JobJitter Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) {H2 : JobCost Job},
@jobs_must_be_ready_to_execute Job original_arrival PState sched H2
  (@jitter_ready_instance Job PState original_arrival H2 H1) ->
@jobs_must_be_ready_to_execute Job (@release_as_arrival Job original_arrival H1) PState sched H2
  (@basic_ready_instance Job PState (@release_as_arrival Job original_arrival H1) H2)

jitter_ready_to_execute is not universe polymorphic
Arguments jitter_ready_to_execute {Job original_arrival H1 PState} sched {H2} _ j t _
jitter_ready_to_execute is opaque
Expands to: Constant prosa.analysis.facts.jitter.jitter_ready_to_execute
Declared in library prosa.analysis.facts.jitter, line 130, characters 8-31
@jitter_ready_to_execute
     : forall (Job : JobType) (original_arrival : JobArrival Job) (H1 : JobJitter Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (H2 : JobCost Job),
       @jobs_must_be_ready_to_execute Job original_arrival PState sched H2
         (@jitter_ready_instance Job PState original_arrival H2 H1) ->
       @jobs_must_be_ready_to_execute Job (@release_as_arrival Job original_arrival H1) PState sched H2
         (@basic_ready_instance Job PState (@release_as_arrival Job original_arrival H1) H2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Jitter.jitter_ready_to_execute : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  (original_arrival : Prosa.Behavior.Job.JobArrival Job) [inst_1 : Prosa.Model.Readiness.Jitter.JobJitter Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
  [inst_2 : Prosa.Behavior.Job.JobCost Job],
  Prosa.Behavior.Ready.jobs_must_be_ready_to_execute sched → Prosa.Behavior.Ready.jobs_must_be_ready_to_execute sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Jitter_jitter_ready_to_execute
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (original_arrival : Prosa_Behavior_Job_JobArrival Job
                               inst_7)
         (inst_12 : Prosa_Model_Readiness_Jitter_JobJitter
                                                                                Job
                                                                                inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (inst_19 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_7),
       Prosa_Behavior_Ready_jobs_must_be_ready_to_execute Job
         inst_7 original_arrival PState sched
         inst_19
         (Prosa_Model_Readiness_Jitter_jitter_ready_instance Job
            inst_7 original_arrival
            inst_12 PState
            inst_19) ->
       Prosa_Behavior_Ready_jobs_must_be_ready_to_execute Job
         inst_7
         (Prosa_Analysis_Facts_Jitter_release_as_arrival Job
            inst_7 original_arrival
            inst_12)
         PState sched inst_19
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_7 PState
            (Prosa_Analysis_Facts_Jitter_release_as_arrival Job
               inst_7 original_arrival
               inst_12)
            inst_19)
```
