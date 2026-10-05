# `cumulative_interference_sub`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.iw_auxiliary.cumulative_interference_sub`
- Lean: `Prosa.Analysis.Abstract.IwAuxiliary.cumulative_interference_sub`
- Certificate: `cumulative_interference_sub_correspondence`

## Official Rocq

```coq
cumulative_interference_sub :
forall {Job : JobType} {H3 : Interference Job} (P : Equality.sort Job -> instant -> bool)
  (j : Equality.sort Job) (al ar bl br : instant),
is_true (bl <= al) ->
is_true (ar <= br) ->
is_true (@cumul_cond_interference Job H3 P j al ar <= @cumul_cond_interference Job H3 P j bl br)

cumulative_interference_sub is not universe polymorphic
Arguments cumulative_interference_sub {Job H3} P%function_scope j al ar bl br _ _
cumulative_interference_sub is opaque
Expands to: Constant prosa.analysis.abstract.iw_auxiliary.cumulative_interference_sub
Declared in library prosa.analysis.abstract.iw_auxiliary, line 83, characters 10-37
@cumulative_interference_sub
     : forall (Job : JobType) (H3 : Interference Job) (P : Equality.sort Job -> instant -> bool)
         (j : Equality.sort Job) (al ar bl br : instant),
       is_true (bl <= al) ->
       is_true (ar <= br) ->
       is_true (@cumul_cond_interference Job H3 P j al ar <= @cumul_cond_interference Job H3 P j bl br)
```

## Lean

```lean
@Prosa.Analysis.Abstract.IwAuxiliary.cumulative_interference_sub : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  (P : Job → Prosa.Behavior.Time.instant → Bool) (j : Job) (al ar bl br : Prosa.Behavior.Time.instant),
  bl ≤ al →
    ar ≤ br →
      Prosa.Analysis.Abstract.Definitions.cumul_cond_interference P j al ar ≤
        Prosa.Analysis.Abstract.Definitions.cumul_cond_interference P j bl br
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IwAuxiliary_cumulative_interference_sub
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (P : Job -> Prosa_Behavior_Time_instant -> Bool) (j : Job)
         (al ar bl br : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat bl al ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat ar br ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
            inst_3
            inst_6 P j al ar)
         (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
            inst_3
            inst_6 P j bl br)
```
