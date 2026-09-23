# Service.lean → Rocq import inspection

Started: 2026-09-23 23:01 (Asia/Hong_Kong). This is an inspection, not a new semantic certificate or acceptance run.

## 2026-09-23 23:06 — fresh build in progress

The inspected production source is `Prosa/Behavior/Service.lean`, SHA-256 `14ba43ed3710f97daaf5183ce558a205843ed3057378878fee5af572c9aa2450`. An isolated `CLEAN_FULL=1 Validation/scripts/validate_behavior_service.sh prepare` run was started; its run log is `Validation/logs/incremental/behavior_service/prepare_20260923_230149_+0800_bbfd9898a550/`. At this timestamp the dependency-closure Lean build is still running. No fresh `Service.olean`/export/import result is claimed yet.

The production `Service.lean` contains definitions but no theorem or lemma declaration. The inspection will print its actual imported definitions (including `service_at`, `service`, `completed_by`, and `completes_at`) and report this absence explicitly rather than inventing a Service theorem.

An inspection-only raw export config, [`service_raw_export_config.json`](service_raw_export_config.json), requests the compiled definition bodies without normalization or body projection. If raw export/import proves infeasible, any guarded projection fallback will be identified as such, with its exact guard boundary.

## 2026-09-23 23:10 — fresh Service compile completed

The isolated run completed fresh Lean compilation of `Prosa.Behavior.Service` (module timing record: 60.466 s, mode `FRESH`, status `PASS`). Its `.olean` currently lives at `Validation/.work/runs/incremental_behavior_service_prepare.XgWkrh/olean/Prosa/Behavior/Service.olean`, SHA-256 `586d36878254e71e082b1f8772c29f41475f0f5d8567cf1891b6b124d9761758`. This path is a temporary run artifact, not a published result. Rocq source/export/import stages are still in progress; their statuses remain pending.

## 2026-09-23 23:14 — complete fresh chain passed

The same isolated `CLEAN_FULL` prepare run exited `0`; snapshot ID `bbfd9898a550b2400dfa685e722a5fa0d118fc104290cf64e7d98c434ea4817c`, prepared root `Validation/.work/runs/incremental_behavior_service_prepare.XgWkrh/`. Its stage evidence records fresh Lean build (590.866 s), source acquisition (7.575 s), export (49.793 s), and a successful Rocq import. Artifact hashes:

| Stage | Actual artifact | SHA-256 |
| --- | --- | --- |
| source | `Prosa/Behavior/Service.lean` | `14ba43ed3710f97daaf5183ce558a205843ed3057378878fee5af572c9aa2450` |
| fresh compile | `Validation/.work/runs/incremental_behavior_service_prepare.XgWkrh/olean/Prosa/Behavior/Service.olean` | `586d36878254e71e082b1f8772c29f41475f0f5d8567cf1891b6b124d9761758` |
| guarded export | `Validation/.work/runs/incremental_behavior_service_prepare.XgWkrh/imported/Service.out` | `0a2c7cc1aa038fa4a0e8ec80a165d3995c7e14a06ac7d0a02c8831c45873c687` |
| Rocq import | `Validation/.work/runs/incremental_behavior_service_prepare.XgWkrh/imported/ImportedService.vo` | `c1d2a445d8c6fdb7fa06e1771896c8e00f2d710feb2bdbca8ee7727281c20695` |

The validator's normal export uses kernel-guarded body projections from `behavior_service_export_config.json`; it must not be described as a literal unprojected body print. A separate raw-body inspection export from this exact fresh `.olean` is now in progress. No translation, certificate, or validator file has been edited for this inspection.

## Fresh imported names and Rocq interpretation

Exact imported names below were confirmed by compiling [`ServiceImportInspection.v`](ServiceImportInspection.v) against this run's `ImportedService.vo`, not inferred from Lean spelling alone. `Set Printing All` was active throughout. The full unedited stdout is included below and saved independently as `Validation/logs/inspection/service_guarded_printcheck.stdout` (SHA-256 `707f674e9fbd00bdb0ad6805fbd70b33df0f6d458832ae6b3afb5daa69b13561`); inspection compilation exited `0`.

| Lean declaration | Imported Rocq declaration | Exact type/body observation |
| --- | --- | --- |
| `Prosa.Behavior.Job.work` | `ImportedService.Prosa_Behavior_Job_work` | Type alias: `Nat : Type`. |
| `Prosa.Behavior.Service.scheduled_at` | `ImportedService.Prosa_Behavior_Service_scheduled_at` | `Job`, `DecidableEq Job`, `ProcessorState`, schedule, job, instant → imported `Bool`; body calls `ProcessorState_scheduled_in` on `sched t`. |
| `Prosa.Behavior.Service.service_at` | `ImportedService.Prosa_Behavior_Service_service_at` | Same base parameters → imported `work`; body calls `ProcessorState_service_in` on `sched t`. |
| `Prosa.Behavior.Service.service_during` | `ImportedService.Prosa_Behavior_Service_service_during` | Adds `t1 t2 : instant` → `work`; inspected guarded projection is a `List.foldr Nat_add` of mapped per-instant service over `List.range' t1 (t2 - t1)`. |
| `Prosa.Behavior.Service.service` | `ImportedService.Prosa_Behavior_Service_service` | Job and instant → `work`; inspected guarded body calls `serviceDuringProjection` from zero to `t`. |
| `Prosa.Behavior.Service.completed_by` | `ImportedService.Prosa_Behavior_Service_completed_by` | Adds `JobCost Job` → `Bool`; guarded body is `Decidable_decide (job_cost j ≤ serviceProjection sched j t)`. |
| `Prosa.Behavior.Service.completes_at` | `ImportedService.Prosa_Behavior_Service_completes_at` | Same parameters → `Bool`; guarded body has `(! completedByProjection (t − 1) || decide (t = 0)) && completedByProjection t`. The explicit zero-time disjunct is visible. |

The `JobType`, `ProcessorState`, `schedule`, `instant`, `work`, `Bool`, `DecidableEq`, and `JobCost` shown here are imported Lean representations in Rocq; they are **not** Rocq's original Prosa constants simply because the names look similar. `Service.lean` has no production theorem declaration, so this inspection does not fabricate one. The guarded projection functions are validation-only helpers whose definitional-equality guards are compiled in the same fresh Lean run; the printed bodies are not claimed to be the literal unprojected compiled bodies.

### Complete raw `Check` / `Print` output

The order is exactly the order of commands in `ServiceImportInspection.v`:

```text
ImportedService.Prosa_Behavior_Job_work
     : Type
ImportedService.Prosa_Behavior_Job_work@{} = Nat
     : Type
ImportedService.Prosa_Behavior_Service_scheduled_at
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst____at___Prosa_Behavior_Service3949817776__hygCtx__hyg3 : 
          ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst____at___Prosa_Behavior_Service3949817776__hygCtx__hyg3)
         (_ : ImportedService.Prosa_Behavior_Schedule_schedule Job
                inst____at___Prosa_Behavior_Service3949817776__hygCtx__hyg3
                PState)
         (_ : Job) (_ : ImportedService.Prosa_Behavior_Time_instant),
       ImportedService.Bool
ImportedService.Prosa_Behavior_Service_scheduled_at@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0
Lean.u_3+2.0} =
fun (Job : ImportedService.Prosa_Behavior_Job_JobType)
  (inst____at___Validation_fixtures_translation_order_ServiceComputationInterface1815056986__hygCtx__hyg9 : 
   ImportedService.DecidableEq Job)
  (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
              inst____at___Validation_fixtures_translation_order_ServiceComputationInterface1815056986__hygCtx__hyg9)
  (sched : ImportedService.Prosa_Behavior_Schedule_schedule Job
             inst____at___Validation_fixtures_translation_order_ServiceComputationInterface1815056986__hygCtx__hyg9
             PState)
  (j : Job) (t : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job
  inst____at___Validation_fixtures_translation_order_ServiceComputationInterface1815056986__hygCtx__hyg9
  PState j (sched t)
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst____at___Prosa_Behavior_Service3949817776__hygCtx__hyg3 : 
          ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst____at___Prosa_Behavior_Service3949817776__hygCtx__hyg3)
         (_ : ImportedService.Prosa_Behavior_Schedule_schedule Job
                inst____at___Prosa_Behavior_Service3949817776__hygCtx__hyg3
                PState)
         (_ : Job) (_ : ImportedService.Prosa_Behavior_Time_instant),
       ImportedService.Bool

Arguments ImportedService.Prosa_Behavior_Service_scheduled_at 
  Job inst____at___Prosa_Behavior_Service3949817776__hygCtx__hyg3 
  PState sched j t
ImportedService.Prosa_Behavior_Service_service_at
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3 : 
          ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3)
         (_ : ImportedService.Prosa_Behavior_Schedule_schedule Job
                inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3
                PState)
         (_ : Job) (_ : ImportedService.Prosa_Behavior_Time_instant),
       ImportedService.Prosa_Behavior_Job_work
ImportedService.Prosa_Behavior_Service_service_at@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0
Lean.u_3+2.0} =
fun (Job : ImportedService.Prosa_Behavior_Job_JobType)
  (inst____at___Validation_fixtures_translation_order_ServiceComputationInterface983300830__hygCtx__hyg9 : 
   ImportedService.DecidableEq Job)
  (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
              inst____at___Validation_fixtures_translation_order_ServiceComputationInterface983300830__hygCtx__hyg9)
  (sched : ImportedService.Prosa_Behavior_Schedule_schedule Job
             inst____at___Validation_fixtures_translation_order_ServiceComputationInterface983300830__hygCtx__hyg9
             PState)
  (j : Job) (t : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.Prosa_Behavior_Schedule_ProcessorState_service_in Job
  inst____at___Validation_fixtures_translation_order_ServiceComputationInterface983300830__hygCtx__hyg9
  PState j (sched t)
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3 : 
          ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3)
         (_ : ImportedService.Prosa_Behavior_Schedule_schedule Job
                inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3
                PState)
         (_ : Job) (_ : ImportedService.Prosa_Behavior_Time_instant),
       ImportedService.Prosa_Behavior_Job_work

Arguments ImportedService.Prosa_Behavior_Service_service_at 
  Job inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3 
  PState sched j t
ImportedService.Prosa_Behavior_Service_service_during
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst____at___Prosa_Behavior_Service4118849154__hygCtx__hyg3 : 
          ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst____at___Prosa_Behavior_Service4118849154__hygCtx__hyg3)
         (_ : ImportedService.Prosa_Behavior_Schedule_schedule Job
                inst____at___Prosa_Behavior_Service4118849154__hygCtx__hyg3
                PState)
         (_ : Job) (_ : ImportedService.Prosa_Behavior_Time_instant)
         (_ : ImportedService.Prosa_Behavior_Time_instant),
       ImportedService.Prosa_Behavior_Job_work
ImportedService.Prosa_Behavior_Service_service_during@{u_1 u_2 u_3
Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0
Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedService.Prosa_Behavior_Job_JobType)
  (inst____at___Validation_fixtures_translation_order_ServiceComputationInterface575646449__hygCtx__hyg9 : 
   ImportedService.DecidableEq Job)
  (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
              inst____at___Validation_fixtures_translation_order_ServiceComputationInterface575646449__hygCtx__hyg9)
  (sched : ImportedService.Prosa_Behavior_Schedule_schedule Job
             inst____at___Validation_fixtures_translation_order_ServiceComputationInterface575646449__hygCtx__hyg9
             PState)
  (j : Job) (t1 t2 : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.List_foldr_inst3 Nat ImportedService.Prosa_Behavior_Job_work
  Nat_add
  (ImportedService.OfNat_ofNat_inst1 ImportedService.Prosa_Behavior_Job_work
     Nat_zero (ImportedService.instOfNatNat Nat_zero))
  (ImportedService.List_map_inst3 ImportedService.Prosa_Behavior_Time_instant
     Nat
     (fun t : ImportedService.Prosa_Behavior_Time_instant =>
      ImportedService.Prosa_Validation_ServiceInterface_serviceAtProjection
        Job
        inst____at___Validation_fixtures_translation_order_ServiceComputationInterface575646449__hygCtx__hyg9
        PState sched j t)
     (ImportedService.List_range' t1
        (ImportedService.HSub_hSub_inst7
           ImportedService.Prosa_Behavior_Time_instant
           ImportedService.Prosa_Behavior_Time_instant
           ImportedService.Prosa_Behavior_Time_instant
           (ImportedService.instHSub_inst1
              ImportedService.Prosa_Behavior_Time_instant
              ImportedService.instSubNat)
           t2 t1)
        (ImportedService.OfNat_ofNat_inst1 Nat (Nat_succ Nat_zero)
           (ImportedService.instOfNatNat (Nat_succ Nat_zero)))))
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst____at___Prosa_Behavior_Service4118849154__hygCtx__hyg3 : 
          ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst____at___Prosa_Behavior_Service4118849154__hygCtx__hyg3)
         (_ : ImportedService.Prosa_Behavior_Schedule_schedule Job
                inst____at___Prosa_Behavior_Service4118849154__hygCtx__hyg3
                PState)
         (_ : Job) (_ : ImportedService.Prosa_Behavior_Time_instant)
         (_ : ImportedService.Prosa_Behavior_Time_instant),
       ImportedService.Prosa_Behavior_Job_work

Arguments ImportedService.Prosa_Behavior_Service_service_during 
  Job inst____at___Prosa_Behavior_Service4118849154__hygCtx__hyg3 
  PState sched j t1 t
ImportedService.Prosa_Behavior_Service_service
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3 : 
          ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3)
         (_ : ImportedService.Prosa_Behavior_Schedule_schedule Job
                inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3
                PState)
         (_ : Job) (_ : ImportedService.Prosa_Behavior_Time_instant),
       ImportedService.Prosa_Behavior_Job_work
ImportedService.Prosa_Behavior_Service_service@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0
Lean.u_3+2.0} =
fun (Job : ImportedService.Prosa_Behavior_Job_JobType)
  (inst____at___Validation_fixtures_translation_order_ServiceComputationInterface995521427__hygCtx__hyg9 : 
   ImportedService.DecidableEq Job)
  (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
              inst____at___Validation_fixtures_translation_order_ServiceComputationInterface995521427__hygCtx__hyg9)
  (sched : ImportedService.Prosa_Behavior_Schedule_schedule Job
             inst____at___Validation_fixtures_translation_order_ServiceComputationInterface995521427__hygCtx__hyg9
             PState)
  (j : Job) (t : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.Prosa_Validation_ServiceInterface_serviceDuringProjection Job
  inst____at___Validation_fixtures_translation_order_ServiceComputationInterface995521427__hygCtx__hyg9
  PState sched j
  (ImportedService.OfNat_ofNat_inst1
     ImportedService.Prosa_Behavior_Time_instant Nat_zero
     (ImportedService.instOfNatNat Nat_zero))
  t
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3 : 
          ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3)
         (_ : ImportedService.Prosa_Behavior_Schedule_schedule Job
                inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3
                PState)
         (_ : Job) (_ : ImportedService.Prosa_Behavior_Time_instant),
       ImportedService.Prosa_Behavior_Job_work

Arguments ImportedService.Prosa_Behavior_Service_service 
  Job inst____at___Prosa_Behavior_Service817721511__hygCtx__hyg3 
  PState sched j t
ImportedService.Prosa_Behavior_Service_completed_by
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3 : 
          ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3)
         (_ : ImportedService.Prosa_Behavior_Schedule_schedule Job
                inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3
                PState)
         (_ : ImportedService.Prosa_Behavior_Job_JobCost Job
                inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3)
         (_ : Job) (_ : ImportedService.Prosa_Behavior_Time_instant),
       ImportedService.Bool
ImportedService.Prosa_Behavior_Service_completed_by@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0
Lean.u_3+2.0} =
fun (Job : ImportedService.Prosa_Behavior_Job_JobType)
  (inst____at___Validation_fixtures_translation_order_ServiceComputationInterface3530936092__hygCtx__hyg9 : 
   ImportedService.DecidableEq Job)
  (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
              inst____at___Validation_fixtures_translation_order_ServiceComputationInterface3530936092__hygCtx__hyg9)
  (sched : ImportedService.Prosa_Behavior_Schedule_schedule Job
             inst____at___Validation_fixtures_translation_order_ServiceComputationInterface3530936092__hygCtx__hyg9
             PState)
  (inst____at___Validation_fixtures_translation_order_ServiceComputationInterface3530936092__hygCtx__hyg16 : 
   ImportedService.Prosa_Behavior_Job_JobCost Job
     inst____at___Validation_fixtures_translation_order_ServiceComputationInterface3530936092__hygCtx__hyg9)
  (j : Job) (t : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.Decidable_decide
  (ImportedService.LE_le_inst1 ImportedService.Prosa_Behavior_Job_work
     ImportedService.instLENat
     (ImportedService.Prosa_Behavior_Job_JobCost_job_cost Job
        inst____at___Validation_fixtures_translation_order_ServiceComputationInterface3530936092__hygCtx__hyg9
        inst____at___Validation_fixtures_translation_order_ServiceComputationInterface3530936092__hygCtx__hyg16
        j)
     (ImportedService.Prosa_Validation_ServiceInterface_serviceProjection Job
        inst____at___Validation_fixtures_translation_order_ServiceComputationInterface3530936092__hygCtx__hyg9
        PState sched j t))
  (ImportedService.Nat_decLe
     (ImportedService.Prosa_Behavior_Job_JobCost_job_cost Job
        inst____at___Validation_fixtures_translation_order_ServiceComputationInterface3530936092__hygCtx__hyg9
        inst____at___Validation_fixtures_translation_order_ServiceComputationInterface3530936092__hygCtx__hyg16
        j)
     (ImportedService.Prosa_Validation_ServiceInterface_serviceProjection Job
        inst____at___Validation_fixtures_translation_order_ServiceComputationInterface3530936092__hygCtx__hyg9
        PState sched j t))
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3 : 
          ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3)
         (_ : ImportedService.Prosa_Behavior_Schedule_schedule Job
                inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3
                PState)
         (_ : ImportedService.Prosa_Behavior_Job_JobCost Job
                inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3)
         (_ : Job) (_ : ImportedService.Prosa_Behavior_Time_instant),
       ImportedService.Bool

Arguments ImportedService.Prosa_Behavior_Service_completed_by 
  Job inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3 
  PState sched inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg10 
  j t
ImportedService.Prosa_Behavior_Service_completes_at
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3 : 
          ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3)
         (_ : ImportedService.Prosa_Behavior_Schedule_schedule Job
                inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3
                PState)
         (_ : ImportedService.Prosa_Behavior_Job_JobCost Job
                inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3)
         (_ : Job) (_ : ImportedService.Prosa_Behavior_Time_instant),
       ImportedService.Bool
ImportedService.Prosa_Behavior_Service_completes_at@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0
Lean.u_3+2.0} =
fun (Job : ImportedService.Prosa_Behavior_Job_JobType)
  (inst____at___Validation_fixtures_translation_order_ServiceComputationInterface828512297__hygCtx__hyg9 : 
   ImportedService.DecidableEq Job)
  (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
              inst____at___Validation_fixtures_translation_order_ServiceComputationInterface828512297__hygCtx__hyg9)
  (sched : ImportedService.Prosa_Behavior_Schedule_schedule Job
             inst____at___Validation_fixtures_translation_order_ServiceComputationInterface828512297__hygCtx__hyg9
             PState)
  (inst____at___Validation_fixtures_translation_order_ServiceComputationInterface828512297__hygCtx__hyg16 : 
   ImportedService.Prosa_Behavior_Job_JobCost Job
     inst____at___Validation_fixtures_translation_order_ServiceComputationInterface828512297__hygCtx__hyg9)
  (j : Job) (t : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.Bool_and
  (ImportedService.Bool_or
     (ImportedService.Bool_not
        (ImportedService.Prosa_Validation_ServiceInterface_completedByProjection
           Job
           inst____at___Validation_fixtures_translation_order_ServiceComputationInterface828512297__hygCtx__hyg9
           PState sched
           inst____at___Validation_fixtures_translation_order_ServiceComputationInterface828512297__hygCtx__hyg16
           j
           (ImportedService.HSub_hSub_inst7
              ImportedService.Prosa_Behavior_Time_instant
              ImportedService.Prosa_Behavior_Time_instant
              ImportedService.Prosa_Behavior_Time_instant
              (ImportedService.instHSub_inst1
                 ImportedService.Prosa_Behavior_Time_instant
                 ImportedService.instSubNat)
              t
              (ImportedService.OfNat_ofNat_inst1
                 ImportedService.Prosa_Behavior_Time_instant
                 (Nat_succ Nat_zero)
                 (ImportedService.instOfNatNat (Nat_succ Nat_zero))))))
     (ImportedService.Decidable_decide
        (@eq ImportedService.Prosa_Behavior_Time_instant t
           (ImportedService.OfNat_ofNat_inst1
              ImportedService.Prosa_Behavior_Time_instant Nat_zero
              (ImportedService.instOfNatNat Nat_zero)))
        (ImportedService.instDecidableEqNat t
           (ImportedService.OfNat_ofNat_inst1
              ImportedService.Prosa_Behavior_Time_instant Nat_zero
              (ImportedService.instOfNatNat Nat_zero)))))
  (ImportedService.Prosa_Validation_ServiceInterface_completedByProjection
     Job
     inst____at___Validation_fixtures_translation_order_ServiceComputationInterface828512297__hygCtx__hyg9
     PState sched
     inst____at___Validation_fixtures_translation_order_ServiceComputationInterface828512297__hygCtx__hyg16
     j t)
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3 : 
          ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3)
         (_ : ImportedService.Prosa_Behavior_Schedule_schedule Job
                inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3
                PState)
         (_ : ImportedService.Prosa_Behavior_Job_JobCost Job
                inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3)
         (_ : Job) (_ : ImportedService.Prosa_Behavior_Time_instant),
       ImportedService.Bool

Arguments ImportedService.Prosa_Behavior_Service_completes_at 
  Job inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg3 
  PState sched inst____at___Prosa_Behavior_Service1909714525__hygCtx__hyg10 
  j t
```

## 2026-09-23 23:22 — raw-body import boundary and reproduction

The inspection-only **unprojected** export from the same fresh `Service.olean` succeeded: `Validation/.work/service_raw_inspection.B3sRMF/ServiceRaw.out`, SHA-256 `cf5e4baab2e5f5ba1ce44d133ec323710808f331043391c0cd34d49cc74623d9`, approximately 4.0 MB. It requested six compiled Service definition bodies with no normalization/body projection. Its importer attempt did **not** produce a usable `.vo`: at the default stack it exited `139` after reaching a `UInt32`/character dependency (`import.log`); with `ulimit -s 65520`, it advanced through deep Mathlib dependencies but remained in `Nat.Internal.Linear.ExprCnstr.denote_toNormPoly` after several CPU-intensive minutes, so that exploratory run was interrupted (`import_high_stack.log`). This is an importer scalability limitation for the raw transitive definition closure, not evidence of a Service semantic mismatch. The successful `Print`/`Check` output above is **only** from the fresh, kernel-guarded validation export (`Service.out` SHA-256 `0a2c7cc1aa038fa4a0e8ec80a165d3995c7e14a06ac7d0a02c8831c45873c687`).

Exact fresh stage timings from `prepare_stage_events.jsonl`: Lean build `590.866 s`, source acquisition `7.575 s`, guarded export `49.793 s`, Rocq import `43.448 s`; all `FRESH/PASS`. The inspection Rocq source SHA-256 is `ec7b2cfcffc7b04d546f5850282c91b0023f9342b0674095e25c375e39e08425` and its compilation passed. Rocq version: `9.3+rc1`; Lean toolchain: `leanprover/lean4:v4.33.1`; Mathlib pin: `0df444a360eaa60ab8c11dca51a86af692955474`.

Reproduction from `Prosa-Shunqi/`:

```sh
CLEAN_FULL=1 Validation/scripts/validate_behavior_service.sh prepare
```

Then from `Reports/inspection/`, binding `FoundationImported` to this run's prepared `imported/` directory:

```sh
ulimit -s 65520
opam exec --switch=rocq93rc1 -- rocq c \
  -Q ../../Validation/.work/tooling/rocq-lean-import/src LeanImport \
  -I ../../Validation/.work/tooling/rocq-lean-import/src \
  -Q ../../Validation/.work/runs/incremental_behavior_service_prepare.XgWkrh/imported FoundationImported \
  ServiceImportInspection.v
```

Verdict: **INSPECTION_PASS_GUARDED**; raw-body import remains **BLOCKED_BY_IMPORTER_SCALABILITY**. The existing translation, certificates, validator, and accepted status were not changed for the Service inspection.
