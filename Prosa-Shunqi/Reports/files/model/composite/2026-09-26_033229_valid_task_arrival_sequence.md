# `model/composite/valid_task_arrival_sequence.v` — canonical file report

2026-09-26 03:32 +08:00 — Rank 93，Layer 13。权威 inventory 有 **6** 个声明：
- 定义 `valid_task_arrival_sequence`，是五个条件的合取；
- 5 个投影 lemma：`_valid_arrivals`、`_valid_costs`、`_from_taskset`、`_respects_max`、`_valid_curve`。

直接依赖 `model/task/arrivals.v` 和 `model/task/arrival/curves.v`，都已验收。

**当前状态：ACCEPTED_V06_FILE（6/6）。正式累计 92/357 文件、694/2439 声明。**

## Lean translation

新文件 `Prosa/Model/Composite/ValidTaskArrivalSequence.lean`，没有 sorry/axiom。binder 顺序与权威类型一致：`Task, TaskCost, MaxArrivals, Job, JobTask, JobCost, JobArrival, ts, arr_seq`。`TaskCost` 通过 `arrivals_have_valid_job_costs` 用到。5 个 lemma 就是相应的合取投影。

## 源绑定

pinned 源在已验收 curves 源闭包上逐字节编译通过。6 个 `Check` fingerprint 与权威 hash 完全一致。

## 语义证书

export 根是 `VtasComputationInterface.lean`，即本文件加已验收 Curves 接口，以及 `TaskCost`、`valid_job_cost`、`arrivals_have_valid_job_costs`、`all_jobs_from_taskset`。5 个 lemma 为 statement-only，共 30,384 行。已验收 curves 证书链（`ArrivalsSeq*`、`ArrivalsCorrespondence`、`CurvesCorrespondence`）只改导入模块名。

`VtasCorrespondence.v`：
- `TaskCost` 关系，并有两方向 total 证书；
- `valid_job_cost`/`arrivals_have_valid_job_costs`：`job_task` 用 `Lean.eq` 传递；
- `all_jobs_from_taskset`；
- 定义证书：五个合取分量分别复用已验收的 `valid_arrival_sequence`、`taskset_respects_max_arrivals`、`valid_taskset_arrival_curve` 证书；
- 5 个 statement 证书：source 取 pinned 声明的精确类型（`type of`，不引用证明），task set 与 arrival sequence 做双向覆盖。

审计 12 项全部通过（`CurvesCorrespondence.I.*` 是别名打印，已按同类归入）：semantic premises 为空，source/target theorem dependency 为 false，unexpected 为空。

## Fresh 验证

脚本 `Validation/scripts/validate_model_composite_valid_task_arrival_sequence.sh`：
- source：2 s
- Lean build：387 s
- export：46 s
- import：33 s
- 证书编译：11 s

## 证据

- manifest/status：`Validation/planning/v06_pipeline/model_composite_valid_task_arrival_sequence_module_{manifest,status}.json`
- publication：`Validation/imported/translation_order/model_composite_valid_task_arrival_sequence/`
