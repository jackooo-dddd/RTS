# `model/task/arrival/request_bound_functions.v` — canonical file report

2026-09-26 01:14 +08:00 — Rank 86，Layer 12。权威 inventory 有 **8** 个声明：
- 2 个单字段 class：`MaxRequestBound`、`MinRequestBound`；
- 6 个定义：`valid_request_bound_function`、`respects_{max,min}_request_bound`、`valid_taskset_request_bound_function`、`taskset_respects_{max,min}_request_bound`。

直接依赖 `model/task/arrivals.v` 和 `util/rel.v`，都已验收。

**当前状态：ACCEPTED_V06_FILE（8/8）。正式累计 85/357 文件、630/2439 声明。**

## Lean translation

新文件 `Prosa/Model/Task/Arrival/RequestBoundFunctions.lean`，没有 sorry/axiom，8 个声明都不依赖 axiom。表示方式与已验收的 `curves.v` 相同：单字段 class、`monotone (fun x y => decide (x ≤ y))`、`decide (tsk ∈ ts) = true`。

需要 `JobCost` 的定义按源顺序放在 `JobTask` 之后，例如 `respects_max_request_bound : Task, Job, JobTask, JobCost, arr_seq, tsk, bound`。

## 源绑定

pinned `util/rel.v` 与本文件在已验收 arrivals 源闭包上逐字节编译通过。8 个 `Check` fingerprint 与权威 hash 完全一致。

## 语义证书

export 根是 `RbfComputationInterface.lean`，共 29,778 行，没有 statement-only 项。已验收 arrivals 证书链只改导入模块名。

`RbfCorrespondence.v` 的结构与 curves 相同：
- 6 个定义证书；`cost_of_task_arrivals` 复用已验收证书，额外的输入关系是 `job_cost` 的 `SubNatRel`；
- 2 个 class 各有 `_source_total` / `_target_total` 载体证书；
- 曲线函数有两方向 total 的 import/export 证书。

第一次运行审计时，4 个证书报告 `ArrivalsCorrespondence.I.True/HEq_inst1` 为 unexpected。原因是两个模块都定义了别名 `I`，`Print Assumptions` 用 `ArrivalsCorrespondence.I.` 前缀打印了同一批 SProp 常量。这只是名称问题，所以把这些限定名加入相同类别（SProp UIP 与 importer foundation）后重新运行 check，其余不变。

审计 14 项全部通过：semantic premises 为空，source/target theorem dependency 为 false，unexpected 为空。

## Fresh 验证

脚本 `Validation/scripts/validate_model_task_arrival_rbf.sh`，run `Validation/.work/experiments/model_task_arrival_rbf_final`：
- source：3 s
- Lean build：316 s
- export：47 s
- import：35 s
- 证书编译：10 s

## 证据

- manifest/status：`Validation/planning/v06_pipeline/model_task_arrival_rbf_module_{manifest,status}.json`
- publication：`Validation/imported/translation_order/model_task_arrival_rbf/`
- 发布入口：`Validation/scripts/publish_model_task_arrival_rbf.py`
