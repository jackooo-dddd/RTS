# `model/task/arrival/task_max_inter_arrival.v` — canonical file report

2026-09-26 01:27 +08:00 — Rank 87，Layer 12。权威 inventory 有 **5** 个声明：
- 单字段 class `TaskMaxInterArrival`；
- 定义 `positive_task_max_inter_arrival_time`（Bool）、`arr_sep_task_max_inter_arrival`、`valid_task_max_inter_arrival_time`、`taskset_respects_task_max_inter_arrival_model`。

直接依赖 `model/task/arrivals.v` 和 `model/task/concept.v`，都已验收。

**当前状态：ACCEPTED_V06_FILE（5/5）。正式累计 86/357 文件、635/2439 声明。**

## Lean translation

新文件 `Prosa/Model/Task/Arrival/TaskMaxInterArrival.lean`，namespace 为 `Prosa.Model.Task.Arrival.Task_max_inter_arrival`（避免 class 名与 namespace 重复触发 lint），没有 sorry/axiom。
- `j <> j'` 写成 `j ≠ j'`；
- `job_task j = tsk` 用 Prop 相等；
- `job_index … > 0` 写成 `0 < job_index (Task := Task) arr_seq j`；
- `a <= b <= c` 写成 `(decide (a ≤ b) && decide (b ≤ c)) = true`；
- `tsk \in ts` 写成 `decide (tsk ∈ ts) = true`。

Lean axioms：class 与 `positive_*` 无 axiom，其余三个为 `[propext]`（来自 Lean 核心 decidable 实例）。

## 源绑定

pinned 源在已验收 arrivals 源闭包上逐字节编译通过。5 个 `Check` fingerprint 与权威 hash 完全一致。

## 语义证书

export 根是 `TmiaComputationInterface.lean`，共 29,737 行，没有 statement-only 项。已验收 arrivals 证书链只改导入模块名。

`TmiaCorrespondence.v`：
- 4 个定义证书；
- class 载体证书 `TaskMaxInterArrival_source_total` / `_target_total`；
- 用到的运算：`arrives_in`、`job_task` 相等（`Lean.eq` 传递）、`job_index`（复用已验收 `job_index_correspondence`）、Job 上的存在量词、`≠`（与已验收 sporadic 证书相同的证明）、Bool `&&` 与 `≤`、`+`、成员。

审计 9 项（6 个声明证书加 3 个辅助引理）全部通过：semantic premises 为空，source/target theorem dependency 为 false，unexpected 为空。

注：manifest 中的 `lean_representation_note` 是从 curves 发布脚本继承的通用措辞，提到的 `monotone` 与本文件无关。manifest 已由 status 的 hash 固定，所以没有改写；发布脚本中的措辞已更正。

## Fresh 验证

脚本 `Validation/scripts/validate_model_task_arrival_tmia.sh`，run `Validation/.work/experiments/model_task_arrival_tmia_final`：
- source：3 s
- Lean build：333 s
- export：49 s
- import：34 s
- 证书编译：10 s

## 证据

- manifest/status：`Validation/planning/v06_pipeline/model_task_arrival_tmia_module_{manifest,status}.json`
- publication：`Validation/imported/translation_order/model_task_arrival_tmia/`
