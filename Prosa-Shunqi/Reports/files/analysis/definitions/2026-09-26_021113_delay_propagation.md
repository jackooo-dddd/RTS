# `analysis/definitions/delay_propagation.v` — canonical file report

2026-09-26 02:11 +08:00 — Rank 89，Layer 13。权威 inventory 有 **7** 个声明：
- 5 个定义：`valid_delay_propagation_mapping`、`propagated_arrival_sequence`、`job_mapping_uniq`、`valid_arr_seq_propagation_mapping`、`release_sequence`；
- 2 个 remark：`jitter_delay_mapping_valid`、`jitter_arr_seq_mapping_valid`。

直接依赖 `model/task/arrival/curves.v` 和 `model/task/jitter.v`，都已验收。

**当前状态：ACCEPTED_V06_FILE（7/7）。正式累计 88/357 文件、644/2439 声明。**

## Lean translation

新文件 `Prosa/Analysis/Definitions/DelayPropagation.lean`，没有 sorry/axiom。
- 源中 section 的 `Let`（`consistent_task_job_mapping`、`bounded_arrival_delay`、`consistent_job_mapping`、`valid_arrival_delay`、`valid_job_arrival_def`）全部内联，没有额外的 public 定义。
- 两个 `JobArrival` 实例与源一样作为显式参数。
- 源的局部 instance `release_as_arrival` 不在权威 inventory 中，在 remark 里内联写成 `⟨fun j => original_arrival.job_arrival j + job_jitter j⟩`。
- `[/\ _, _, _ & _]` 写成嵌套 `∧`。
- `flatten [seq job2_of j | j <- …]` 写成 `List.flatten (List.map …)`。
- `==` 写成 `decide (_ = _)`。

Lean axioms：`propagated_arrival_sequence`、`release_sequence` 无；其余为 `[propext]`，`jitter_arr_seq_mapping_valid` 为 `[propext, Quot.sound]`。

## 源绑定

pinned `delay_propagation.v` 在 Rocq 9.3 与当前 MathComp 下有 1 行证明失败：第 198 行的 intro pattern `split => [|->]` 不再能 rewrite `id j2`。新增了 proof-only 补丁 `Validation/patches/prosa-v06-rocq93-analysis-definitions-delay-propagation.patch`，把这一行改成先 `rewrite mem_seq1` 再 `split => [/eqP ->|<-]`，声明本身不变。

源闭包由以下部分组成：已验收 curves 源闭包、已验收 task/readiness jitter 源（pinned 源加已批准补丁），以及本文件（pinned 源加上述补丁）。发布脚本逐个验证这些文件等于 pinned 源加补丁。

fingerprint 探针有一处仅影响显示的调整。权威 evidence 打印时 ssrfun 记号 `f^~ y` 在作用域内，且 `id` 指向 `Datatypes.id`（打印为 `cons^~ [::]` 与 `id`），所以探针在加载源之后执行 `From mathcomp Require Import ssrfun.` 和 `Import Corelib.Init.Datatypes.`。这不改变任何项。之后 7 个 `Check` fingerprint 与权威 hash 完全一致。第一次运行因探针旧版而不完整，已改名保留为 `analysis_definitions_delay_propagation_attempt1_probe_display`；发布使用全新的运行。

## 语义证书

export 根是 `DelayPropagationComputationInterface.lean`，即本文件加已验收 Arrivals 接口；jitter 两个 class 与 `valid_jitter(_bounds)` 也列为目标。两个 remark 为 statement-only。export 共 30,234 行。已验收 arrivals 证书链只改导入模块名。

`DelayPropagationCorrespondence.v`：
- 5 个定义证书。映射函数 `job1_of`/`task1_of` 两侧共用；`job2_of` 按 `ArListRel` 逐点关联；延迟函数与 jitter class 按 `SubNatRel` 逐点关联，class 另有两方向 total 证书。
- 新 bridge：
  - `dp_flatten_map_related`：`flatten ∘ map` 对应；
  - `dp_decide_eq_related`：Nat `==` 与 `decide (=)` 对应；
  - `dp_and4_correspondence`：`and4` 与嵌套 `And` 对应；
  - `dp_release_as_arrival_related`：源常量 `release_as_arrival` 与内联 `JobArrival.mk` 对应。
- 2 个 remark：source 侧是 pinned 声明的精确类型（`type of`，不引用证明），target 侧是导入定理的类型。task set 与 arrival sequence binder 都做双向覆盖。源中 `id` 是 `Datatypes.id`，目标中是 Lean `id`，两者通过展开定义可转换。

审计 18 项全部通过：semantic premises 为空，source/target theorem dependency 为 false，unexpected 为空。

## Fresh 验证

脚本 `Validation/scripts/validate_analysis_definitions_delay_propagation.sh all`，run `Validation/.work/experiments/analysis_definitions_delay_propagation_final`：
- source：6 s
- Lean build：341 s
- export：48 s
- import：34 s
- 证书编译：10 s

## 证据

- manifest/status：`Validation/planning/v06_pipeline/analysis_definitions_delay_propagation_module_{manifest,status}.json`
- publication：`Validation/imported/translation_order/analysis_definitions_delay_propagation/`
- 补丁：`Validation/patches/prosa-v06-rocq93-analysis-definitions-delay-propagation.patch`
