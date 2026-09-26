# `implementation/definitions/maximal_arrival_sequence.v` — canonical file report

2026-09-26 03:20 +08:00 — Rank 92，Layer 13。权威 inventory 有 **7** 个计算性定义：`suffix_sum`、`jobs_remaining`、`next_max_arrival`、`extend_arrival_prefix`、`maximal_arrival_prefix`、`max_arrivals_at`、`concrete_arrival_sequence`。直接依赖 `model/task/arrival/curves.v` 和 `util/supremum.v`，都已验收。

**当前状态：ACCEPTED_V06_FILE（7/7）。正式累计 91/357 文件、688/2439 声明。**

## Lean translation

新文件 `Prosa/Implementation/Definitions/MaximalArrivalSequence.lean`，没有 sorry/axiom，axioms 均为 `[propext]`。

表示方式：

| 源 | Lean |
|---|---|
| `\sum_(a <= t < b) F t` | `sumSeq (List.range' a (b - a)) F` |
| `nth 0 xs t` | `xs.getD t 0` |
| `supremum leq` | 已验收 `Prosa.Util.Supremum.supremum (decide ≤)` |
| `iter t.+1 f [::]` | `Nat.repeat f (t+1) []`（与 MathComp 的 `iter` 递归方式相同：`f (iter n f x)`） |
| `\cat_(tsk <- ts)` | `bigCatSeqAll` |

binder 顺序与权威类型一致，例如 `concrete_arrival_sequence : Task, Job, MaxArrivals, generate_jobs_at, ts, t`。

## 源绑定

pinned `util/supremum.v` 与本文件在已验收 curves 源闭包上逐字节编译通过。7 个 `Check` fingerprint 与权威 hash 完全一致。

## 语义证书

export 根只包含本模块（加 `MaxArrivals` 类、`supremum`、`sumSeq`、`bigCatSeqAll`），共 20,890 行。

第一次 prepare 的 export 不含 `Membership.mem`、`List.instMembership`、`List.Mem`、`Bool.not`，已验收的 service 适配器（`JitterSvcBaseAdapter` 等）无法重新绑定。于是把这 4 个 Lean 核心常量加入 export 目标后重新 prepare，适配器无需修改即可编译。旧运行保留为 `implementation_definitions_maximal_arrival_sequence_attempt1_adapter_closure`。

`MaximalArrivalSequenceCorrespondence.v`：7 个定义证书。输入相关时（arrival prefix 为 Nat 列表、task、时刻、`MaxArrivals` 曲线、job 生成器、task 列表），源定义与编译后的 Lean 定义结果相关。
- 已有 bridge：Nat 列表的 `size`/`nth`/`range'`/`map`、区间和（复用已验收证书，并用 `ms_list_sum_fold` 连接 `List.sum` 与 `foldr`）。
- 新 bridge：
  - Nat 上的 `supremum leq`：逐步归约 `choose_superior`，用 `decide ≤` 的已验收对应传递 `ite`；
  - `Nat.repeat` 与 `iter`：按次数归纳；
  - 单元素 `++`；
  - `\cat` 与 `bigCatSeqAll`（`flatMap`）；
  - `Option` 分支（`next_max_arrival`）。
- 每个输入关系（曲线类、生成器、Nat 列表、task 列表）都有两方向 total 证书。

审计 19 项全部通过：semantic premises 为空，source/target theorem dependency 为 false，unexpected 为空。

## Fresh 验证

脚本 `Validation/scripts/validate_implementation_definitions_maximal_arrival_sequence.sh`，run `Validation/.work/experiments/implementation_definitions_maximal_arrival_sequence_final`：
- source：3 s
- Lean build：188 s
- export：43 s
- import：32 s
- 证书编译：5 s

## 证据

- manifest/status：`Validation/planning/v06_pipeline/implementation_definitions_maximal_arrival_sequence_module_{manifest,status}.json`
- publication：`Validation/imported/translation_order/implementation_definitions_maximal_arrival_sequence/`
