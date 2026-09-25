# `implementation/definitions/generic_scheduler.v` — canonical file report

2026-09-25 06:04 +08:00 — Rank 71、Layer 11。官方 Prosa v0.6 commit `414e66760333eaa4ef78c685bcf53291c527a548` 中本文件有 4 个 public declarations：`PointwisePolicy`、`empty_schedule`、递归 `schedule_up_to`、`generic_schedule`；唯一直接 file-DAG 前驱 `analysis/transform/swap.v` 已验收。私有 worker 在独立 worktree 中翻译和开发证书，复用已验收 Swap 的 `replace_at` 思路，但以当前 v0.6 原文为规格。worker 只交付目标专用 patch 和冻结证据，未改主树正式状态、未自行发布。

2026-09-25 06:53 +08:00 — 主代理核对并合入 11 个目标专用源文件；官方 Rocq source copy 与 pinned 文件字节一致，不需 Rocq 9.3 兼容补丁。`GenericSchedulerSourceTypeAudit.v` 对 4 项完整 Section-closure 后的 `Check @` 通过，源侧 `Print Assumptions` 全部 closed。合并后的 production Lean 在独立目录 **fresh** 编译；`.olean` hash 与 worker 冻结值一致。Lean type/body audit 和 4 项 `#print axioms` 均通过，只有已批准的 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx` 或 custom axiom。

本次实际 compiled Lean artifact 的四个 definition body 全量导出，没有 statement-only export 或 normalization；主树 fresh `.out` 是 **111,841 行、2,458,055 字节**（worker 先前口头行数不准确，按主树 `wc` 和相同 SHA-256 的 artifact 为准），Rocq 9.3 高栈 import exit 0。四项 imported exact-type guards、`schedule_up_to` 的实际 `Nat.brecOn` zero/succ equation guards、双向 State relation/constant-policy coverage 及最终 correspondence 全部经主树 Rocq kernel 重编。核心递归证明对 source 计数归纳，每一步组合当前 artifact 的计算方程、`replace_at` 对应、Nat equality 与关联 pointwise policy 的函数关系；`generic_schedule` 直接由此前的 prefix 对应组合，**不是分别证明源/目标两边为真**。

| 官方 source | Production Lean | 最终 certificate | 状态 |
| --- | --- | --- | --- |
| `PointwisePolicy` | `Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy` | `gs_pointwise_policy_application` | `CERTIFIED` |
| `empty_schedule` | `Prosa.Implementation.Definitions.GenericScheduler.empty_schedule` | `gs_empty_schedule_correspondence` | `CERTIFIED` |
| `schedule_up_to` | `Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to` | `gs_prefix_correspondence` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` |
| `generic_schedule` | `Prosa.Implementation.Definitions.GenericScheduler.generic_schedule` | `gs_generic_schedule_correspondence` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` |

主树 fail-closed `Print Assumptions` 审计还检查了 7 项辅助 operation/coverage 证书；11/11 均为 `semantic_premises=[]`、`statement_only_dependencies=[]`、`unexpected=[]`、source/target theorem self-dependency=false。递归/通用 schedule 使用的显式逻辑边界仅为 `PropSPropFoundation.interpret_strict`；其余是已批准 importer primitives/definitional UIP。见[assumption summary](../../../../Validation/imported/translation_order/generic_scheduler/assumption_summary.json)、[整文件 manifest](../../../../Validation/planning/v06_pipeline/implementation_definitions_generic_scheduler_module_manifest.json) 和[发布门槛脚本](../../../../Validation/scripts/publish_implementation_definitions_generic_scheduler.py)。主代理在 publication lock 内串行发布，`implementation/definitions/generic_scheduler.v = ACCEPTED_V06_FILE`，4/4 declarations `ACCEPTED_V06_TRANSLATION`；此时正式累计 **66/357 files、463/2439 declarations**，translated-but-not-certified 仍为 0。
