# Finish Time：一份可单独分享的语义验证案例

此包展示 Prosa v0.6 的 `analysis/definitions/finish_time.v` 如何与**实际编译并导入 Rocq 的** Lean 声明对齐。官方源版本为 Prosa v0.6（commit `414e667`）。已发布的验证结果是 **5/5 个 public declarations 验收通过**；本案例额外重载已发布的导入产物，实际运行 `Check` / `Print`。它没有把这次 inspection 冒充新的 clean build。

本文提到的案例文件均随 `casestudy/` 一同提供，链接也只指向包内。长串文件校验值不干扰阅读，集中放在 [SHA256SUMS](SHA256SUMS)；验收时的机器记录见 [manifest](provenance/analysis_finish_time_module_manifest.json) 和 [status](provenance/analysis_finish_time_module_status.json)。

## 建议阅读顺序

| 步骤 | 包内文件 | 看什么 |
| --- | --- | --- |
| 官方规格 | [原始 Rocq 源](source/finish_time_official.v) | `finish_time`、三个定理 statement、`response_time` |
| 当前 Lean 实现 | [FinishTime.lean](lean/FinishTime.lean) | 实际生产 translation；[编译后的 .olean](lean/FinishTime.olean)也在包内 |
| 导出 | [export 配置](audit/analysis_finish_time_export_config.json)、[interface](lean/FinishTimeExportInterface.lean)、[实际 .out](imported/FinishTime.out) | 两个定义的 body、三个定理的精确编译类型；定理 proof body 不导出 |
| 导入 Rocq | [import wrapper](imported/ImportedFinishTime.v)、[imported .vo](imported/ImportedFinishTime.vo)、[完整 Print/Check 输出](finish_time_import_print.txt) | Lean 常量导入后的名字、参数、类型和定义体 |
| 语义对齐 | [最小值 bridge](certificates/FinishTimeMinBridge.v)、[五项 correspondence](certificates/FinishTimeCorrespondence.v)、[源/目标类型检查阅读版](finish_time_alignment_readable.txt) | 使用表示关系组合，而非把 theorem 在两侧各证明一遍 |
| 审计 | [Print Assumptions 原文](finish_time_assumptions_published.txt)、[分类结果](finish_time_assumption_summary_published.json)、[Lean #print axioms 原文](finish_time_lean_axioms_published.txt) | 显式信任边界与自依赖检查 |

Rocq 9.3 所需的[兼容源副本](source/finish_time_rocq93_compat.v)和[精确补丁](source/finish_time_rocq93_compat.patch)也在包内；补丁只改了两个旧 proof script，不改 public statements 或两个计算定义。源侧最终类型的[检查文件](source/FinishTimeSourceTypeAudit.v)和[编译产物](source/FinishTimeSourceTypeAudit.vo)一并保留。

## 五个声明如何一一对应

完整、未删节的导入结果请看 [Print 原文](finish_time_import_print.txt)；[inspection 程序](finish_time_import_inspection.v)记录了实际运行的 `Set Printing All; Print; Check` 命令。下表的 imported 名称来自实际导入环境：

| 官方 Rocq 声明 | Lean 声明 | Imported Rocq 常量 | 对应证书 |
| --- | --- | --- | --- |
| `finish_time` | `Prosa.Analysis.Definitions.FinishTime.finish_time` | `ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time` | `finish_time_correspondence` |
| `finished_at_finish_time` | `…FinishTime.finished_at_finish_time` | `ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finished_at_finish_time` | `finished_at_finish_time_statement_correspondence` |
| `earliest_finish_time` | `…FinishTime.earliest_finish_time` | `ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_earliest_finish_time` | `earliest_finish_time_statement_correspondence` |
| `completes_at_finish_time` | `…FinishTime.completes_at_finish_time` | `ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_completes_at_finish_time` | `completes_at_finish_time_statement_correspondence` |
| `response_time` | `…FinishTime.response_time` | `ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_response_time` | `response_time_correspondence` |

官方两个计算定义的核心分别是 `ex_minn job_finishes` 和 `finish_time - job_arrival j`。实际 imported body 中，前者调用 imported `Nat_find` 并携带完成条件的 witness；后者使用 Lean Nat 的截断减法。证书并没有在 Rocq 中手写另一个“Lean 模型”。[对齐检查程序](finish_time_alignment_inspection.v)同时 `Check` 官方源、导入的 Lean 常量和证书。建议阅读[去掉 warning 前缀的类型输出](finish_time_alignment_readable.txt)；[未修改的原始输出](finish_time_alignment_check.txt)仍保留。删去的仅是开头四条 load-path 重映射提示，所有 `Check` 结果逐字不变。[精确类型 guards](certificates/FinishTimeExactTypeGuards.v)分别检查三个定理 statement，且不被语义证书导入。

三个 Lean theorem 使用 **statement-only export**：实际 compiled theorem *type* 被导入，proof body 不经 importer 重验。Lean proof 的独立公理审计见包内原始记录；Rocq 证书只证明两侧 statement 的语义对应。

## 最终 correspondence 证明在哪个文件？

**本案例的最终证明是 [FinishTimeCorrespondence.v](certificates/FinishTimeCorrespondence.v)，不是 `ServiceCorrespondence.v`。**它的五个 Rocq lemma（上表最右列）分别对应本文件的五个 public declarations；[对应的编译产物](certificates/FinishTimeCorrespondence.vo)由 Rocq kernel 接受。两个定义的证书直接引用官方定义与实际导入的 Lean 定义。三个定理的证书则从已导入的组成运算构造两侧完整 statement，再证明其对应；它们**不使用** source theorem proof 或 statement-only imported target theorem 自身。[精确类型 guards](certificates/FinishTimeExactTypeGuards.v)另外检查这三个实际 theorem 常量恰好具有证书使用的 statement 类型，因此不是只证明了一个无关的手写命题。

证明依赖可按下面的顺序阅读：

```text
ServiceCorrespondence.v       FinishTimeMinBridge.v
  ├─ completed_by 等            └─ ex_minn ↔ imported Nat_find
  └─ completes_at                    ↓
              └──────────→ FinishTimeCorrespondence.v
                                  └─ 本案例五个最终 correspondence lemmas
```

[ServiceCorrespondence.v](certificates/ServiceCorrespondence.v)证明的是较低层 Service 操作的关系，例如 `completed_by_correspondence` 和 `completes_at_correspondence`；Finish Time 证书**复用**它们。[FinishTimeMinBridge.v](certificates/FinishTimeMinBridge.v)证明可复用的最小值关系。[FinishTimeExactTypeGuards.v](certificates/FinishTimeExactTypeGuards.v)只检查目标定理的准确类型；[FinishTimeAssumptionAudit.v](certificates/FinishTimeAssumptionAudit.v)只对六个证书执行 `Print Assumptions`。后两个文件均不是语义对应证明。

## Correspondence 是怎样组合出来的

这里不要求 Rocq `eqType` 与 Lean carrier 语法同一，而采用 `eqType ↔ Type + DecidableEq` 的观察关系；`nat/instant` 采用 `SubNatRel`；Boolean 真值通过已证关系连接；Rocq `Prop` 与 imported Lean `SProp` 通过[显式 foundation](certificates/PropSPropFoundation.v)解释。

[FinishTimeMinBridge.v](certificates/FinishTimeMinBridge.v)独立连接 MathComp `ex_minn` 与**实际导入**的 `Nat_find`：分别得到满足谓词和最小性，再由 Nat 反对称性得到相应返回值。应用到此文件时，predicate correspondence 使用已经验证的 `completed_by_correspondence`，其代码在 [ServiceCorrespondence.v](certificates/ServiceCorrespondence.v)。其余 Service 相关 operation bridge、基础逻辑关系也随包放在 [certificates/](certificates/) 内，不要求读者到别的目录寻找。

| 目标 | 已证依赖的组合 |
| --- | --- |
| `finish_time` | 最小值、`completed_by`、Bool truth |
| `finished_at_finish_time` | `finish_time`、`completed_by` |
| `earliest_finish_time` | finish time、completed-by、Nat `≤`、量词/蕴含 |
| `completes_at_finish_time` | finish time、`completes_at_correspondence` |
| `response_time` | finish time、JobArrival projection、Nat 截断减法 |

`Hsched`、`Hcost`、`Harrival` 是相关输入的**表示关系条件**，不是“本目标已经对应”的任意语义公理；本案例也不宣称所有 Rocq/Lean processor 实例存在无条件的全局同构。五个证书未调用其官方 source theorem 或 imported target theorem 本身来制造双向结论。

## 假设与防作弊边界

正式发布记录中，最小值 bridge 加五个目标都标为 **`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`**，而非 axiom-free `CERTIFIED`。[原始 `Print Assumptions`](finish_time_assumptions_published.txt) 和 [机器分类](finish_time_assumption_summary_published.json)显示：

- `semantic_premises = []`；`statement_only_dependencies = []`；`unexpected = []`。
- source/target theorem self-dependency 均为 `false`。
- 仍有审核过的 foundation：尤其 `PropSPropFoundation.interpret_strict`，以及 importer 的 equality/UIP 与标准逻辑/primitive 边界；因此 `closed = false`，绝不宣称完全无公理。
- [Lean 原始 axiom audit](finish_time_lean_axioms_published.txt)仅列 `propext`、`Classical.choice`、`Quot.sound`，未列 `sorryAx`。

[assumption 配置](audit/finish_time_assumption_config.json)与[fail-closed 分类器](audit/audit_assumptions.py)检查缺失/截断的输出、未知 assumption、语义前提和 theorem 自依赖。[发布 gate 源码](audit/publish_analysis_finish_time.py)另检查 pinned source、类型/计算体、Lean proof-clean、导出配置、产物与证书的有效性；[工具来源记录](audit/tooling_manifest.json)、[exporter 补丁](audit/tooling/lean4export.patch)、[importer 补丁](audit/tooling/rocq-lean-import.patch)、[工具重建脚本](audit/tooling/setup_validation_tooling.sh)、[Lean toolchain pin](audit/tooling/lean-toolchain)、[Lake 依赖 pin](audit/tooling/lake-manifest.json)及[export metadata](imported/export_metadata.json)也在包内。作为计算接口 guard 的 [ServiceComputationInterface.lean](lean/ServiceComputationInterface.lean)使用实际 Lean 表达式，而不是无约束的手写近似式。

## 这份包能复核什么

可直接打开本目录逐层检查：官方源、生产 Lean、编译/导出/导入产物、correspondence 源码和已编译 `.vo`、完整 `Print` / `Check` / assumption 输出，以及正式 [manifest](provenance/analysis_finish_time_module_manifest.json)。[SHA256SUMS](SHA256SUMS)使打包复制后的字节可核对。

本次还以包内的 `imported/ImportedFinishTime.vo` 为加载目标，在原验证环境运行包内 inspection 程序，Rocq batch 退出码为 0。因此复制后的关键导入产物确实可以被 Rocq 读取。本包是**可独立阅读的案例证据包**，不是把 MathComp、所有上游 Prosa 模块、Lean/Rocq 工具链一起拷入的离线构建环境；单独拿走本文件夹即可讲解和查验证据，但重新执行完整编译仍需原验证环境的上游依赖。这里保存的 inspection 输出来自实际 Rocq 运行，不能代替一次新 fresh export/import。
