# 翻译与验证报告

## 当前状态

截至 2026-09-24，最新正式发布的是 `model/processor/ideal_uni_exceed.v`：**48/357 个文件、353/2439 个声明已验收**。数字来自[正式状态文件](../Validation/planning/v06_pipeline/model_processor_ideal_uni_exceed_module_status.json)，不是根据报告或 Lean 文件数量推算。

- [最新已验收文件报告](files/model/processor/2026-09-24_102300_ideal_uni_exceed.md)：7 个声明全部通过实际产物语义验证和审计。
- [当前进行中：`model/processor/overheads.v`](files/model/processor/2026-09-24_111300_overheads.md)：13 个对应证书已编译，但 class/proof-field 的 statement-only 依赖尚未关闭；**未发布验收**。
- [较早的阻塞项：`util/lcmseq.v`](files/util/2026-09-23_073256_lcmseq.md)：尚未验收，不计入上述数字。
- [本次连续执行汇总](runs/2026-09-24_035607_translation_order_continuous_run.md)：跨文件进展与运行背景；不替代正式状态。

下一个执行文件须依据[文件顺序](../v06_file_translation_order.md)、最新 status/manifest 和文件依赖图重新判定；本页不固定其 READY 状态。

## 报告约定

每个已开始的 v0.6 source file 只维护一份 `files/<source-directory>/<首次报告时间>_<source-basename>.md`。后续批次、失败、修复和验收均更新该报告；文件名前的时间沿用最早的历史报告，不随更新改变。详细历史与发现请读[逐文件报告目录](files/)；跨文件执行记录见[runs/](runs/)。

[legacy/](legacy/) 保留可能被引用的旧报告，不能把其中的阶段性 PASS 当成最终验收。原始机器日志位于[Validation/logs/](../Validation/logs/)；正式验收和覆盖始终以[Validation/planning/v06_pipeline/](../Validation/planning/v06_pipeline/)中的 status/manifest 为准。`Prosa/` 中存在候选或 Rocq 证书编译通过，均不足以单独构成 `ACCEPTED_V06_FILE`。
