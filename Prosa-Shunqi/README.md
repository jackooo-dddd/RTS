# Prosa v0.6 → Lean 4 翻译

本工作区以 Prosa v0.6（commit `414e66760333eaa4ef78c685bcf53291c527a548`）为唯一翻译规范，目标环境为 Lean 4.33.1 和 Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。新翻译从固定 v0.6 源码与本工作区已认证的表示关系出发，不使用旧版本 translation memory。

## 目录

- `Prosa/`：当前 v0.6 Lean 翻译候选；文件存在**不代表已验收**。
- `Validation/`：依赖与映射规划、验证脚本、证书、测试材料及机器证据。
- [Reports/](Reports/README.md)：当前进度入口、逐文件报告及运行汇总。

正式验收以 `Validation/planning/v06_pipeline/` 中的 status/manifest 为准，仅 `ACCEPTED_V06_TRANSLATION` 计入声明覆盖。翻译先依[文件依赖图](Validation/planning/v06_dependency/)，再按[文件执行顺序](v06_file_translation_order.md)选择已就绪文件；[当前 v0.6 表示政策](Validation/planning/v06_current_policy/representation_policy.md)约束新翻译。声明依赖图只作辅助，不能替代文件依赖图。`v06_mapping/` 保留为历史比较证据，不再提供 translation memory。
