# Validation

本目录包含 Prosa v0.6 → Lean 4 翻译的语义验证基础设施与全部验收证据。

## 内容

| 目录 | 内容 |
|---|---|
| `scripts/` | `translation_file_pipeline.py`（逐文件 prepare/check/publish 流水线）、`update_reports_readme.py`（报告总表生成与核对），以及早期各阶段的发布与审计脚本。早期 manifest 的 `pipeline` 字段仍引用这些脚本。 |
| `tooling/` | `lean4export` 与 `rocq-lean-import` 的固定 commit、补丁和构建脚本（[README](tooling/README.md)），`file_specs/`（每个文件一份 spec），各文件的导出配置，官方证明闭包清单（`proof_closure/`），以及 CoqEAL 构建清单。 |
| `fixtures/translation_order/` | 各文件的导出根模块、类型指纹探针、Lean 类型审计，以及仅用于验证的接口等式。这些等式在 Lean 中证明，连同证明一起导出，由内核检查。 |
| `certificates/` | 每个文件一个目录：Rocq correspondence 证书链、假设审计模块与假设配置；`common/` 为共享基础模块。 |
| `patches/` | 官方证明闭包的 Rocq 9.3 兼容补丁。只改证明，不改任何语句；每处差异都在对应报告中说明。 |
| `planning/` | 文件 DAG 与声明 inventory（`v06_dependency/`）、表示政策（`v06_current_policy/`）、逐文件 manifest 与 status（`v06_pipeline/`）、早期比较研究的历史快照（`v06_mapping/`，见 [planning/README](planning/README.md)）。 |
| `imported/` | 已发布的导入产物，按文件存放（不纳入版本控制）。 |
| `logs/` | 原始机器日志。 |
| `templates/` | 生成产物本地证书适配器所用的 Rocq 模板。 |

## 验收规则

1. 唯一语义规范是 Prosa v0.6 commit `414e66760333eaa4ef78c685bcf53291c527a548`。
2. 仅编译通过一个 Lean 文件，不构成语义验收。
3. 规划材料、原型、fixture、导入产物与证书本身都不计入翻译 coverage。
4. coverage 只计 `planning/v06_pipeline/` 中 manifest/status 标记为 `ACCEPTED_V06_TRANSLATION` 的声明；文件级验收为 `ACCEPTED_V06_FILE`。
5. 已发布的产物（manifest、status、`imported/` 中的发布目录）不得修改；需要重新验证时，形成新的运行与发布记录。
6. 每次失败的尝试都在对应报告的 Attempts 一节中记录原因与修复。运行期间，失败的运行目录以 `.work/experiments/<run>_attemptN_<reason>/` 归档；全部文件验收后，这些目录已删除以节省空间（2026-10-01）。
