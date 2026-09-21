# 编写依据与版本边界

编写日期：2026-09-21。以下材料在编写本包时读取；它们不是未来运行的最新状态，也不代表本包在 Codex/Lean/Rocq 中做过端到端测试。

## 仓库基线

读取的 RTS commit：

```text
repository: jackooo-dddd/RTS
commit: ee6cf24db110d8179fe990f8b4e796fafb90aa13
```

关键材料（路径相对仓库根目录）：

| 材料 | 用途 |
|---|---|
| `Prosa-Shunqi/Validation/planning/v06_mapping/v06_coq_lean_mapping_policy.md` | 已批准默认表示、工具链及基础结构决策 |
| `Prosa-fei/Validation/reports/2026-09-20_105946_HKT_prosa_source_provenance_history_audit_report.md` | v0.4 来源范围、ProcessorState/completes_at 的版本演化 |
| `Prosa-Shunqi/Reports/2026-09-21_082258_HKT_utility_foundation_expansion_report.md` | 递归 equations、Section-closed type、source extraction、分层进度经验 |

批准 policy 的 blob：`f772f50274cfb1486af8d4fa4efdbf20bf5f211e`。
历史 audit 的 blob：`8cb92c4e06dec811908e10a21373b66c0aa15c03`。
utility expansion report 的 blob：`b93e37d6e61bed32c487190de7aba18c0a2d329b`。

运行时再从当前 workspace 读取其适用 policy 和 manifest；不要从本索引推断某个 declaration 当前仍然 accepted。

## 旧翻译仓库

```text
repository: jackooo-dddd/TranslatedProsaRepo
base path:
rt-proofs-lean4_src_20260917_195641/rt-proofs-lean4/
```

实际查看了：

- `.opencode/skill/coq-lean-mapping.md`，blob `ceb2f745dcc299e32b0d169d5d2e198ee4ad52ab`。
- `.opencode/agent/coq2lean-statement.md`，blob `96e8e8d06656de004ddef15c0afe14ed1f44a7ac`。

旧文件提供映射/分阶段 workflow 参考。本包没有复制旧 prompt 的强制 sorry、Section 泛化或纯统计验收规则。

## 官方文档

Codex skill 的 frontmatter、仓库级 `.agents/skills` 和按需 references 的形式，参考官方 skills 文档：

```text
https://developers.openai.com/codex/skills
https://developers.openai.com/docs/build-skills
```

Lean 递归定义与 elaboration 背景：

```text
https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/
```

`latest` 文档不能替代项目固定 Lean/Mathlib checkout。具体 API、equation lemma 名字和生成 body 必须在目标版本实际检查。

## 本包的状态

这是 instruction-only skill：没有携带新 validator、没有创建 translation certificate、没有更改仓库 policy 或工具链。附带示例、模板和 smoke cases 是执行指引，不能计入翻译或证明覆盖率。

静态检查仅覆盖 Markdown/frontmatter、相对链接、JSON 以及包布局。未在用户的 Codex 中验证触发/加载行为，也未在固定 Lean/Rocq 环境编译本包的说明性示例。
