# 使用 v0.4 Lean 作为 Translation Memory

v0.6 决定“翻什么、是什么意思”；旧 Lean 提供“可能怎样实现和证明”的候选。不能把名字重合率变成语义正确率。

## 1. 值得继承的经验

| 旧流程/资产 | 复用方式 | 限制 |
|---|---|---|
| source 文件与 Lean module 接近的布局 | 保留明确 source 路径和 namespace 映射 | 按 v0.6 当前路径，不强留旧目录 |
| 稳定的 public theorem 名称 | 方便对应、查找和追踪变化 | 名称相同仍需核对类型/body |
| Nat、Bool、List、Option 等直接表示 | 作为默认候选，复用已验证 bridges | 不能称跨 ITP 内核的字面同一类型 |
| 已存在的 Lean proofs | 查可用 lemma、归纳参数、局部 helper | 固定 Mathlib 下重新检查，不相信旧 compile 状态 |
| statement/proof 分阶段 | 先固定完整契约，再重建 proof | 不继承“所有 proof 必须 sorry”的统计依赖 |
| dependency-based selector | 复用按前置接口选择任务的思路 | 不复用 v0.4 的 file_order 内容 |
| compile/fix loop | 按错误位置修 import、类型、实例与 proof | 不许通过加假设/改目标来让它通过 |
| Mathlib proof reconstruction | 不模拟所有 SSReflect tactic；用自然 Lean 证明 | 保留 theorem 契约，不是逐 tactic 相似度 |
| notation/local Let 提升为 helper | 在新映射中明确语义与来源 | helper 不算新增 source coverage |
| declaration inventory 与多层审查 | 保留 coverage、完整类型检查、人工审查 | binder 计数、相似度和 self-review 不是 certificate |

这些是“有帮助的既有做法”，并不表示旧项目所有结果都通过了新的语义验收。

## 2. 复用决策流程

先取得目标 v0.6 完整 declaration，然后查可信 ancestor/旧 candidate。

比较：kind、最终类型、隐式/显式参数、source Section closure、相关 instance、body/fields、边界条件、已变化依赖。

随后记录：

- `REUSE_AFTER_REVALIDATION`：有强候选，仍需 fixed-toolchain 重编译和 v0.6 validation。
- `ADAPT_OLD_LEAN`：代码/证明思路可用，必须应用 v0.6 差异。
- `REFERENCE_ONLY`：只能借鉴策略，不可把旧实现当目标。
- `NEW_TRANSLATION`：没有值得复用的候选，直接从 v0.6 开始。
- `REVIEW_REQUIRED`：存在无法自行解决的表示/对应歧义，仅阻塞相关目标。

不要为了“证明可以复用”无限重建历史；旧参考不足时直接翻当前 source，但保留不知道来源的事实。

## 3. 必须修正的历史解读

### ProcessorState

历史 audit 表明旧 Lean 的 aggregate `service_in` 与 v0.4 源结构相符，per-core supply/service 是后来的演化。因此不能写“v0.4 translator 删除了当时 source 的 supply_on/service_on”。

正确迁移规则是：源版本变了，v0.6 新翻译必须保留其真实 per-core operations、laws 和 derived sums。

### completes_at

旧 Lean 与 v0.6 在 `t=0` 上不同，不能仅凭此认定原 v0.4 翻译错误。检查历史后，应归为新版一致性差异；迁移时忠实实现 v0.6 的零时刻语义并做回归。

### util/sum 的旧“多出来”声明

有些是正常 v0.4 源声明，有些是 Lean helper。必须分别记录；不把所有 extra 都当 LLM 编造，也不把所有旧 theorem 自动带入 v0.6 覆盖率。

### Classic

modern 部分的 provenance 结论不能自动扩展到所有 Classic 文件。Classic 候选需单独证据，概念相似不等于已覆盖 v0.6。

## 4. 不继承的旧 prompt 规则

- **“ALL proof bodies MUST be sorry”**：为旧统计服务，不适合当前 clean proof / semantic acceptance 流程。保留阶段隔离，不保留强制占位证明。
- **“Section 的所有假设自动进入每个 theorem”**：不能这样概括。使用最终 elaborated type。
- **“只看 ∀/→ 数量即可验证 signature”**：最多作为异常筛查。
- **“禁止 lake build，直接 lean 检查即可”**：检查单文件和生成依赖 artifact 是不同需求，必须正确构建实际 import 链。
- **“nat/Prop identical”**：语言级相似不等于跨 ITP 表示相同；Lean Prop 导入的 SProp foundation 仍需单独披露。
- **“== 与 decide equality 任意互换”**：须验证 equality behavior 和实例。
- **“finfun 可以直接选 Finsupp”**：检查全函数、有限 support、零元要求，不能增加源没有的限制。
- **“foldl/foldr/Finset 任意替换”**：保留运算 laws、重复项、顺序和单位元。
- **“max 用非空 API 即可”**：源若允许空集合并给默认值，不允许新增 nonempty 条件。
- **“Canonical Structure 机械换 instance”**：读取 observable structure 和实际 elaboration 选择。
- **“无文本 sorry 就 success”**：必须检查实际编译、传递 axioms、source mapping 和证书有效性。

## 5. 不把风格选择写成错误归因

外部 carrier 参数、Prop API、noncomputable 标记和 `brecOn` 都不自动构成翻译错误。需要区分：

```text
已证语义不对应
当前 policy 不允许的未审查变换
正确但验证较困难的表示
源版本演化
尚未取得足够证据
```

只有第一类能直接叫 semantic mismatch。其余类型按实际证据报告，不用“看着奇怪”替代分析。
