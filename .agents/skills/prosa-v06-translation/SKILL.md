---
name: prosa-v06-translation
description: 在 Prosa-Shunqi 中将固定 Prosa v0.6 的 Rocq/MathComp/SSReflect 声明翻译或迁移到 Lean 4；用于选择表示、复用 v0.4 Lean、重建证明、检查编译后计算接口及交接语义验证。不用于把旧报告当作认证、不用于擅自升级源码或工具链、不用于无关 Lean 项目。
---

# Prosa v0.6 → Lean 4 Translation

## 1. 目标与权限边界

生成符合 **v0.6 源语义、已批准表示规则、后续 actual-artifact validation** 的 Lean 实现。

**优先级：语义忠实与假设完整 > 可验证性 > 下游可用性 > 表面风格。**

本 skill 指导翻译、证明重建和验证交接，不是 validator，也不能代替 kernel 检查。加载本 skill 不授权扩大用户指定的批次、修改历史工作区、放宽验收规则或提交远端。

从当前任务和实际仓库读取进度；不要把某轮的声明数、完成率或 PASS 写成长期事实。

## 2. 启动检查与权威来源

定位仓库根目录和 `Prosa-Shunqi/`，读取适用的 `AGENTS.md`、项目 README、`Validation/WORKSPACE_POLICY.md`、任务范围及相关 manifest。以下路径均相对 `Prosa-Shunqi/`。

基线 pins：

| 项目 | 固定值 |
|---|---|
| Prosa v0.6 | `414e66760333eaa4ef78c685bcf53291c527a548` |
| Lean | `leanprover/lean4:v4.33.1` |
| Mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` |
| v0.4 历史参考 | `ee05f255e29676ad79e07b5d6cc59dc66cd7fcb7` |

实际执行前核验源码 commit/tree、工作树、`lean-toolchain`、Lake manifest、实际工具版本及工具补丁。pins 与仓库后来明确批准的迁移发生冲突时，报告 `CONFIGURATION_CONFLICT`，核实批准记录；不要静默升级或回退。

按以下角色使用材料：

- **语义目标**：固定 v0.6 源码和与其绑定的最终 elaborated declaration。
- **表示决策**：`Validation/planning/v06_mapping/v06_coq_lean_mapping_policy.md` 和 `foundational_representation_decisions.md`。
- **调度与对应**：`v06_dependency/` 的文件图、声明 inventory，以及 `v06_mapping/v06_migration_table.*`。
- **实现参考**：同版本且证据仍有效的新版 Lean，随后才是旧 Lean/v0.4。
- **接受依据**：本次实际 artifact 对应的证书、审计和有效性检查；不是 mapping 表或历史 dashboard。

表示 policy 不能覆盖源语义；本 skill 不偷偷更改已批准 policy。发现实质冲突时，只阻塞受影响声明，记录待审查事项并继续独立任务。

## 3. 工作区与依赖

`Prosa/` 是正式 v0.6 **翻译候选树**，不保证每个声明都已 accepted。
`Validation/` 放候选实验、桥接、证书、工具和证据；`Reports/` 放可追溯汇总。
`../Prosa-fei/` 默认为只读历史参考。不得把整棵旧 `Prosa/` 复制成新版。

优先运行已存在、已审核的 workspace-local source/tooling 入口；不要默认依赖旧工作区的 `.work` 或手工 `/private/tmp` 工具。旧 planning snapshot 保留原证据，不改写成新运行记录。

当前文件 DAG 是保守调度边界；边 `B → A` 表示 A 依赖 B。按当前任务定义的 readiness gate 执行。声明 DAG 用于细化上下文与局部顺序；缺边不证明无依赖，尤其涉及实例、coercion、canonical/HB。

区分类型/定义依赖、证明依赖、证书依赖。不要把“所有证明先完成”当成数学必需，也不得擅自绕过本批明确的文件验收门槛。若聚合导入过度阻塞，另提有证据的调度改进，不删除原图边来制造 READY。

检索只先取：目标完整声明、直接依赖的真实接口、相关 policy、相符旧候选、少量有用 lemma。真实依赖优先于名称/向量相似度。

## 4. 翻译前的声明契约

每个目标先记录以下信息；可使用 [任务记录模板](assets/task-record-template.json)，并适配现有数据库，不再建立竞争性状态源。

1. v0.6 文件、完整声明名、种类、位置及内容 hash。
2. Section 关闭后的完整类型：universes、显式/隐式参数、typeclass、假设和结论。
3. 对定义读取真实 body；对结构读取 carriers、字段、构造器及 laws；对递归定义读取所有分支。
4. 源码中的 notation、coercion、默认值、实例选择和 proof-dependent computation。
5. Lean 对应名或对应声明组、旧候选证据、复用决策、预计验证方法。

**不根据 Section 文本猜最终参数。**只保留源最终契约要求的假设；既不能把整个 Section 的假设全加进去，也不能遗漏 proof 使用后被泛化进最终类型的假设。

`Check @source_decl` 与 `#check @target_decl` 是检查入口；严谨比较使用实际 elaborated expressions/可靠提取器。打印文本和 binder 数只是诊断，不能证明对应。

源旧 proof 在新 Rocq 中失败时，先使用已批准的兼容层或源码提取工具。提取必须绑定原完整类型、Section context 和计算 body。提取模块能编译，不自动证明提取忠实；缺少源绑定证据时保留 `SOURCE_BINDING_UNVERIFIED`。

## 5. 旧 v0.4 translation memory

阅读 [v0.4 复用规则](references/v04-translation-memory.md)。继承文件/namespace 对照、直接类型映射、已成功的归纳组织、Mathlib lemma 提示，以及“statement 与 proof 分阶段”的工作方式。

先比较 v0.6，再决定沿用现有 migration label：
`REUSE_AFTER_REVALIDATION`、`ADAPT_OLD_LEAN`、`REFERENCE_ONLY`、`NEW_TRANSLATION` 或 `REVIEW_REQUIRED`。

同名、相同源码 command、旧编译成功，都不是语义证据；依赖变了，即使声明文本没变也须复核。

**不要把历史漂移误写成翻译错误。**旧 `ProcessorState` 的 aggregate service 和旧 `completes_at` 的零时刻行为，已有 provenance 证据支持其来自 v0.4；新版仍必须采用 v0.6 语义。

默认给每个源 public declaration 一个稳定主对应，允许已记录的一对多/多对一表示。任何 helper 标记 `LEAN_HELPER`；源声明被 inline 不能无记录消失。构造器、projection、recursor 不重复计入 public 数，但其语义仍要覆盖。

## 6. 已批准表示规则

下表是默认摘要。触及集合、Bool/Prop、类或聚合边界时，再读 [详细表示规则](references/representation-rules.md) 和仓库正式 policy。

| 源对象 | Lean 默认 | 必须保留的内容 |
|---|---|---|
| `nat`、时间/工作量 alias | `Nat`，简单 alias 用 `abbrev` | 自然数语义、截断减法、默认值；不是自动已证同构 |
| `bool` 计算 | `Bool` | 真值、分支及可计算输出 |
| 源 `Prop` | Lean `Prop` | 完整量词/假设/结论；导回 Rocq 的 SProp 是另一个验证边界 |
| `eqType` | carrier + `DecidableEq` | 当前 policy 要求的边界参数和正确 equality 行为 |
| `finType` | carrier + `Fintype` + `DecidableEq` | 有限枚举覆盖、唯一性与同一套实例 |
| `seq T` | `List T` | 顺序、重复项、访问越界时的源默认值 |
| `option T`、普通积/和类型 | `Option T`、对应 Lean 数据类型 | 构造分支和 payload；依赖版本另审 |
| MathComp `{set T}` 等外延有限集合 | `Finset T` | membership、集合操作及有限 carrier 边界 |
| Prosa `util/seqset.set` | `List` + `Nodup` 的结构 | 可观察列表顺序，不能误当 `{set T}` |
| 自然数 `[m,n)` 求和 | `Finset.Ico m n` 的求和值语义 | 上端不含、空/反向区间、筛选和零元 |
| 序列上的聚合 | 对应 `List` fold/sum | 重复项及必要的折叠顺序；不自动去重 |
| Class/Record/Inductive | 对应 Lean 结构 | carriers、数据、laws、构造分支及消去能力 |

禁止混淆：

- `DecidableEq` 与任意 `BEq` 不是同一个正确性保证。用 `==` 前核查 `LawfulBEq` 或已证桥接。
- source Bool API 保留 Bool；theorem 中 `is_true b` 可用 `b = true` 或有桥接的 Prop。不是禁止所有 Prop 改写。
- `reflect P b` 可能是 `Set` 中的 informative view；不能无条件改成 `↔` 并丢失消去用途。
- 只在 `variable` 中写 `[DecidableEq T]` 不保证最终声明携带它；核查 `#check @decl`。按当前 policy 显式保留所需边界，不擅自泛化到裸 `Type`。
- 泛型 bigop 保留运算、单位元和所需 laws；不要给源非交换运算新增交换性假设以便使用 `Finset.fold`。

### ProcessorState 默认

采用已批准的 owned/nested `State` 与 `Core`，携带 Core 的有限性/判等、`scheduled_on`、`supply_on`、`service_on` 及两条 laws。
`scheduled_in`、`supply_in`、`service_in` 留作派生定义，不能换成无约束 primitive fields。
`scheduled_in` 沿用有限 Bool-or fold 及 existential reflection；后两者沿用有限求和。

外置 State 在数学上不必错误，但不是本项目当前默认；不能一边迁移一边另选接口。prototype 编译通过不等于整个结构已跨 ITP 认证。

## 7. Translation 必须考虑 validation friendliness

**在批量证明下游 theorem 之前，先为新 computational definition 做一个小型验证预检。**

先问：真实编译结果能否用已有桥接、简单 equations 或局部等价证明与源连接？不是只问 Lean 能否编译。

### 7.1 选择易验证的实现

- 语义相同且表达成本合理时，优先接近源的直接函数、构造器和显式结构递归。
- 显式安排递减参数与分支，减少不必要的嵌套 matcher、依赖 cast 和实例层。
- **不保证某种表面写法一定生成 `Nat.rec`。**先检查 compiled body 和 equation lemmas。
- `brecOn`、`below`、well-founded recursion 本身不是错误。已有简单、已证 equations 时，优先用 equations，而非重写已正确的生产定义。
- 默认避免整体 `reduceAll` / 无界展开。局部展开必要 wrapper，保留已建立 bridge 的运算头。
- `noncomputable` 不是语义错误标记，但源可计算定义不应无故依赖选择公理。分清逻辑对应与可执行性要求，记录必要的变化。

### 7.2 检查实际 artifact

对新递归/表示边界，提前执行一个最小 probe：

1. 在固定环境生成当前模块及其项目依赖的 fresh `.olean`。
2. 检查完整类型、实际 body、关键 instances、编译器生成的 equations。
3. 检查 `.eq_1/.eq_2` 等的实际名字、参数、类型与 `#print axioms`；不假设名字或 `rfl` 总成立。
4. 在验证器可用时，试导出/导入最小切片，查看引入的定义与 assumptions。
5. 确定验证路径后再扩展该定义的下游证明。

预检还要先查找已经审核过的 exporter/importer pattern，而不是为每个文件
重新探索同一个问题。至少复用：statement-only theorem type export、
definition-body projection、实际 computation equations、`Finset.sum`/半开区间
的 guarded normalization、universe-sensitive `List`/datatype interface，以及由
kernel `Eq.refl` 或 `Meta.isDefEq` 检查的 normalization guard。命中已有 pattern
时，把目标名、实际类型和 artifact hash 参数化进现有配置/helper；只有模式不
适用时才新增接口。

任何 projection 或 normalization 都必须来自本次 actual compiled artifact，
保存原表达式与变换后表达式的 provenance，并有 kernel-checkable guard；
`Meta.isDefEq` 是有用的预检，但不能单独冒充 kernel certificate。预检同时记录
export 大小、依赖爆炸、universe 和 imported datatype identity，尽早选择最小但
完整的 actual-artifact interface。

**允许使用目标定义的已证递归 equations**：它们是计算规律，不是把目标业务定理当成自身 correctness 的证明。
但 equations 必须绑定实际定义，proof body 在 Rocq 中导入并检查，或在 Rocq 对真实导入体重证。只有 statement 的 equation 仍是 assumption，不能伪装成闭合桥接。

若改写已存在定义使验证更容易：保留候选差异，证明新旧定义的等价或重新对源验证；所有受影响结果失效后重建。不要只保留“新实现满足相似 spec”。

详见 [验证友好实现](references/validation-friendly-patterns.md)。

## 8. Lean 证明重建与编译

保留源 statement，不逐句翻译 SSReflect tactic。优先复用已有 Lean/Mathlib lemma，随后尝试 `rfl`、受控 `simp`、`rw`、`constructor`、`cases`、`induction`、`omega` 等适用方法。

旧 proof 提示中的 API 必须在固定版本查证。自动搜索成功后整理实际 proof；`native_decide` 等路径不能绕过公理/信任审计。

本项目默认不向 `Prosa/` 提交 `sorry`/`admit`/`sorryAx`、伪造 axiom、`unsafe` 绕过或隐蔽 oracle。不要沿用旧 agent 为便于统计而强制填 `sorry` 的规则。未完成 theorem 可先记录完整类型，或在 validation-only 文件中定义 statement 对象；不得假称已证明 theorem。

冻结 statement 后进入 proof-only 阶段：不得静默改类型、参数、实例、相关计算 body 或结构 fields。单改 proof 也会改变 artifact；是否可复用旧证书由 hash/依赖检查决定，不由模型猜测。

`lake env lean <file>` 可做检查，但不会自动为后续 import 安装最新 `.olean`；需要时用 `lake build <Module>` 或显式 `-o` 构建正确依赖。正式验证隔离项目 build root，禁止同名旧 `Prosa.*` 抢先被加载。

对目标及计算实例检查传递公理依赖，不只 grep 文本。允许项取自现有审计 policy；没有审计、空日志或不认识的项均不是 clean。

## 9. 验证交接：简单声明走轻量路径

为每个目标选择实际验证计划；不要把“文件仅一个声明”当成简单性的证据。

| 验证计划 | 使用方式 |
|---|---|
| `DIRECT_REUSE_BRIDGE` | alias/基础构造实例化已有桥接，仍绑定本次 artifact |
| `COMPOSE_EXISTING_BRIDGES` | 组合运算、函数、量词和集合桥接 |
| `NEW_PRIMITIVE_BRIDGE` | 新增最小未覆盖操作，如减法、访问、计数 |
| `NEW_REPRESENTATION_CERTIFICATE` | 显式载体转换、覆盖及可观察操作对应 |
| `THEOREM_STATEMENT_ONLY` | 验证完整 theorem type；此标签不是自动允许任意 assumption |
| `CUSTOM_SEMANTIC_VALIDATION` | 记录上述方法不足的具体原因 |

桥接定义与当前 `ImportedX.*` 是否兼容必须核查；同名或放在 `common/` 不等于自动可复用。优先轻量实例化/适配，不为每个文件重新证明同一基础。

证书必须连接实际源码对象/可靠类型提取与实际导入的 Lean 对象。额外手写模型需要经过检查的绑定；不能代替真实 target。

对 theorem，不能以“源 theorem 和目标 theorem 各自是真的”代替翻译验证。完整类型 guards 与 correspondence proof 分开；记录允许的 binder 重排、表示变换和覆盖范围。

### Correspondence 依赖图与复用

把 semantic correspondence 当作独立于 Lean proof graph 的依赖 DAG：

```text
primitive/type bridges
        ↓
operation/function correspondences
        ↓
helper correspondences
        ↓
target theorem-statement correspondence
```

开始新证书前，先从现有 certificate、validation database 和 imported
operation interface 中枚举并查找其类型、函数、谓词和辅助运算依赖。
已认证的 correspondence 必须直接组合复用；不要在目标证书内再次展开并
重证。缺失项先提取成最小、具名、可独立编译和审计的 operation-level
certificate，再供当前与后续目标使用。只有技术上无法抽取时，才保留有
说明的局部证明。

高频 primitive/operation（尤其 `Bool`、`nat`、`seq`/`List`、
`eqType`/`DecidableEq`、membership、length、append、filter、roundtrip 和逻辑
连接词）的默认顺序是：

```text
certified common bridge
→ 参数化或实例化
→ 生成最小 artifact-local adapter
→ 最后才手写新的 correspondence proof
```

artifact-local adapter 可以由小型模板/生成器产生，但生成物必须显式引用实际
imported constructors/equations，作为普通 Rocq 源码进入 kernel 编译、
`Print Assumptions` 和 fail-closed audit；生成器本身不能把对应关系写成 axiom
或未证明 premise。common bridge 的复用也必须检查其输入 relation、universe、
datatype identity 和 artifact hash，不能只因名称相同就套用。

对已经具备 operation bridges 的普通 theorem statement，优先用可审计的
combinator/tactic/template 自动组合 `forall`、`exists`、`And`、`Or`、蕴含、
等式、membership、Bool truth 以及 List/Nat 运算。自动化遇到缺失 operation
relation 时应留下明确 subgoal；先补一个最小可复用 bridge，再继续组合，而不
在每个 theorem 内复制基础语义证明。

目标是证明 official Rocq statement 与 actual imported Lean statement 在
批准的表示关系下对应，而不是重演任一侧 proof。目标 correspondence 不得
直接或间接使用 source theorem constant 或 imported target theorem constant
来自证；也不得因两边 theorem 各自可证就宣称 translation correctness。

逐目标报告至少列出：`REUSED_CERTIFIED_DEPENDENCIES`、
`NEW_CORRESPONDENCE_CERTIFICATES`、`UNRESOLVED_OR_ASSUMED_DEPENDENCIES`，以及
source/target self-dependency 两项布尔审计。严格区分已认证 correspondence、
statement-only imported dependency、显式 semantic premise 与未验证假设；
只有第一类可作为已完成的可复用语义依赖。

**区分 related-input 参数与缺口假设**：`ListRel xsR xsL`、`SubNatFunRel fR fL` 是逻辑关系的输入条件；它们不是自动作弊，也不是不存在。记录为 `input_relations`，说明构造/覆盖。尚未证明的目标操作对应、或直接假设当前结论，是额外 semantic premise，必须标 `CONDITIONAL` 或拒绝。

`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`、importer equality/UIP、statement-only dependencies、源码提取边界分别记录。`Print Assumptions` 不会自动审计所有局部前提，也不能仅凭其不出现一个已证明的常量就断言没有该依赖；复核完整 certificate type 和实际依赖闭包。

## 10. 批量执行、增量验证与卡点管理

按依赖独立的 semantic cluster 推进：契约 → 定义/表示预检 → proof → 验证 → 记录。
整文件所有源声明必须有映射与状态；允许局部进展，不把局部成功说成整文件 accepted。

除非目标已有更严格入口，文件/批次验证默认分为：

```text
prepare  → 固定 snapshot 的 Lean build、source acquisition、export、Rocq import
check    → 只编译受影响 certificate DAG 并运行局部 assumption audit
finalize → 对当前 snapshot 做 whole-file regression、完整 audit 和 publication
```

同一 snapshot 共用一次 prepare。certificate-only 修改不得触发 Lean build、
export 或 import；production/source、transitive relevant dependency、计算接口、
export 配置、工具链、模块加载配置或工具 binary/patch 变化时，必须准确使相关
prepare cache 失效。缺失、hash 不符或损坏的 cache 一律重建或 fail closed，
不得从其它 workspace 静默加载同名 `.olean`/`.vo`。保留 `CLEAN_FULL`（或等价）
路径，在 batch publication 和独立复现时比较增量路径的结论与 trust boundary。

新 validator 优先使用配置驱动的通用 prepare/check/finalize helper；per-file
代码只描述目标、source acquisition、export interface、certificate DAG 和
publication schema。不要复制一整套大型 shell pipeline。抽取复用逻辑时保持
原有 fail-closed 行为，避免为了“通用”而扩大 cache key 或缩小审计范围。

每次运行统一记录以下 stage：`lean_build`、`source_acquisition`、`export`、
`rocq_import`、`certificate_compile`、`assumption_audit`、`publication`。每项
至少含 execution count、`FRESH`/`VERIFIED_CACHE`/失败模式、elapsed time、
input fingerprint 和输出 hashes；失败尝试记录 stage 和原因。报告瓶颈必须
来自这些 evidence，而不是从 report 时间戳间隔推测。

优先收尾接近验收的 cluster。单个未闭合边界默认最多三种实质方法：已有桥接/局部归约、已证 equations 加强归纳、经过审查的表示调整。三者不是必做清单，也不限制必要的普通 tactic 调试。

预算耗尽则保留目标、已试方法与证据，标 `BLOCKED_SEMANTIC_VALIDATION` 或相应 blocker，并转向独立任务。未证明不是发现反例，不改成 `FAILED_SEMANTIC_EQUIVALENCE`。不得因此降低 gate，也不让一个卡点垄断整个批次。

只补当前目标需要的最小通用 bridge；没有具体受益目标，不启动大型基础设施重构。

## 11. 状态、失效与交付

独立记录 translation、compile、proof、semantic proof、audit、acceptance；至少能表达：
`NOT_STARTED`、`TRANSLATED`、`PROOF_CLEAN`、`SEMANTIC_PROOF_COMPILED`、`NOT_YET_VALIDATED`、`CONDITIONAL`、`ACCEPTED`、`BLOCKED`、`STALE`。
这些是不同维度，不是一条强制线性状态链。

每个状态附对应源码/artifact hash 和日志证据；未重跑不得标 fresh。已改源码与旧成功结果不匹配时显示 STALE。不能把 not accepted 写成 NOT_STARTED。

publication 明确区分 `FRESH` 与 `VERIFIED_CACHE`，并区分当前 snapshot evidence
与历史 evidence。只有先验证证据的 snapshot/input fingerprint 与当前发布对象
一致，才能汇总为 accepted；`fresh_build=true` 不得硬编码。审计规则变化至少
使 audit stage 失效，certificate 变化使其下游 compile/audit/publication 失效，
Lean/source/interface 变化则使 prepare 及全部下游失效。

hash 用真实字节/实际 expression 生成；不要对硬编码的 `"Type"`/`"Nat"` 字符串冒充提取结果。记录 hash 不等于实现失效检查；复用前必须比对。

接受必须经过现有 validator 的完整 gate；不得通过手写 PASS 更新 accepted 数。任务记录不能冒充 validator schema。各依赖变更按类型/body、proof、certificate 边传播失效；证书和 allowlist 的变化同样记录。

交付包括：目标对应表、各维度进度、表示偏离、复用/新增 bridge、卡点、已运行检查、有效性证据，以及沿用时间格式的新/更新报告。分开报告本次与累计数字，不硬编码总量或零积压。

最终检查 `git diff --check`，不覆盖他人改动；忽略偶然 cache（如 `.lia.cache`），不批量删除有意保留的证据。说明哪些检查未运行。

## 12. 完成标准

一项 translation 可以“已写出且编译通过”，但未经过语义验收就不能“翻译已认证”。
本 skill 的成功标准是：**契约忠实、表示一致、计算接口可验证、证据可交接、进度真实；而不是生成最多文件或声明最多 PASS。**

附加材料按需读取：
- [详细表示规则](references/representation-rules.md)
- [验证友好实现与证书边界](references/validation-friendly-patterns.md)
- [v0.4 翻译复用与纠错](references/v04-translation-memory.md)
- [证据索引](references/evidence-index.md)
- [安装后 smoke cases](references/skill-smoke-tests.md)
