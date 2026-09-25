# 表示规则：默认、边界和待审查项

本文件细化 SKILL.md 第 6 节。权威仍是 pinned v0.6 及仓库批准的 mapping policy。不要将这里的说明当成新增的 semantic certificate。

## 1. 基本类型、sort 和能力

`nat → Nat`、`bool → Bool`、普通 `option → Option`、积/和类型保持构造分支，是复用默认。语法相似不等于导回 Rocq 后成为同一 inductive；实际验证需已有桥接。

时间和工作量 aliases 默认仍是自然数，不擅自换 `Int`、`Real`、有界整数或额外 subtype。若源带非负/正值假设，保留原假设，而不是修改 carrier 来隐藏它。

对 `Type/Set/Prop/SProp` 分别读取真实 sort、universe 和依赖消去用途。不要以同一字符串 `Type` 代表所有层级；不要默默加 `Inhabited`、`Nonempty`、有限性或 choice 解决 elaboration。

### eqType

当前项目默认保留 carrier 和 `DecidableEq` 能力。对从 eqType 解包来的参数，用实际声明边界保证证据存在：

```lean
-- 说明性模板；应在固定项目中检查最终类型，不是已认证产物。
class Arrival (Job : Type u) [DecidableEq Job] where
  arrival : Job → Nat
```

在实际文件中声明 `universe u`。若将 `[DecidableEq Job]` 只放在 Section 风格的 `variable` 中，Lean 可能不把未使用参数保留到最终声明，必须检查 `#check @Arrival` 或实际目标。

这是项目的保守接口约定，不是“任何不带 DecidableEq 的 Arrival 类数学上都错”。发现有意泛化应另记表示决策和验证范围，不偷偷切换 policy。

Boolean equality 优先使用已经核实的 `decide (x = y)`；若使用 `x == y`，核实 `BEq` 与命题相等的一致性，不能只提供一个任意 Boolean comparator。

不要仅从存在一个源→目标 DecidableEq 构造，宣称已经覆盖任意目标类型、任意实例或所有记录结构。明确证书针对同一 carrier、相关 carrier、canonical instance 还是任意相关 instance。

### finType

保留 carrier、有限枚举和 equality 证据。对记录内部 Core，用它自带的 `Fintype`/`DecidableEq` 建立局部实例，避免同名全局实例改变选取。

有限集合上的交换运算通常无需保持枚举顺序，但必须证明覆盖和无重复；若源公开枚举列表或做顺序敏感 fold，顺序也是可观察语义。

## 2. List、set 与访问

| 对象 | 默认 | 危险替换 |
|---|---|---|
| `seq T` | `List T` | 转 Finset 去掉重复项或顺序 |
| 外延 `{set T}` | `Finset T`，保留源 carrier 的有限性语境 | 用任意 list 却不记录 uniqueness/extensional relation |
| Prosa `seqset.set` | 具有 underlying List 和 Nodup law 的结构 | 因为名字是 set 就改成 Finset |
| `nth default xs i` | 保持越界 fallback 的访问方式 | 换成要求 `i < length` 的访问而多加前提 |
| 源 head/last 的默认值 | 相同默认值和空列表行为 | 直接换返回 Option 的 API而不建立对应 |
| `map`、`filter`、`count`、`zip` | 保持各自顺序/长度/计数规则 | 把 count 变 membership；改变 zip 截断规则 |

filter 的 Bool predicate 和 theorem 中的 Prop membership 分别处理。`uniq` 与 `List.Nodup` 需要 bridge；有一个 Nodup proof 字段不等于整个记录对应已完成。

对于携带 proof 的 record，通常证明数据投影和 laws 的对应，不要求两边 proof term 字节相同。若只证 observable roundtrip，不把它报告为所有 records/proofs 的字面同构。

## 3. Bool、Prop、reflect

当源定义返回 bool，它的结果是数据，默认保持 Lean Bool。源命题通过 `is_true b` 使用该 Bool 时，可翻译为 `b = true`。

`decide P` 是合法 Boolean computation，只要使用了已知且相符的可计算 Decidable instance；经过 Prop 本身并不使计算错误或不可计算。不要把“禁止 Prop-mediated decide”写成全局原则。

对 `scheduled_in`，项目已经专门选定有限 Bool-or fold，应沿用该决策，而不是自行替换。将这个局部决策与一般 Bool/Prop 规则分开。

`reflect P b` 是带构造信息的 view。翻成 `(b = true ↔ P)` 仅在已审查的 view relation/消费方式允许时使用。若下游要在 Type/Set 中消去 view 构造数据，单纯 Prop 的 iff 可能不足；使用合适的 Decidable/view encoding 或提交表示审查。

不能把“从 Boolean 证明直接写 `have h : x = y := by decide`”当作通用步骤；`decide` 不能替代对输入证明的反射转换。

## 4. 算术与聚合

自然数减法为截断减法；增加/复用已绑定 actual operations 的 bridge。除法和模必须额外核对除数为 0 的行为，不能添加源中没有的非零假设绕过。

集合/序列/区间聚合的不同情形：

- 自然数区间 `[m,n)`：`Finset.Ico m n` 的求和值语义，覆盖 `m=n`、`n<m` 和单点。
- 序列求和：保留每一次出现，如 `[x,x]` 应贡献两次；List fold 不要求输入本来无重复。
- 集合求和：以集合 membership 和唯一性对应。
- filter：保留谓词真假；单位元与源一致。
- 泛型 bigop：保留 carrier、operation、identity、已有 algebraic laws；不能默默特化成 Nat sum。
- 从 foldr 换 foldl：检查单位元、结合律和 fold 方向，不能仅因“都叫 fold”替换。
- 从 sequence fold 换 Finset fold：额外检查重复项、顺序无关性和所需交换律。
- max/min 聚合：源空集合/空序列有默认值时，不擅自使用需要非空证据的 API。

先定义精确对应，再选择最方便的 Lean lemma。用 normalization 改写实现时，输出 guard 必须绑定实际 compiled original/normalized expressions；仅 `Meta.isDefEq` 的成功日志不是独立 kernel 证书。

## 5. ProcessorState 和结构

保持批准的：

```text
ProcessorState
  State
  Core
  Core 的 Fintype / DecidableEq
  scheduled_on : Job → State → Core → Bool
  supply_on    : State → Core → work
  service_on   : Job → State → Core → work
  每核 service ≤ supply
  未 scheduled 的每核 service = 0

派生：scheduled_in、supply_in、service_in
```

名称可以遵守已存在 mapping，但不同时维护语义不同的 snake_case/camelCase 实现。示例中的字段清单仍须与 pinned source 逐项核对，不以这份文字替代完整 class type。

外置 State 与删掉 per-core operations 是两个独立选择；前者并不必然造成后者。当前采用 nested carriers 是已批准的项目决策，不是其他 Lean 编码均不正确的定理。

Class/Record 到 Lean structure/class 的选择保留实例使用语义。不得用 `Classical.choice` 自动制造本来应作为输入的结构，也不得新增“总能 service”等源未要求的 laws。

## 6. 尚未批准的其他表示

`ordinal → Fin`、有限函数、dependent sum、HB mixin、setoid/morphism、CoFixpoint 等，在本任务触及时读取真实 v0.6 源、下游和现行 policy。没有批准方案就局部审查，不自动提升为新默认。

特别注意：

- 有限域上的全函数不等于一般 `Finsupp`；后者额外涉及零元和有限 support。
- Rocq Canonical Structure/HB 与 Lean typeclass 并非逐命令同构；应保留被计算和类型实际观察的结构，记录实例选择。
- 源工具性 Ltac/Hint/Notation 无须逐句模拟 SSReflect，但要登记替代用途。无 public named declaration 不等于文件无贡献。
- `util/all.v` 之类 aggregator 不靠空文件完成；单独核对模块导出、实例和 notation 范围。
