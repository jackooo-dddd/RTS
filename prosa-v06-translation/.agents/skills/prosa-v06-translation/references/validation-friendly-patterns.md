# Validation-friendly translation：实施模式

## 1. 何时必须先 probe

新递归、依赖模式匹配、proof-carrying data、class carrier 搬移、choice/Nat.find、有限枚举和 big operator 改写，应在为它们写大量下游证明前进行最小预检。

只检视当前声明及其必要依赖，避免整个 Mathlib/full body 展开。记录新边界是什么、已有 bridge 缺哪一步，而不是只写“import 太复杂”。

## 2. 验证路径选择

### A. 已有基础上的直接对应

`instant := nat → instant := Nat`：检查 alias 的真实 body，实例化已有 Nat relation，再绑定本轮 source/export/import。不要重复写一套独立 Nat 理论。

简单 `f n := n + 1`：组合输入、加法和常量 bridge。前提是这些 bridge 的 imported operations 与本轮一致，不能仅按名字复用。

### B. 递归定义

目标不是强制 compiler 生成某一种内部 term，而是获得 **和实际定义绑定、可检查且可复用的计算规律**。

下面是一个表达结构递归的说明性例子，不是 Prosa declaration，也不是已在项目中认证的翻译：

```lean
namespace ValidationFriendlyExample

def prefixTotal (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixTotal f n + f n

theorem prefixTotal_zero (f : Nat → Nat) :
    prefixTotal f 0 = 0 := by
  rfl

theorem prefixTotal_succ (f : Nat → Nat) (n : Nat) :
    prefixTotal f (n + 1) = prefixTotal f n + f n := by
  rfl

end ValidationFriendlyExample
```

实际执行时必须在固定版本检查这个例子或真实声明；本 skill 包的文本检查不等于 Lean 编译证据。

对于 `search_arg`：保留 `[a,b)`、返回哪个索引、比较关系方向和 ties 时选哪一项。证明“返回某个最优元素”可能弱于源的确定性返回值对应，不能替代。

若有已检查的 `.eq_1/.eq_2`，按递归参数归纳，组合 Nat/Bool/Option/function bridges。出现 `Nat.brecOn` 不必重写定义。只有现有 equations 无法有效工作、等价改写确实更简单且代价值得时，才比较新方案。

### C. 依赖记录

先列数据投影与 law，再建立合法对象的映射/相关性。需要全域对应时，证明覆盖/反向构造；只处理 canonical instances 时标清范围。不能用一个永远为 False 的输入 relation 获得空洞“成功”。

### D. theorem statement

核对完整 source/target type，证明其构成部分对应并按连接词组合。

“源 theorem 已证，目标 theorem 已证，所以 `P ↔ Q`”不能单独证明翻译忠实；甚至不引用两侧 theorem、却分别重新证明任意真命题，仍可能得到无意义的匹配。

需要对原子 predicate、数据操作、量词域和参数 relation 建立对应。诸如 `neqP` 的 universally valid reflection schema 可以有很短的证明，但必须绑定 equality/Bool 观察和准确的 view/type，不能靠可证性任意匹配另一条恒真式。

## 3. 什么 equations 可以用

允许：本目标函数的 recursion equations、已证定义等式、先前通过审计的 generic logical/arithmetic bridges。

不允许：直接假设当前函数的 source-target equivalence；以正在验证的业务 theorem 为自身翻译正确性的依据。

在严格 Rocq 重检查路径中，Lean equations 的 proof body 应一并导入且通过 Rocq kernel，或在 Rocq 对真实导入体证明该 equation。只有 theorem statement 被导入时，它还未在 Rocq 获得证明；记录为 statement-only dependency，不能加入“无条件可信”白名单。

即使 Lean 侧 `#print axioms` 干净，也不能把这项检查说成“equation proof 已在 Rocq 重验”。区分每一层实际做过什么。

## 4. 受控 normalization

优先保留已知运算头、展开 typeclass wrapper 和当前需要的一个递归步骤。
如果采用另一种表示 `g`，需检查 `f = g` 或所需 relational equivalence，并绑定实际 `f` 和 `g`，不能复制相似源码做 guard。

建议的负测包含：端点偏移、初始值 0→1、返回 some 候选改变、重复元素去重、关系方向颠倒。目标是确认相应 type/semantic gate 会拒绝，而不是只看编译能否通过。

不要把 `Meta.isDefEq` 记录、string hash 或 LLM self-review称作 kernel proof。

## 5. 源 theorem 提取不是没有边界的捷径

旧 source proof 在新 Rocq 下失败，不要求重新翻译旧 proof，也不能随意插 `Admitted`。
使用仓库已有提取器时检查：

- 来自固定 commit 的原 body/type；proof 与 computational Definition/Defined 不能误分。
- 已 elaborated 完整类型与 Section 参数，非单看原 theorem header。
- namespace、local notation、隐式参数、canonical/instance 环境。
- 经过语法兼容变换前后的源字节和类型证据。
- 提取输出、原始类型证据和证书之间的绑定。

源字节 hash 证明版本/字节身份，不证明新提取器语义正确。提取器中新加的语义路径必须被检查并透明记录；不能因为生成模块编译成功就自动 accepted。

## 6. 关系参数、foundation 与真正缺口

区分四类：

1. 源 theorem 本来就有的假设，例如 R transitive。
2. 相关输入约定，例如 `SubNatFunRel fR fL`；需要记录范围和可构造性。
3. 已批准、明确披露的基础，如项目 `interpret_strict` 或 importer equality/UIP。
4. 尚未证明的操作对应，例如“假设 source service 与 target service 相同”。

第 2 类不是自动作弊；第 4 类不能伪装成第 2 类。`semantic_premises=[]` 只可表示没有未闭合的额外语义义务，不能声称 certificate type 没有任何关系前提。

`Print Assumptions` 对全局 axioms 有用，但不会枚举所有绑定进类型的局部条件，也不会把正常已证明 helper 一律显示为公理。反循环检查同时依赖完整 proof/constant 依赖分析；regex token 列表只能辅助。

若只验证 source carrier 对应某个 canonical target instance，不报告为“任意 Lean carrier/instance 都已双向覆盖”。若只证明 record 的 underlying list roundtrip，不报告为所有 proof 字段的字面等同。

## 7. 缓存、哈希与吞吐

固定版本且已校验的外部依赖 cache 可以复用；项目与证书产物必须绑定本轮输入和构建计划。语义 fresh 不等于每次重建全部 Mathlib。

先把每个阶段的真实进度写入状态，独立于最后 publication。预备 semantic proof 编译成功可记录为 intermediate evidence，但不得加入 accepted 数。

当一个 importer/primitive 阻塞当前边界时，最多执行约定的有限种方法，保留精确目标与可复现 probe，继续独立 cluster；不要把扩大白名单或添加公理算成新的证明方法。
