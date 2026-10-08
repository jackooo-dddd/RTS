<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>证明系统已经报错，但你不知道这条错误在提示你检查什么。这份 skill 是一张“报错后先查哪里”的速查表，主要针对求和和算术表达式的改写失败。<br><strong>具体例子：</strong>你想用“1 × x = x”简化一个式子，系统却说找不到匹配位置。它会提醒你先检查当前目标：指定的位置真的有“1 × 某个数”吗？也许那一部分还写成求和，尚未变成乘法；这时反复尝试同一条乘法定理不会补上缺少的转换。<br><strong>它会怎么处理：</strong>根据错误文字找到相关检查项，再结合当时的目标判断下一步：是先把求和整理成乘法，还是当前已经离开了求和形式，需要换一类定理。它把难读的报错变成可执行的检查和修复建议。表中的具体报错和例子来自 Coq/MathComp，迁移到 Lean 时，这张速查表本身也需要重新建立。</span>

<span style="color:red">【Lean迁移总评】错误到下一步行动的框架可保留；具体签名库与 MathComp 状态案例需按 Lean 重新建立。整体重写力度：重。</span>

<span style="color:red">【Common Messages｜首要结构性问题 1】<a href="#lean-review-2">点击跳转</a><br><strong>改哪里：</strong>Common Messages 整张速查表的入口、分类和修复动作；它负责把一条报错变成“下一步先查哪里”。<br><strong>为什么：</strong>表原来依赖 Coq/SSReflect 的报错和 MathComp 中间表达式。Lean 同一道题可能报告另一类错误，也不会保证经历 iter 状态；只重写三个代码块仍然没有换掉真正起作用的诊断规则。<br><strong>替换（Rocq → Lean）：</strong>以真实 Lean 错误类别重建：改写匹配失败 → trace_state＋核对改写式；类型不匹配 → 核对 expected/actual；未知名称 → #check/import；实例合成失败 → #synth；未解决目标 → 检查剩余 goals。常数和案例 → rw [Finset.sum_const] 后读取真实状态，再 simp [Nat.mul_comm]。<br><strong>删除（仅未来 Lean 版）：</strong>旧 Coq 错误文字和 iter 轨迹作为 Lean 分类依据的规则；旧表只保留为迁移评审历史材料。<br><strong>新增（Lean 适配）：</strong>从目标 Lean 版本采集带上下文的 diagnostics，并验证每条“下一步”适用于对应目标，不能把候选分类写成已经采集的错误证据。<br><strong>保留：</strong>错误 → 原因检查 → 下一步这一速查表结构。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-2">Common Messages</a>；<a href="#lean-review-3">Diagnostic Example</a>。</span>

<span style="color:red">【Rocq 示例需转为 Lean 代码｜点击跳转】<a href="#lean-review-code-1">示例 1</a>；<a href="#lean-review-code-2">示例 2</a>；<a href="#lean-review-code-3">示例 3</a>。共 3 个原代码块，全部保留。</span>

---
name: coq-failure-signatures
description: Use when Coq or ssreflect rewrite errors are hard to interpret and you need error-message-to-action mappings for shape mismatches.
argument-hint: '[error message] [current goal form]'
user-invocable: true
---

<span style="color:red">【Frontmatter｜中改】<br><strong>改哪里：</strong>frontmatter 的 name 和 description 中 Coq/SSReflect 故障触发词。<br><strong>为什么：</strong>Lean 诊断不会沿用 mul1n/big_ord_recr 的 Coq 错误签名。<br><strong>替换（Rocq → Lean）：</strong>建议 name → lean-failure-signatures；description → Lean 改写匹配失败、type mismatch、unknown identifier、failed to synthesize、unsolved goals 等类别。<br><strong>删除（仅未来 Lean 版）：</strong>mul1n/big_ord_recr 的旧报错字符串触发条件。<br><strong>新增（Lean 适配）：</strong>具体英文文案、大小写从目标 Lean 版本实际日志取值，rewrite pattern not found 等只能作类别提示，不能假定为固定输出。</span>

# Failure Signatures

<span style="color:red">【Failure Signatures｜重改】<br><strong>本节在做什么：</strong>把难读的证明报错整理成速查表，帮助决定下一步先检查哪里。<br><strong>改哪里：</strong>Failure Signatures 的库定义和下方诊断表三列。<br><strong>为什么：</strong>换到 Lean 后，旧 Coq 报错不能继续代表相同原因，必须连同当时目标和引理类型判断。<br><strong>替换（Rocq → Lean）：</strong>“Coq 报错 → 缺失正规化步骤” → “Lean diagnostic＋当前目标/引理类型 → 检查动作”；表三列 → Lean 错误类别、需核实的条件、验证过的动作。<br><strong>删除（仅未来 Lean 版）：</strong>旧 Coq 签名作为 Lean 运行规则；原历史表留在迁移评审材料中，未来 Lean 版使用新表。<br><strong>新增（Lean 适配）：</strong>为每条新诊断记录实际上下文和动作结果；未观察到的错误不得伪装成现成证据。<br><strong>保留：</strong>错误 → 原因检查 → 下一步的说明方式。</span>

This reference maps common Coq and ssreflect rewrite errors to the missing normalization step.

<a id="lean-review-1"></a>

<span style="color:red">【Read the Error as a Shape Mismatch｜轻改】<br><strong>本节在做什么：</strong>提醒看到改写失败时，先核对系统实际显示的表达式。<br><strong>改哪里：</strong>Read the Error as a Shape Mismatch 的“读到错误后采取什么动作”。<br><strong>为什么：</strong>Lean 的 rw 匹配、名称解析、实例合成会产生不同故障；不能凭旧 Coq 文本一律判断缺少计数桥接。<br><strong>替换（Rocq → Lean）：</strong>当前表达式检查 → 临时 trace_state；候选引理类型检查 → #check 实际声明。rw 失败核对左端/改写方向/类型；名称或实例错误先核对 import/实例。<br><strong>保留：</strong>先查看真实目标、再决定下一步。错误位置、类型和方向的核对是通用方法，不是 Lean 独有机制。</span>

## Read the Error as a Shape Mismatch
Treat most failed rewrites as evidence that the current goal shape is different from the one in your head.

<a id="lean-review-2"></a>

<span style="color:red">【Common Messages｜基本重写｜需重建诊断规则库】<br><strong>本节在做什么：</strong>逐条解释常见错误，并给出相应的检查或修复动作。<br><strong>改哪里：</strong>Common Messages 的全部报错签名，以及右侧建议使用的 MathComp 引理。<br><strong>为什么：</strong>Lean 的报错和求和正规形不同；只换报错文字但保留旧动作仍会失败。<br><strong>替换（Rocq → Lean）：</strong>改写匹配失败 → <code style="white-space:pre-wrap">trace_state</code> 后查改写式与位置；类型不匹配 → 比较 expected/actual；未知名称 → <code style="white-space:pre-wrap">#check 全限定名</code> 并查 import；实例合成失败 → <code style="white-space:pre-wrap">#synth 实例类型</code>；未解决目标 → 查剩余目标并分支证明。旧引理建议按目标形状换为：mul1n → Nat.one_mul；mulnC → Nat.mul_comm；big_ord_recr → Fin.sum_univ_succ（Fin 索引首项）或 Finset.sum_range_succ（range 索引末项）；big_const_ord → Finset.sum_const。<br><strong>删除（仅未来 Lean 版）：</strong>No applicable tactic 这一 Coq 签名条目不能直接作为 Lean 入口；iter 中间态及其对应修复建议从未来 Lean 表中移除，重新按实际状态建立。<br><strong>新增（Lean 适配）：</strong>从实际目标版本日志收集英文错误串，记录发生位置和当时 goal，再验证每个建议动作。以上类别是重建表的提纲，不代替采集证据。</span>

## Common Messages

| Error message | What it means | What to do next |
|---|---|---|
| `Unable to unify "X * n" with "iter n (addn X) 0"` | A constant big operator has already reduced to `iter`, but not yet to multiplication. | Finish the `iter` normalization, or rewrite the other side back to big operator form first. |
| `The LHS of mul1n ... does not match any subterm` | There is no literal `1 * _` in the goal. | Do not apply `mul1n` yet. First reduce the branch or constant sum until `1 * _` actually appears. |
| `The LHS of mulnC ... does not match any subterm` | There is no multiplication node yet, or it is not the subterm you intended. | Inspect the goal and confirm whether you are still in `bigop` or `iter` form. |
| `The LHS of big_ord_recr ... does not match any subterm` | The goal is no longer a standard ordinal big operator head. | Restore a `\sum_(i < n)` shape before peeling the first term. |
| `No applicable tactic` after several rewrites | The proof has drifted across multiple equivalent forms without a stable intermediate target. | Freeze the current goal, choose one normal form, and add a bridge lemma toward it. |

<a id="lean-review-3"></a>

<span style="color:red">【Diagnostic Example｜重改】<br><strong>本节在做什么：</strong>用一个常数求和的例子，展示改写前后的表达式如何决定下一步。<br><strong>改哪里：</strong>Diagnostic Example 三个代码块之间的“初始目标 → 单步改写 → 中间状态”链。<br><strong>为什么：</strong>这是同一段证明的执行记录，Lean 的常数求和改写结果是基数倍数形式，不能把 Coq iter 状态当成 Lean 输出。<br><strong>替换（Rocq → Lean）：</strong>输入 → <code style="white-space:pre-wrap">(∑ _cpu : Fin num_cpus, X) = X * num_cpus</code>，其中 X、num_cpus : Nat；单步 rewrite big_const_ord → rw [Finset.sum_const]；读取结果后用 simp [Nat.mul_comm]。<br><strong>删除（仅未来 Lean 版）：</strong>旧 Coq iter 状态及专为该状态设计的后续修复说明，不再直接用作 Lean 示例。<br><strong>保留：</strong>三个代码块展示同一次改写的前后过程，不是三个独立定理。<br><strong>新增（Lean 适配）：</strong>以实际 Lean 运行结果更新第三块状态，保留采集它的同一次 tactic 上下文。</span>

## Diagnostic Example

If the goal started as:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>写出一个待证明的等式：有 num_cpus 个处理器，每个处理器对应同一个自然数 X，把这些 X 相加，应当等于 X × num_cpus。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>第一块初始目标中的 ordinal 索引和 MathComp 求和记号。<br><strong>为什么：</strong>Lean 需要真实索引类型和自然数求和值；Fin num_cpus 恰有 num_cpus 个元素。<br><strong>替换（Rocq → Lean）：</strong>目标声明 → <code style="white-space:pre-wrap">example (num_cpus X : Nat) :&#10;    (∑ _cpu : Fin num_cpus, X) = X * num_cpus := by</code>；这是证明开头，证明体接下面两步。<br><strong>新增（Lean 适配）：</strong>文件前使用 import Mathlib 与 open scoped BigOperators。</span>

```coq
\sum_(cpu < num_cpus) X = X * num_cpus
```

then after:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>对上面的常数求和做一次改写，再查看系统实际产生了什么新目标，从而决定下一步用哪条定理。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>第二块 rewrite big_const_ord. 这一单步指令。<br><strong>为什么：</strong>Lean 使用 Finset 常数求和定理，必须查看它实际生成的目标再选后续简化。<br><strong>替换（Rocq → Lean）：</strong><code style="white-space:pre-wrap">rewrite big_const_ord. → rw [Finset.sum_const]</code>。<br><strong>新增（Lean 适配）：</strong>为采集示例状态，在该行后临时加入 <code style="white-space:pre-wrap">trace_state</code>；案例核实后可去掉此调试指令。</span>

```coq
rewrite big_const_ord.
```

the proof state may become:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展示 Coq 在上一步改写后可能出现的中间目标：从 0 开始重复加 X，共加 num_cpus 次；后面还要把它化成乘法。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>第三块 iter 中间目标及它的后续简化说明。<br><strong>为什么：</strong>Finset.sum_const 给出 s.card • X，不按 Coq iter 轨迹表达重复加法。<br><strong>替换（Rocq → Lean）：</strong>旧状态文本 → 上一步 trace_state 的实际输出；其中 Finset.univ 的基数等于 num_cpus，后续用 <code style="white-space:pre-wrap">simp [Nat.mul_comm]</code> 完成简化。<br><strong>删除（仅未来 Lean 版）：</strong>旧 iter 状态这一行；其位置由实际 Lean 输出替代，不能仅改名后将旧行伪装成新输出。</span>

```coq
iter num_cpus (addn X) 0 = X * num_cpus
```

At that point:
- `mulnC` is too early if multiplication is not yet on the left.
- `big_ord_recr` is too late because the left side is no longer a big operator.
- the correct move is a bridge step from `iter` to multiplication, or a different earlier normalization plan.

<a id="lean-review-4"></a>

<span style="color:red">【Practical Rule｜中改】<br><strong>本节在做什么：</strong>给出每次改写前的简短检查方法，避免在目标不匹配时继续盲试。<br><strong>改哪里：</strong>Practical Rule：保留调试表原三行，在其后补充检查字段；改写表后的“字面没有出现就添加 bridge”决策。<br><strong>为什么：</strong>打印文字不相同未必缺少数学等式，可能只是可展开的封装；Lean 还需要核对 elaboration 后实际采用的隐式参数、类型和实例。因此不能只看字面是否匹配就创建桥接。<br><strong>替换（Rocq → Lean）：</strong>原末句的自动加桥接 → 按原因处理：只差定义展开时，尝试 <code style="white-space:pre-wrap">change 目标表达式</code>（须定义等同）或 <code style="white-space:pre-wrap">simp only [实际定义]</code>；索引/数值域不一致时，先核对转换关系并证明所需等式；确认确实缺少连接等式后，才写 <code style="white-space:pre-wrap">have hBridge : 左侧 = 右侧 := by&#10;  完成连接证明</code> 再按方向 rw。这里中文是占位说明，实际 API 需按 Lean Prosa 当前声明确认。<br><strong>删除（仅未来 Lean 版）：</strong>删除“字面没有出现就一定缺桥接”的判定；不删除原三行观察字段。<br><strong>新增（Lean 适配）：</strong>原表后追加 <code style="white-space:pre-wrap">Index/value types:&#10;Rewrite direction: rw [h] / rw [←h]&#10;Actual Lean error and source position:</code>。类型/方向/错误位置记录也是 Rocq 可用的通用方法，这里只是适配 Lean；需要额外核实的是 Lean elaboration 最终确定的参数、类型和实例，不能仅凭原表打印文字猜测。<br><strong>保留：</strong>原三行 Current head form、Lemma left-hand side、Does the left-hand side literally occur in the goal?；最后一行只作观察，不作桥接存在与否的充分判据。</span>

## Practical Rule
Before each rewrite, write down:

```text
Current head form:
Lemma left-hand side:
Does the left-hand side literally occur in the goal?
```

If the answer is no, add a bridge lemma instead of trying another algebraic rewrite.