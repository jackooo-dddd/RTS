<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>证明系统已经报错，但你不知道这条错误在提示你检查什么。这份 skill 是一张“报错后先查哪里”的速查表，主要针对求和和算术表达式的改写失败。<br><strong>具体例子：</strong>你想用“1 × x = x”简化一个式子，系统却说找不到匹配位置。它会提醒你先检查当前目标：指定的位置真的有“1 × 某个数”吗？也许那一部分还写成求和，尚未变成乘法；这时反复尝试同一条乘法定理不会补上缺少的转换。<br><strong>它会怎么处理：</strong>根据错误文字找到相关检查项，再结合当时的目标判断下一步：是先把求和整理成乘法，还是当前已经离开了求和形式，需要换一类定理。它把难读的报错变成可执行的检查和修复建议。表中的具体报错和例子来自 Coq/MathComp，迁移到 Lean 时，这张速查表本身也需要重新建立。</span>

<span style="color:red">【Common Messages｜首要结构性问题 1】<a href="#lean-review-2">点击跳转</a><br><strong>为什么会有结构性问题：</strong>这张表负责根据报错判断“出了什么问题，下一步做什么”。它原来使用 Coq 的报错和 MathComp 改写后的表达式作为线索；换到 Lean，同一道题的报错和中间目标可能完全不同。即使几个示例已经改成 Lean，旧表也可能把错误分到错误的类别，给出不适用的修复动作。<br><strong>Lean 中大致怎么做：</strong>用实际 Lean 报错、当时的目标和候选定理类型重建速查表，验证每条建议适用于什么情形。保留“错误 → 检查原因 → 下一步”的阅读方式。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-2">Common Messages</a>；<a href="#lean-review-3">Diagnostic Example</a>。</span>

<span style="color:red">【Rocq 示例需转为 Lean 代码｜点击跳转】<a href="#lean-review-code-1">示例 1</a>；<a href="#lean-review-code-2">示例 2</a>；<a href="#lean-review-code-3">示例 3</a>。共 3 个原代码块，全部保留。</span>

---
name: coq-failure-signatures
#<span style="color:red">【description】建议改为“解释 Lean 的实际报错，并结合当前目标和候选定理类型选择检查动作；用于改写不匹配、类型或实例错误，以及未完成目标难以定位的情况”。理由：旧 Coq 报错文字不能作为 Lean 的固定触发条件，具体文案应以实际诊断为准。</span>
description: Use when Coq or ssreflect rewrite errors are hard to interpret and you need error-message-to-action mappings for shape mismatches.
argument-hint: '[error message] [current goal form]'
user-invocable: true
---



# Failure Signatures <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【把难读的证明报错整理成速查表，帮助决定下一步先检查哪里。】</span>

<span style="color:red"><strong>为什么要改：</strong>Coq/SSReflect 的错误串属于旧后端，不能继续作为 Lean 的故障签名。<br><strong>怎么改：</strong>以当前 Lean diagnostic、目标和声明为入口，替换具体签名与相关库接口。</span>

This reference maps <span style="color:gray">common Coq and ssreflect rewrite errors</span> to the missing normalization step.

<a id="lean-review-1"></a>



## Read the Error as a Shape Mismatch <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【提醒看到改写失败时，先核对系统实际显示的表达式。这一原则保留，在 Lean 中用当前目标与实际诊断核对；可用 trace_state 和 #check 辅助。】</span>
Treat most failed rewrites as evidence that the current goal shape is different from the one in your head.

<a id="lean-review-2"></a>



## Common Messages <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【逐条解释常见错误，并给出相应的检查或修复动作。｜基本重写】</span>

<span style="color:red"><strong>为什么要改：</strong>① 第 1/4 行依赖 MathComp 的 iter/ordinal 状态，Lean 常数和产生基数倍数，拆项取决于实际索引。<br>② 第 2/3 行的 mul1n、mulnC 是旧库名称；第 5 行的 No applicable tactic 及其余错误串也属于 Coq，不能直接作为 Lean 签名。<br><strong>怎么改：</strong>使用真实 Lean 错误与目标重建对应接口；可查 Nat.one_mul、Nat.mul_comm、Finset.sum_const。拆项按 Fin/Finset.range 选择 Fin.sum_univ_succ/Finset.sum_range_succ，保持原索引范围。</span>

| Error message | What it means | What to do next |
|---|---|---|
| <span style="color:gray">`Unable to unify "X * n" with "iter n (addn X) 0"`</span> | <span style="color:gray">A constant big operator has already reduced to `iter`, but not yet to multiplication.</span> | <span style="color:gray">Finish the `iter` normalization, or rewrite the other side back to big operator form first.</span> |
| <span style="color:gray">`The LHS of mul1n ... does not match any subterm`</span> | There is no literal `1 * _` in the goal. | Do not apply <span style="color:gray">`mul1n`</span> yet. First reduce the branch or constant sum until `1 * _` actually appears. |
| <span style="color:gray">`The LHS of mulnC ... does not match any subterm`</span> | There is no multiplication node yet, or it is not the subterm you intended. | Inspect the goal and <span style="color:gray">confirm whether you are still in `bigop` or `iter` form</span>. |
| <span style="color:gray">`The LHS of big_ord_recr ... does not match any subterm`</span> | The goal is no longer <span style="color:gray">a standard ordinal big operator head</span>. | <span style="color:gray">Restore a `\sum_(i < n)` shape before peeling the first term.</span> |
| <span style="color:gray">`No applicable tactic` after several rewrites</span> | The proof has drifted across multiple equivalent forms without a stable intermediate target. | Freeze the current goal, choose one normal form, and add a bridge lemma toward it. |

<a id="lean-review-3"></a>



## Diagnostic Example <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【用同一个常数求和例子，展示一次改写前后的目标如何决定下一步。】</span>

If the goal started as:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>要证明 num_cpus 个相同的自然数 X 相加，等于 X × num_cpus。<br><strong>2）怎么换成 Lean 代码：</strong>原 ordinal 求和是 MathComp 记号。Lean 用恰有 num_cpus 项的 Fin 索引：<code style="white-space:pre-wrap">example (num_cpus X : Nat) :&#10;    (∑ _cpu : Fin num_cpus, X) = X * num_cpus := by</code>。前置 import Mathlib 与 open scoped BigOperators；这是证明开头，后两段接着处理同一目标。</span>

```coq
\sum_(cpu < num_cpus) X = X * num_cpus
```

then after:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>做一次常数求和改写，查看随后生成的目标。<br><strong>2）怎么换成 Lean 代码：</strong>big_const_ord 不属于 Lean 库；对应一步是 <code style="white-space:pre-wrap">rw [Finset.sum_const]&#10;trace_state</code>。记录实际状态再选后续简化，案例核实后可去掉临时 trace_state。</span>

```coq
rewrite big_const_ord.
```

the proof state may become:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展示 Coq 改写后用 iter 表示的重复加法，下一步还要化成乘法。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 的 Finset.sum_const 给出 s.card • X，不要求经过这个 iter 状态；此处必须换成上一条实际输出，再用 <code style="white-space:pre-wrap">simp [Nat.mul_comm]</code> 等合适步骤简化。</span>

```coq
iter num_cpus (addn X) 0 = X * num_cpus
```

At that point:

<span style="color:red"><strong>为什么要改：</strong>下方三条建议依赖原 iter/ordinal 中间态；Lean 的真实结果不同，不能只换引理名后沿用“太早/太晚/必须桥接”的判断。<br><strong>怎么改：</strong>根据上一条实际 Lean 输出重新选择动作；先核对当前表达式的原则保留。</span>

- <span style="color:gray">`mulnC` is too early if multiplication is not yet on the left.</span>
- <span style="color:gray">`big_ord_recr` is too late because the left side is no longer a big operator.</span>
- <span style="color:gray">the correct move is a bridge step from `iter` to multiplication</span>, or a different earlier normalization plan.

<a id="lean-review-4"></a>



## Practical Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【给出每次改写前的简短检查方法，避免在目标不匹配时继续盲试。】</span>
Before each rewrite, write down:

```text
Current head form:
Lemma left-hand side:
Does the left-hand side literally occur in the goal?
```



If the answer is no, add a bridge lemma instead of trying another algebraic rewrite.