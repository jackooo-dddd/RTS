<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>一行很短的证明代码实际做了好几件事，系统只说这一行失败，你却看不出是哪一步出了问题。这份 skill 用来把这类紧凑写法展开，让隐藏的中间目标和未完成部分显露出来。<br><strong>具体例子：</strong>一行代码连续使用三个等式改写。失败可能发生在第二个等式，也可能三个等式都改写成功了，但最后还剩一个没有证明的目标。另一种情况是同一条命令同时处理两个分支，其中一个完成了，另一个仍需要额外论证。只看那一行短代码，很难区分这些情况。<br><strong>它会怎么处理：</strong>先保留原来要做的步骤，把这一处紧凑写法展开，重新运行并查看具体失败位置或剩余目标，再决定是换改写、补前提，还是分别处理分支。原 Coq/SSReflect 版本常通过去掉 by 来展开；Lean 中 by 的含义不同，不能照搬这个动作，但逐步检查内部证明步骤的目的仍然适用。</span>

<span style="color:red">【Core Rule｜首要结构性问题 1】<a href="#lean-review-2">点击跳转</a><br><strong>为什么会有结构性问题：</strong>这份 skill 最核心的动作是“去掉 by，再运行里面的步骤”，以便看清 SSReflect 紧凑证明哪里失败。但 Lean 的 by 是进入 tactic 证明块的入口，删掉后里面的命令通常不再构成合法证明。失效的是调试动作本身，因此把示例里的 tactic 名改成 Lean 名称仍然不够。<br><strong>Lean 中大致怎么做：</strong>保留 by，把块内连续改写、自动化或分支处理拆成较小步骤，逐步查看目标和错误。局部证明也在自己的块内检查，修好后再决定是否合并内部步骤。 <a href="https://lean-lang.org/doc/reference/latest/Tactic-Proofs/">Lean 官方说明</a>。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-1">When to Use</a>；<a href="#lean-review-2">Core Rule</a>；<a href="#lean-review-3">Why `by` Hides the Useful Error</a>；<a href="#lean-review-4">Required Procedure</a>；<a href="#lean-review-5">First Revealed Error -&gt; Real Cause</a>；<a href="#lean-review-7">Anti-Patterns</a>；<a href="#lean-review-9">Success Condition</a>。</span>

<span style="color:red">【Rocq 示例需转为 Lean 代码｜点击跳转】<a href="#lean-review-code-1">示例 1</a>；<a href="#lean-review-code-2">示例 2</a>；<a href="#lean-review-code-3">示例 3</a>；<a href="#lean-review-code-4">示例 4</a>；<a href="#lean-review-code-5">示例 5</a>；<a href="#lean-review-code-6">示例 6</a>；<a href="#lean-review-code-7">示例 7</a>；<a href="#lean-review-code-8">示例 8</a>；<a href="#lean-review-code-9">示例 9</a>；<a href="#lean-review-code-10">示例 10</a>；<a href="#lean-review-code-11">示例 11</a>；<a href="#lean-review-code-12">示例 12</a>；<a href="#lean-review-code-13">示例 13</a>；<a href="#lean-review-code-14">示例 14</a>；<a href="#lean-review-code-15">示例 15</a>；<a href="#lean-review-code-16">示例 16</a>；<a href="#lean-review-code-17">示例 17</a>；<a href="#lean-review-code-18">示例 18</a>。共 18 个原代码块，全部保留。</span>

---
name: by-expansion-diagnostics
#<span style="color:red">【description】建议改为“定位 Lean 多步改写、组合 tactic 或分支处理中具体失败的步骤；保留 by，拆开块内动作并查看实际目标，再区分改写不匹配、缺少前提和分支未完成”。理由：Lean 的 by 是证明块入口，不能删除它来展开诊断。</span>
description: 'Debug Coq and ssreflect `No applicable tactic` failures that arise on `by ...` lines by removing `by`, exposing the remaining goals, and treating the first revealed proof state as the real error signal. Use when a compact `by rewrite`, `by apply:`, `have ... by ...`, or `case ...; by ...` script hides whether the failure is a rewrite mismatch, a missing assumption, or an unexpected branch split.'
#<span style="color:red">【argument-hint】建议改为“提供失败的 Lean tactic 块、当前目标，以及拆开块内步骤后出现的第一条具体错误”。理由：明确展开的是 by 内部的步骤，保留合法的证明结构。</span>
argument-hint: 'Describe the failing `by ...` line, the current goal, and the first message after expanding it.'
user-invocable: true
---



# By Expansion Diagnostics <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【帮助展开紧凑的证明代码，找出究竟是哪一步或哪个分支失败。】</span>

<a id="lean-review-1"></a>



## When to Use <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出一行代码包含多个动作、却只给出笼统错误时适合使用本 skill 的情况。｜重改】</span>

<span style="color:red"><strong>为什么要改：</strong>旧入口依赖 SSReflect by 和 No applicable tactic；Lean by 是普通证明块入口，不能据此判断存在压缩失败。<br><strong>怎么改：</strong>用真实失败的连续改写、局部证明或分支分发触发诊断。</span>

- <span style="color:gray">Coq reports `No applicable tactic` on a line that starts with `by` or ends in a compressed `...; by ...` tail.</span>
- A large model reacts to the flat error by trying random rewrites or lemma applications.
- You do not know whether the real failure is a rewrite mismatch, a missing assumption, or an extra branch.

<span style="color:red"><strong>为什么要改：</strong>① apply: 和 have ... by ... 是旧语法。② Coq case 新建分类，Lean case 选标签。③ 原分号分发分支步骤的作用不能换成 Lean 普通分号。<br><strong>怎么改：</strong>用 apply、have h : P := by、cases/by_cases；需要向各支分发步骤时用 &lt;;&gt;。</span>

- The failing line is a short script such as <span style="color:gray">`by rewrite ...`</span>, <span style="color:gray">`by apply: ...`</span>, <span style="color:gray">`have H : P by ...`</span>, or <span style="color:gray">`case E: x; by ...`</span>.

<a id="lean-review-2"></a>



## Core Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【要求先展开当前失败片段并查看剩余目标，再尝试更换证明步骤。｜基本重写｜核心操作在 Lean 失效】</span>

<span style="color:red"><strong>为什么要改：</strong>Lean by 构造 tactic 证明块，不承担这里 SSReflect 的压缩命令角色。<br><strong>怎么改：</strong>把调试对象改为 by 块内的复合步骤，保留入口。</span>

<span style="color:gray">Treat `by` as a proof-state compressor, not as a diagnostic tactic.</span>


When `by ...` fails, do not immediately try other tactics.

<span style="color:red"><strong>为什么要改：</strong>删掉 Lean by 后，内部 tactic 通常不再组成合法证明；这会引入新的语法问题。<br><strong>怎么改：</strong>保留 by，只拆内部动作，再查看每步目标。</span>

<span style="color:gray">Remove `by`, rerun the exact payload</span>, and inspect the first revealed proof state. That first revealed state is the real debugging signal.

<a id="lean-review-3"></a>



## Why `by` Hides the Useful Error <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【解释原 SSReflect 的紧凑写法为什么可能只报告整行失败而没有直接显示未完成部分。｜基本重写】</span>

<span style="color:red"><strong>为什么要改：</strong>这句话描述 SSReflect by 的行为。Lean 的完整 by 块也须完成证明，但它是语法入口，不能删除来展开。<br><strong>怎么改：</strong>分别说明内部步骤失败和最终仍有目标两种情况，保留证明块。</span>

<span style="color:gray">`by tac.` means: run `tac` and close every resulting goal immediately.</span>

If `tac` does any of the following,
- leaves one goal unsolved,
- opens two or more goals,
- rewrites the wrong normal form,
- applies a lemma with mismatched premises,


<span style="color:red"><strong>为什么要改：</strong>这是旧 Coq 的错误报告方式，不能预设 Lean 也给出相同的笼统错误。<br><strong>怎么改：</strong>记录 Lean 真实错误及其位置，不以旧字符串作唯一触发依据。</span>

then <span style="color:gray">Coq often reports only `No applicable tactic` at the compressed line</span>.

After expansion, the hidden signal usually becomes one of these:
- a concrete remaining goal,

<span style="color:red"><strong>为什么要改：</strong>下面四条是 Coq 诊断词汇，不是 Lean 的现成错误签名表。<br><strong>怎么改：</strong>用实际 Lean 输出和当时目标核实新的分类；保留读取具体剩余目标的方法。</span>

- <span style="color:gray">`Expected a single focused goal but 2 goals are focused.`</span>,
- <span style="color:gray">`The LHS of ... does not match any subterm of the goal.`</span>,
- <span style="color:gray">`Cannot apply lemma ...`</span>,
- <span style="color:gray">`No assumption in ...`</span>.


<span style="color:red"><strong>为什么要改：</strong>“扁平 by 错误”沿用了 SSReflect 的失败模型；Lean 的失败应定位到块内步骤或未完成目标。<br><strong>怎么改：</strong>保留优先处理具体诊断的原则，替换旧错误称呼及触发机制。</span>

That specific message is what you should debug, not <span style="color:gray">the original flat `by` failure</span>.

<a id="lean-review-4"></a>



## Required Procedure <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【给出保留失败片段、逐步展开、读取具体错误并选择修复方式的顺序。｜基本重写】</span>
1. Freeze the exact failing line.
   - Copy the `by ...` line exactly.
   - Do not rewrite its payload yet.
2. Expand only that one compression boundary.

   <span style="color:red"><strong>为什么要改：</strong>Lean by 是证明块入口，删除它会改变或破坏证明结构。<br><strong>怎么改：</strong>拆分 by 内部步骤，保持入口和原证明意图。</span>

   - <span style="color:gray">Remove `by`.</span>
   - Keep the original tactic payload unchanged.
3. Re-run immediately.
   - Record the first new message.
   - Record the number of focused goals.
4. Classify the revealed signal.
   - One remaining goal: the compressed script was incomplete.

   - More than one goal: the payload split the proof and needs bullets or braces.
   - Rewrite mismatch: the current goal shape does not match the intended lemma.

   <span style="color:red"><strong>为什么要改：</strong>view pattern 指 SSReflect 的反射/引入机制，不是 Lean 可直接沿用的诊断类别。<br><strong>怎么改：</strong>分别检查 Lean 的参数类型、intro/rcases 模式和实际 Bool 转换。</span>

   - Apply or intro mismatch: the theorem head, premises, or <span style="color:gray">view pattern</span> is wrong.
5. Only then choose the next repair.

   - If branches appeared, fix proof structure first.
   - If a rewrite mismatch appeared, debug the exact goal syntax.
   - If a premise mismatch appeared, inspect the theorem application.

<span style="color:red"><strong>为什么要改：</strong>Lean by 始终是证明入口，“加回 by”不能表达重新压缩已展开步骤。<br><strong>怎么改：</strong>验证后按需合并内部 tactic，不移除或补回入口。</span>

6. <span style="color:gray">Re-compress back to `by`</span> only after the expanded script actually closes all goals.



## Expansion Templates <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【展示几种紧凑证明写法应该怎样展开，才能看清中间步骤。】</span>

### Plain `by rewrite`
Original:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>连续使用三个等式改写，并尝试完成目标。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 的 by 开启证明块，改写列表用 rw：<code style="white-space:pre-wrap">by&#10;  rw [L1, L2, L3]</code>。L1/L2/L3 须是适用的已有等式。通用片段按项目 Lean 4.33.1/Mathlib 核对；示例变量和前提仍需由上下文提供。</span>

```coq
by rewrite L1 L2 L3.
```

Expand to:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>按顺序查看三次改写，找出失败点。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 不能通过删 by 暴露状态，应在块内拆开：<code style="white-space:pre-wrap">by&#10;  rw [L1]&#10;  trace_state&#10;  rw [L2]&#10;  trace_state&#10;  rw [L3]</code>。某步已关闭目标时，去掉多余的后续 tactic。</span>

```coq
rewrite L1 L2 L3.
```

Do not change the rewrite list until you see which exact rewrite fails or what goal remains.

### Plain `by apply:`
Original:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>应用一个定理，尝试完成目标。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 不使用 apply: 的冒号语法，改为 <code style="white-space:pre-wrap">by&#10;  apply some_lemma</code>；some_lemma 代表已核实的定理，剩余前提仍须证明。</span>

```coq
by apply: some_lemma.
```

Expand to:

<a id="lean-review-code-4"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>查看应用定理后还缺哪些前提。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 保留 by，在其中执行 <code style="white-space:pre-wrap">apply some_lemma&#10;trace_state</code>，再分别证明留下的目标；不靠删除 by 展开。</span>

```coq
apply: some_lemma.
```


<span style="color:red"><strong>为什么要改：</strong>这里应读取目标 Lean 后端的状态；查看剩余前提和应用类型的方法本身不变。<br><strong>怎么改：</strong>从 Lean 当前目标和诊断读取实际剩余义务。</span>

Now inspect whether <span style="color:gray">Coq</span> exposed missing premises, extra subgoals, or an application mismatch.

### `have ... by ...`
Original:

<a id="lean-review-code-5"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>用一行证明一个局部结论 P。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 的局部声明需要用 := 接证明项，改成 <code style="white-space:pre-wrap">have h : P := by tac</code>；tac 代表实际 Lean 证明步骤。</span>

```coq
have H : P by tac.
```

Expand to:

<a id="lean-review-code-6"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把局部证明单独写完，再继续主证明。<br><strong>2）怎么换成 Lean 代码：</strong>原 have H : P. 的句点和声明连接要改；Lean 本身支持花括号。这里推荐用 := by 连接局部证明：<code style="white-space:pre-wrap">have h : P := by&#10;  tac</code>。展开的是 tac 内部步骤，完成后再回到外层缩进。</span>

```coq
have H : P.
{
  tac.
}
```

This isolates the local proof and prevents drift into the outer proof.

### `suff ... by ...`
Original:

<a id="lean-review-code-7"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>先说明 P 足以推出目标，再证明 P。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 使用 suffices，by 后仍要保留“由 P 推出目标”的证明：<code style="white-space:pre-wrap">suffices h : P by&#10;  exact hToGoal h</code>。hToGoal : P → 当前目标；随后另证 P。</span>

```coq
suff H : P by tac.
```

Expand to:

<a id="lean-review-code-8"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>分别完成充分条件的两个证明方向。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 展开后仍须保留 by，明确写出两部分。已有 hToGoal : P → Q、hP : P 时：<code style="white-space:pre-wrap">suffices h : P by&#10;  exact hToGoal h&#10;exact hP</code></span>

```coq
suff H : P.
- tac.
```

Then inspect the newly exposed sufficiency goal separately.

### `case ...; by ...`
Original:

<a id="lean-review-code-9"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>分类后，把同一命令用于每个分支。<br><strong>2）怎么换成 Lean 代码：</strong>① Lean 的 case 只选分支标签，分类要用 cases。② 原分号把后续步骤分发到各支；Lean 的分号只按顺序执行，这种分发用 &lt;;&gt;：<code style="white-space:pre-wrap">cases E : x &lt;;&gt; tac</code>。这里用于数据类型；命题真假分类用 by_cases h : P。</span>

```coq
case E: x; by tac.
```

Expand to:

<a id="lean-review-code-10"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>拆开各分支，分别检查证明。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 按真实构造子写分支。x : Nat 时为 <code style="white-space:pre-wrap">cases E : x with&#10;| zero =&gt; tac&#10;| succ k =&gt; tac</code>；Bool 则用 false/true。tac 是待接入的实际步骤。</span>

```coq
case E: x.
- tac.
- tac.
```

If the branches are not symmetric, the expansion will show which branch actually needs a different proof.

<a id="lean-review-5"></a>



## First Revealed Error -> Real Cause <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【把展开后出现的具体错误对应到需要修复的问题类别。｜基本重写】</span>

<span style="color:red"><strong>为什么要改：</strong>这条焦点报错来自 Coq，不能继续作为 Lean 诊断表的匹配项。<br><strong>怎么改：</strong>改用实际 Lean 诊断、对应的目标标签及未完成块，重新验证这一类错误的处理示例。</span>

- <span style="color:gray">`Expected a single focused goal but 2 goals are focused.`</span>
  The payload opened branches. This is a structure problem, not a math problem.

<span style="color:red"><strong>为什么要改：</strong>这里匹配的是旧 Coq 改写报错字符串，Lean 后端的输出及报错位置不同。<br><strong>怎么改：</strong>用实际 Lean 改写失败案例替换诊断表的这一项，并记录当时的目标和等式类型。</span>

- <span style="color:gray">`The LHS of ... does not match any subterm of the goal.`</span>
  The chosen rewrite does not literally fit the current goal shape.

<span style="color:red"><strong>为什么要改：</strong>这是旧 Coq 应用错误字符串；仅凭它不能预设 Lean 缺的是哪一项前提。<br><strong>怎么改：</strong>读取 Lean 的实际应用错误及引理完整类型，再定位不匹配的参数或前提。</span>

- <span style="color:gray">`Cannot apply lemma ...`</span>
  The theorem head or expected premise shape is wrong.

<span style="color:red"><strong>为什么要改：</strong>旧 No assumption 对应 Coq 的 intro/view/move 操作，Lean 没有同一套反射引入流程可机械套用。<br><strong>怎么改：</strong>检查当前上下文、intro/rcases 模式与需要显式转换的 Bool 事实。</span>

- <span style="color:gray">`No assumption in ...`</span>
  An <span style="color:gray">intro pattern, view pattern, or moved hypothesis</span> does not exist in the current context.
- A concrete goal remains with no special error.

  <span style="color:red"><strong>为什么要改：</strong>在 Lean 中，留下目标说明块内证明尚未完成，不能解释成删去一个 SSReflect 收尾压缩器后暴露了目标。<br><strong>怎么改：</strong>直接定位留下目标的内部步骤，再完成该目标。</span>

  <span style="color:gray">The original `by` was simply too optimistic.</span> Read and solve that goal directly.



## Examples <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【通过四类常见失败说明，展开证明后应该观察什么并采取什么行动。】</span>

### Example 1: `by` Hides a Rewrite Mismatch
Compressed script:

<a id="lean-review-code-11"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>连续改写常数求和，尝试把它化成乘法。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 不一定经过 MathComp 的 iter 中间态，旧失败链不能直接复现。导入 Mathlib、启用 BigOperators 后，同一等式可写为 <code style="white-space:pre-wrap">example (n x : Nat) : (∑ _i : Fin n, x) = x * n := by&#10;  simp [Nat.mul_comm]</code>。失败教学案例须另取真实 Lean 错误。</span>

```coq
by rewrite big_const_ord iter_addn mul1n.
```

Expand to:

<a id="lean-review-code-12"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>查看常数求和每一步产生的实际目标。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 常数和会涉及基数倍数，不能预设旧 iter 状态。保留 by，内部改为 <code style="white-space:pre-wrap">rw [Finset.sum_const]&#10;trace_state&#10;simp [Nat.mul_comm]</code>，观察实际 card • x 再化简。</span>

```coq
rewrite big_const_ord iter_addn mul1n.
```

What this often reveals:

<span style="color:red"><strong>为什么要改：</strong>这条判断依赖 MathComp 的 mul1n 及 iter 中间态；Lean 的同一数学等式未必经过该轨迹。<br><strong>怎么改：</strong>观察所选 List/Finset 求和 API 的实际结果，再决定化简路径；不要人为制造旧错误。</span>

- <span style="color:gray">`mul1n` does not match because the goal is still in `iter` form</span>.
- Or the multiplication appears as `n * x`, not `1 * x`.

Correct reaction:
- Stop guessing.

<span style="color:red"><strong>为什么要改：</strong>这两个名字指向 MathComp 的特定正规化步骤，不能假定 Lean 有同名同形结果。<br><strong>怎么改：</strong>使用已核实的 Lean 求和步骤，并查看每一步生成的真实目标。</span>

- Read the exact intermediate goal after <span style="color:gray">`big_const_ord`</span> and <span style="color:gray">`iter_addn`</span>.
- Decide whether you need a bridge lemma or a different arithmetic normal form.

### Example 2: `by apply:` Hides Missing Premises
Compressed script:

<a id="lean-review-code-13"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>尝试用不等式传递性完成目标。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 普通 Nat 比较是 Prop，改用 Nat.le_trans。中间界为 b 时写 <code style="white-space:pre-wrap">refine Nat.le_trans (m := b) ?_ ?_</code>，留下两条待证不等式。</span>

```coq
by apply: leq_trans.
```

Expand to:

<a id="lean-review-code-14"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>明确中间界，分别证明两边的不等式。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 用两个显式目标替代原 apply: 写法。已有 hAB : a ≤ b、hBC : b ≤ c 时：<code style="white-space:pre-wrap">refine Nat.le_trans (m := b) ?_ ?_&#10;· exact hAB&#10;· exact hBC</code>，外层 by 保留。</span>

```coq
apply: leq_trans.
```

What this often reveals:
- two ordinary comparison goals,
- or a missing middle bound that was never named.

Correct reaction:
- Prove or name the intermediate inequality.
- Do not swap in a different lemma until you read the actual subgoals.

### Example 3: `have ... by ...` Hides an Incomplete Local Proof
Compressed script:

<a id="lean-review-code-15"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>尝试证明区间内作业已到达且尚未完成。<br><strong>2）怎么换成 Lean 代码：</strong>已核实的 Classic pending 仍是 Bool，但 Lean 的普通区间条件是 Prop，不能两处都照搬 /andP。声明改为 have PENDING0 : ∀ t, ... → pending ... = true := by；区间条件用 intro 后 rcases 拆开。接口取自 <code style="white-space:pre-wrap">Prosa.Classic.Model.Schedule.Global.Basic.Schedule</code> 及其 Schedule 命名空间，不混用 Prosa.Behavior 的实例参数版。</span>

```coq
have PENDING0 : forall t, a0 <= t < a0 + R -> pending job_arrival job_cost sched j0 t by
  move=> t /andP [GE LT]; apply/andP; split.
```

Expand to:

<a id="lean-review-code-16"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展开局部证明，找出尚未完成的那一项。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 要把 pending 的 Bool 合取为真拆成两个命题，在上一段局部块中用 <code style="white-space:pre-wrap">simp only [pending, Bool.and_eq_true]&#10;constructor</code>。两支分别证明已到达和未完成；!completed ... = true 可用 simp 化为 completed ... = false。两支未补齐前，这仍是不完整示例。</span>

```coq
have PENDING0 : forall t, a0 <= t < a0 + R -> pending job_arrival job_cost sched j0 t.
{
  move=> t /andP [GE LT].
  apply/andP; split.
}
```

What this reveals:
- the first conjunct may be solved,
- the second conjunct still needs a backlog or completion argument.

Correct reaction:
- Finish the exposed second conjunct.
- Do not invent a new helper lemma before reading that exact missing goal.

### Example 4: `case ...; by ...` Hides Branch Asymmetry
Compressed script:

<a id="lean-review-code-17"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>将服务量分为零和后继两种情况。<br><strong>2）怎么换成 Lean 代码：</strong>service_at 是 Nat，Lean 分类写为 cases E : service_at sched j0 t with，分别处理 zero / succ k；add0n 换成 Nat.zero_add，/= 的简化用适用的 simp。两支是否完成仍须各自检查。</span>

```coq
case E: (service_at sched j0 t) => [|k] /=; by rewrite add0n.
```

Expand to:

<a id="lean-review-code-18"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>逐支检查，找出还需额外论证的一支。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 不使用旧 Coq focus 报错判断分支是否完成。在上一段 zero / succ k 两支分别用 simp only [Nat.zero_add]，读取余下目标再继续；允许两支采用不同证明。</span>

```coq
case E: (service_at sched j0 t) => [|k] /=.
- rewrite add0n.
- rewrite add0n.
```

What this reveals:
- the zero branch may close,
- the successor branch may need a different argument entirely,

<span style="color:red"><strong>为什么要改：</strong>这是原 Coq 对焦点/分支结构的可能诊断，不能作为 Lean 缺少 bullet 的证据。<br><strong>怎么改：</strong>分别检查 zero/succ 分支及当前位置的 Lean 诊断。</span>

- or <span style="color:gray">Coq may complain about multiple focused goals if bullets were missing</span>.

Correct reaction:
- manage the branches explicitly,
- then solve each branch from its own goal shape.

<a id="lean-review-6"></a>



## What To Do After Expansion <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【根据展开后发现的是分支、改写还是参数问题，选择下一份专门 skill。】</span>

- If expansion reveals multiple goals, switch to the goal-count and bullet discipline in `skill_goal.md`.

- If expansion reveals a rewrite mismatch, debug the literal goal shape as in `.github/skills/coq-proof-state-discipline/skill_math.md`.
- If expansion reveals theorem-application ambiguity before ordinary goals appear, switch to early-bound argument diagnosis instead of adding random premises.

<a id="lean-review-7"></a>



## Anti-Patterns <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出展开诊断时应避免的做法，例如同时改动太多步骤或未验证就重新压缩。｜重改】</span>
- Do not respond to a failing `by` by trying three other rewrite lists first.

<span style="color:red"><strong>为什么要改：</strong>保留原 payload 的原则是对的，但 Lean 不能用删除 by 来做这次展开。<br><strong>怎么改：</strong>保持 by，只拆内部动作；一次改变一件事。</span>

- Do not <span style="color:gray">remove `by`</span> and simultaneously change the tactic payload. Expand first, then inspect.
- Do not expand the whole proof at once. Expand one compression boundary at a time.

<span style="color:red"><strong>为什么要改：</strong>需替换的是 have H : P. 的句点和声明连接语法；Lean 支持花括号，Use braces 的隔离建议可保留。<br><strong>怎么改：</strong>可写 have h : P := by，并在其内部证明 P；使用缩进或合法的花括号块。</span>

- Do not leave <span style="color:gray">`have H : P.`</span> floating inline when its local proof can drift. Use braces.

<span style="color:red"><strong>为什么要改：</strong>Lean by 始终保留，不是等验证后才加回的压缩语法。<br><strong>怎么改：</strong>验证后仅酌情合并块内步骤。</span>

- Do not <span style="color:gray">compress back to `by`</span> until the expanded form is known to close every resulting goal.

<a id="lean-review-8"></a>



## Minimal Debug Log <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【规定记录失败行、展开结果、第一条具体错误和接下来的修复动作。｜中改】</span>

<span style="color:red"><strong>为什么要改：</strong>Expanded form 原指删去 SSReflect by 后的脚本；Lean by 是证明块入口，不能这样删掉。<br><strong>怎么改：</strong>将此字段改为保留 by、拆开内部步骤后的脚本，并记录相应的 Lean 诊断位置。</span>

```text
Failing compact line:
Expanded form:
First revealed message:
Focused goal count after expansion:
Did the payload split goals: yes/no
Real problem class: rewrite mismatch / missing premise / extra branch / incomplete local proof
Next repair chosen from revealed signal:
```

<a id="lean-review-9"></a>



## Success Condition <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【说明什么时候已经找到了具体失败原因，并验证对应的修复确实完成目标。｜基本重写】</span>

<span style="color:red"><strong>为什么要改：</strong>旧 Coq 错误消失不能证明 Lean 修复成功，因为诊断来源已经改变。<br><strong>怎么改：</strong>确认具体失败位置已修复、相关目标完成且声明通过检查。</span>

This skill has worked when the flat <span style="color:gray">`No applicable tactic`</span> has been replaced by a specific, local proof-state diagnosis, and the next tactic is chosen from that diagnosis instead of from blind trial and error.


<span style="color:red"><strong>为什么要改：</strong>Lean 证明不能通过“压回 by”恢复结构，by 原本就应一直存在。<br><strong>怎么改：</strong>仅简化或合并已验证的内部步骤。</span>

If the expanded form closes the proof cleanly, then and only then is it reasonable to <span style="color:gray">compress it back into `by`</span>.