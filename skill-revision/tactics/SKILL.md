<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>一行很短的证明代码实际做了好几件事，系统只说这一行失败，你却看不出是哪一步出了问题。这份 skill 用来把这类紧凑写法展开，让隐藏的中间目标和未完成部分显露出来。<br><strong>具体例子：</strong>一行代码连续使用三个等式改写。失败可能发生在第二个等式，也可能三个等式都改写成功了，但最后还剩一个没有证明的目标。另一种情况是同一条命令同时处理两个分支，其中一个完成了，另一个仍需要额外论证。只看那一行短代码，很难区分这些情况。<br><strong>它会怎么处理：</strong>先保留原来要做的步骤，把这一处紧凑写法展开，重新运行并查看具体失败位置或剩余目标，再决定是换改写、补前提，还是分别处理分支。原 Coq/SSReflect 版本常通过去掉 by 来展开；Lean 中 by 的含义不同，不能照搬这个动作，但逐步检查内部证明步骤的目的仍然适用。</span>

<span style="color:red">【Lean迁移总评】单步诊断、根据首个可靠错误行动的方法可保留；原 by 展开机制及其错误模型在 Lean 不成立，需要重新设计技能主体。整体重写力度：重。</span>

<span style="color:red">【Core Rule｜首要结构性问题 1】<a href="#lean-review-2">点击跳转</a>：<br><strong>原来在做什么：</strong>一小段 SSReflect 证明只报 No applicable tactic、看不出具体哪里失败时，先去掉 by，运行里面的步骤，查看还剩什么目标。<br><strong>改哪里：</strong>本 skill 的核心调试动作“先移除 by，再运行其内部步骤”，以及围绕这一动作建立的触发条件和成功标准。<br><strong>为什么：</strong>SSReflect 的 by tac. 带有立即收尾的要求；Lean 的 by 却是进入 tactic 证明块的入口。删掉它通常使证明语法失效，因此只改示例里的 tactic 名不能修复这份 skill。<br><strong>替换（Rocq → Lean）：</strong>调试动作改为保留 by：将 rw [L1,L2] 拆成 rw [L1]、trace_state、rw [L2]；将分支分发拆成各自的 ·/case 块；局部事实写为 have h : P := by。成功标准是定位并关闭具体剩余目标，且声明通过 Lean 检查。<br><strong>删除（仅未来 Lean 版）：</strong>从迁移版规则中移除“删 by 暴露目标、验证后加回 by”这组操作及其错误模型。<br><strong>保留：</strong>一次展开一处、先读首个可靠错误、根据真实目标决定修复动作。<br><a href="https://lean-lang.org/doc/reference/latest/Tactic-Proofs/">Lean 官方说明</a>。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-1">When to Use</a>；<a href="#lean-review-2">Core Rule</a>；<a href="#lean-review-3">Why `by` Hides the Useful Error</a>；<a href="#lean-review-4">Required Procedure</a>；<a href="#lean-review-5">First Revealed Error -&gt; Real Cause</a>；<a href="#lean-review-7">Anti-Patterns</a>；<a href="#lean-review-9">Success Condition</a>。</span>

<span style="color:red">【Rocq 示例需转为 Lean 代码｜点击跳转】<a href="#lean-review-code-1">示例 1</a>；<a href="#lean-review-code-2">示例 2</a>；<a href="#lean-review-code-3">示例 3</a>；<a href="#lean-review-code-4">示例 4</a>；<a href="#lean-review-code-5">示例 5</a>；<a href="#lean-review-code-6">示例 6</a>；<a href="#lean-review-code-7">示例 7</a>；<a href="#lean-review-code-8">示例 8</a>；<a href="#lean-review-code-9">示例 9</a>；<a href="#lean-review-code-10">示例 10</a>；<a href="#lean-review-code-11">示例 11</a>；<a href="#lean-review-code-12">示例 12</a>；<a href="#lean-review-code-13">示例 13</a>；<a href="#lean-review-code-14">示例 14</a>；<a href="#lean-review-code-15">示例 15</a>；<a href="#lean-review-code-16">示例 16</a>；<a href="#lean-review-code-17">示例 17</a>；<a href="#lean-review-code-18">示例 18</a>。共 18 个原代码块，全部保留。</span>

---
name: by-expansion-diagnostics
description: 'Debug Coq and ssreflect `No applicable tactic` failures that arise on `by ...` lines by removing `by`, exposing the remaining goals, and treating the first revealed proof state as the real error signal. Use when a compact `by rewrite`, `by apply:`, `have ... by ...`, or `case ...; by ...` script hides whether the failure is a rewrite mismatch, a missing assumption, or an unexpected branch split.'
argument-hint: 'Describe the failing `by ...` line, the current goal, and the first message after expanding it.'
user-invocable: true
---

<span style="color:red">【Frontmatter｜中改】<br><strong>改哪里：</strong>frontmatter 的 name、description 和 argument-hint，尤其是其中“删除 by”的触发与操作描述。<br><strong>为什么：</strong>Lean 的 by 用来进入 tactic 证明块；用它是否出现来识别 SSReflect 压缩故障，会选错诊断动作。<br><strong>替换（Rocq → Lean）：</strong>建议 name 改为 lean-tactic-step-diagnostics；description/argument-hint 改为“定位组合 tactic 或多步改写中的首个失败点，保留 by 并展开内部步骤”。<br><strong>删除（仅未来 Lean 版）：</strong>移除以“删掉 by”作为诊断动作的说明。<br><strong>保留：</strong>这里只调整迁移注释，原元数据不动。下面的通用片段已按本地 Lean 4.33.1 / 项目锁定的 Mathlib 核对；h、xs、P 等是局部变量，完整业务证明仍需相应上下文。</span>

<span style="color:red">【By Expansion Diagnostics】<br><strong>本节在做什么：</strong>帮助展开紧凑的证明代码，找出究竟是哪一步或哪个分支失败。</span>

# By Expansion Diagnostics

<a id="lean-review-1"></a>

<span style="color:red">【When to Use｜重改】<br><strong>本节在做什么：</strong>列出一行代码包含多个动作、却只给出笼统错误时适合使用本 skill 的情况。<br><strong>改哪里：</strong>触发列表第 1、4 项：旧错误字符串，以及 by rewrite、by apply: 等 SSReflect 写法。<br><strong>为什么：</strong>Lean 的普通 by 不代表步骤被压缩，也不会必然产生 Coq 的 No applicable tactic。<br><strong>替换（Rocq → Lean）：</strong>改为“多步 rw、复杂 simp、cases 的分支分发、all_goals 或局部 have 的内部步骤失败，需查明具体失败点”。可识别的 Lean 形状包括 <code style="white-space:pre-wrap">rw [h1,h2,h3]</code>、<code style="white-space:pre-wrap">cases ... &lt;;&gt; tac</code>、<code style="white-space:pre-wrap">have h : P := by ...</code>；记录实际 diagnostic 及源位置。迁移后的入口仍须有具体失败或未完成目标；by exact h、by rfl 不因含有 by 就单独触发。<br><strong>保留：</strong>不盲猜改写、先区分匹配失败与前提缺失的原则。</span>

## When to Use
- Coq reports `No applicable tactic` on a line that starts with `by` or ends in a compressed `...; by ...` tail.
- A large model reacts to the flat error by trying random rewrites or lemma applications.
- You do not know whether the real failure is a rewrite mismatch, a missing assumption, or an extra branch.
- The failing line is a short script such as `by rewrite ...`, `by apply: ...`, `have H : P by ...`, or `case E: x; by ...`.

<a id="lean-review-2"></a>

<span style="color:red">【Core Rule｜基本重写｜核心操作在 Lean 失效】<br><strong>本节在做什么：</strong>要求先展开当前失败片段并查看剩余目标，再尝试更换证明步骤。<br><strong>改哪里：</strong>“Treat by as a proof-state compressor”以及后面的“Remove by, rerun the exact payload”。<br><strong>为什么：</strong>Lean by 是证明项进入 tactic 模式的入口，删去它通常使原步骤不再构成合法证明。<br><strong>替换（Rocq → Lean）：</strong>旧 Remove by → 保留外层 by，展开其内部动作：rw [L1,L2,L3] 拆成三行 rw；cases ... &lt;;&gt; tac 拆成独立的 ·/case 分支。需要查看状态时在步骤之间用 trace_state。<br><strong>删除（仅未来 Lean 版）：</strong>取消“先删 by，验证后再加回 by”的往返；最终只酌情合并已验证的内部步骤。<br><strong>保留：</strong>一次只展开一处，并根据实际状态决定下一步。</span>

## Core Rule
Treat `by` as a proof-state compressor, not as a diagnostic tactic.

When `by ...` fails, do not immediately try other tactics. Remove `by`, rerun the exact payload, and inspect the first revealed proof state. That first revealed state is the real debugging signal.

<a id="lean-review-3"></a>

<span style="color:red">【Why `by` Hides the Useful Error｜基本重写】<br><strong>本节在做什么：</strong>解释原 SSReflect 的紧凑写法为什么可能只报告整行失败而没有直接显示未完成部分。<br><strong>改哪里：</strong>整节对 by 失败的解释及其五种报错例子。<br><strong>为什么：</strong>旧解释建立在 SSReflect 的 by tac. 行为上；Lean 的 by 不会统一把内部错误变成 No applicable tactic。<br><strong>替换（Rocq → Lean）：</strong>未来标题改为“Locate the Failing Step Inside a Tactic Block”；正文分别说明 rw 列表哪一项失败、&lt;;&gt; 哪个分支失败、局部块还剩什么目标。诊断例用 <code style="white-space:pre-wrap">by&#10;  rw [h1]&#10;  trace_state&#10;  rw [h2]</code>，将当前 Lean 实际输出与相应源位置放在该步骤旁。<br><strong>删除（仅未来 Lean 版）：</strong>删去“by 会统一隐藏底层错误”的解释，以及直接把旧 Coq 字符串当作 Lean 报错的列表。<br><strong>保留：</strong>展开后记录具体目标和错误的用途；采集实际报错是通用方法，不是 Lean 新增的证明原理。</span>

## Why `by` Hides the Useful Error
`by tac.` means: run `tac` and close every resulting goal immediately.

If `tac` does any of the following,
- leaves one goal unsolved,
- opens two or more goals,
- rewrites the wrong normal form,
- applies a lemma with mismatched premises,

then Coq often reports only `No applicable tactic` at the compressed line.

After expansion, the hidden signal usually becomes one of these:
- a concrete remaining goal,
- `Expected a single focused goal but 2 goals are focused.`,
- `The LHS of ... does not match any subterm of the goal.`,
- `Cannot apply lemma ...`,
- `No assumption in ...`.

That specific message is what you should debug, not the original flat `by` failure.

<a id="lean-review-4"></a>

<span style="color:red">【Required Procedure｜基本重写】<br><strong>本节在做什么：</strong>给出保留失败片段、逐步展开、读取具体错误并选择修复方式的顺序。<br><strong>改哪里：</strong>步骤 2 的 Remove by、步骤 3/4 的 focused-goal 判断，以及步骤 6 的 Re-compress back to by。<br><strong>为什么：</strong>Lean 要保留 by；正常的 apply/cases 可以生成多个合法子目标，数量不等于结构损坏。<br><strong>替换（Rocq → Lean）：</strong>步骤 1 保存完整 := by 块和错误位置；步骤 2 只拆块内 rw/组合器；步骤 3 用 trace_state 或 Lean LSP 查看每一步目标；步骤 4 按实际错误及分支归属分类；步骤 6 仅合并已验证的内部动作。<br><strong>删除（仅未来 Lean 版）：</strong>去掉“删除/恢复 by”步骤和“目标数不等于 1 就判故障”的标准。<br><strong>保留：</strong>冻结失败片段、只改一处、先读首个可靠诊断再选修复动作。</span>

## Required Procedure
1. Freeze the exact failing line.
   - Copy the `by ...` line exactly.
   - Do not rewrite its payload yet.
2. Expand only that one compression boundary.
   - Remove `by`.
   - Keep the original tactic payload unchanged.
3. Re-run immediately.
   - Record the first new message.
   - Record the number of focused goals.
4. Classify the revealed signal.
   - One remaining goal: the compressed script was incomplete.
   - More than one goal: the payload split the proof and needs bullets or braces.
   - Rewrite mismatch: the current goal shape does not match the intended lemma.
   - Apply or intro mismatch: the theorem head, premises, or view pattern is wrong.
5. Only then choose the next repair.
   - If branches appeared, fix proof structure first.
   - If a rewrite mismatch appeared, debug the exact goal syntax.
   - If a premise mismatch appeared, inspect the theorem application.
6. Re-compress back to `by` only after the expanded script actually closes all goals.

<span style="color:red">【Expansion Templates】<br><strong>本节在做什么：</strong>展示几种紧凑证明写法应该怎样展开，才能看清中间步骤。</span>

## Expansion Templates

### Plain `by rewrite`
Original:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把三次等式改写压在一条命令里，并要求这条命令直接完成当前目标。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>这一行的 by rewrite 语法和三个引理的排列方式。<br><strong>为什么：</strong>Lean 的 by 开启证明块，等式改写由 rw 的列表完成。<br><strong>替换（Rocq → Lean）：</strong>把原行换为 <code style="white-space:pre-wrap">by&#10;  rw [L1, L2, L3]</code>；L1/L2/L3 必须是已有且类型合适的等式。</span>

```coq
by rewrite L1 L2 L3.
```

Expand to:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展开上一段改写，按原顺序检查每一步，找出哪条等式不匹配，或者全部改写后还剩什么目标。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>展开后的 rewrite L1 L2 L3.，以及“展开就是删 by”的做法。<br><strong>为什么：</strong>Lean 需要保留 by；要观察中间结果，应把改写逐条拆开。<br><strong>替换（Rocq → Lean）：</strong>换为 <code style="white-space:pre-wrap">by&#10;  rw [L1]&#10;  trace_state&#10;  rw [L2]&#10;  trace_state&#10;  rw [L3]</code>。trace_state 用于读取当前 Lean 目标。<br><strong>删除（仅未来 Lean 版）：</strong>删去诊断步骤中“移除外层 by”的操作；某一步已关闭目标时，移除无目标可处理的后续 tactic。</span>

```coq
rewrite L1 L2 L3.
```

Do not change the rewrite list until you see which exact rewrite fails or what goal remains.

### Plain `by apply:`
Original:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>应用一个定理，并尝试在这一步直接完成目标。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>by apply: some_lemma. 的定理应用语法。<br><strong>为什么：</strong>Lean 的 apply 在 by 块内执行，并把尚需证明的前提留下来。<br><strong>替换（Rocq → Lean）：</strong>换为 <code style="white-space:pre-wrap">by&#10;  apply some_lemma</code>，some_lemma 是已核实的实际定理。<br><strong>保留：</strong>未完成前提保持可见，不能用 sorry 代替证明。</span>

```coq
by apply: some_lemma.
```

Expand to:

<a id="lean-review-code-4"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展开上一段定理应用，查看定理还要求哪些前提，以及是否出现了参数或目标不匹配。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>单独一行 apply: some_lemma. 的展开形式。<br><strong>为什么：</strong>Lean 应在原 by 块内查看定理应用后的目标，不通过删 by 暴露状态。<br><strong>替换（Rocq → Lean）：</strong>在同一 by 下写 <code style="white-space:pre-wrap">apply some_lemma&#10;trace_state</code>，随后为剩余目标写 · 分支。需明确保留某项义务时，用 refine (some_lemma ... ?_)；省略部分按 #check 确认的真实参数填写。</span>

```coq
apply: some_lemma.
```

Now inspect whether Coq exposed missing premises, extra subgoals, or an application mismatch.

### `have ... by ...`
Original:

<a id="lean-review-code-5"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>声明一个局部结论 P，并把它的证明压在同一行里。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>have H : P by tac. 中局部声明与证明的连接语法。<br><strong>为什么：</strong>Lean 的 have 需要 := 指定证明项，by 再引入其 tactic 证明。<br><strong>替换（Rocq → Lean）：</strong>替换为 <code style="white-space:pre-wrap">have h : P := by tac</code>；tac 表示实际 Lean 证明步骤，并非新库接口。</span>

```coq
have H : P by tac.
```

Expand to:

<a id="lean-review-code-6"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把局部结论 P 的证明放进单独的块里，先完成这个小证明，再继续外层证明。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>have H : P. 后用花括号包住 tac 的局部证明范围。<br><strong>为什么：</strong>Lean 用 := by 和缩进表示局部证明；照搬 Coq 的句点与花括号会改变语法结构。<br><strong>替换（Rocq → Lean）：</strong>换为 <code style="white-space:pre-wrap">have h : P := by&#10;  第一步&#10;  trace_state&#10;  第二步</code>。中文行是待填入实际 tactic 的示意，不是 Lean 命令；证明 P 后以较少缩进返回外层。<br><strong>删除（仅未来 Lean 版）：</strong>删除迁移模板中的 Coq 花括号、Proof./Qed. 和声明后的句点。</span>

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

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把原目标转为一个足够的条件 P，并说明只要 P 成立，原目标就能成立。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>suff H : P by tac. 的充分条件声明。<br><strong>为什么：</strong>Lean 使用 suffices；by 后的块负责由 P 推出原目标，而 P 本身仍要另证。<br><strong>替换（Rocq → Lean）：</strong>换为 <code style="white-space:pre-wrap">suffices h : P by&#10;  exact hToGoal h</code>，其中 hToGoal : P → 当前目标；随后另外证明 P。<br><strong>删除（仅未来 Lean 版）：</strong>取消“展开时删 by”的规则；这里的 by 是所需证明结构。</span>

```coq
suff H : P by tac.
```

Expand to:

<a id="lean-review-code-8"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展开充分条件这一步，分别检查“P 能推出原目标”和“P 本身成立”这两项证明。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>suff 后只显示一个 - tac 的展开模板。<br><strong>为什么：</strong>Lean 的 suffices 要明确区分“从 P 推出 Q”和“证明 P”，不能把一个旧 bullet 当成全部证明。<br><strong>替换（Rocq → Lean）：</strong>已有 hToGoal : P → Q、hP : P，目标 Q 时写 <code style="white-space:pre-wrap">suffices h : P by&#10;  exact hToGoal h&#10;exact hP</code>，分别检查两个方向。</span>

```coq
suff H : P.
- tac.
```

Then inspect the newly exposed sufficiency goal separately.

### `case ...; by ...`
Original:

<a id="lean-review-code-9"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>对 x 分类，然后把同一条证明命令用于每个分支，尝试一次完成所有分支。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>case E: x; by tac 的分类命令及对所有分支执行 tactic 的写法。<br><strong>为什么：</strong>Lean 用 cases 拆归纳类型，用 by_cases 拆命题；case 本身只是选择已有目标的标签。<br><strong>替换（Rocq → Lean）：</strong>自然数版本换为 <code style="white-space:pre-wrap">cases E : x &lt;;&gt; tac</code>；命题 P 的真假分类用 by_cases h : P。&lt;;&gt; 将右侧 tactic 用到产生的各分支。</span>

```coq
case E: x; by tac.
```

Expand to:

<a id="lean-review-code-10"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把分类后的分支分别写出来，逐个执行证明命令，便于发现某一支需要不同的证明。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>case E: x. 后的两个 - tac 分支。<br><strong>为什么：</strong>Lean 的分支名称取决于分类对象的真实构造子，不能统一套两个 Coq bullet。<br><strong>替换（Rocq → Lean）：</strong>自然数版本写 <code style="white-space:pre-wrap">cases E : x with&#10;| zero =&gt;&#10;  tac&#10;| succ k =&gt;&#10;  tac</code>；Bool 用 false/true，其他类型按实际构造子展开。tac 仍代表待验证的证明步骤。</span>

```coq
case E: x.
- tac.
- tac.
```

If the branches are not symmetric, the expansion will show which branch actually needs a different proof.

<a id="lean-review-5"></a>

<span style="color:red">【First Revealed Error -&gt; Real Cause｜基本重写】<br><strong>本节在做什么：</strong>把展开后出现的具体错误对应到需要修复的问题类别。<br><strong>改哪里：</strong>整张“旧 Coq 错误字符串 → 原因”列表。<br><strong>为什么：</strong>Lean 的报错分类和目标分支管理不同，旧 focus 文本不能直接充当 Lean 故障证据。<br><strong>替换（Rocq → Lean）：</strong>按观察到的 Lean 错误重建映射：改写不匹配 → trace_state 后查等式、方向和作用位置；类型不匹配 → 对照 expected/actual type；未知名称 → <code style="white-space:pre-wrap">#check 全限定名</code> 并查 import；实例合成失败 → <code style="white-space:pre-wrap">#synth 实例类型</code>；未解决目标 → 查看对应分支。错误原文从目标版本实际输出采集。<br><strong>删除（仅未来 Lean 版）：</strong>删去“多目标自动等于结构问题”和按旧错误文本推断 Lean 原因的规则。<br><strong>新增（Lean 适配）：</strong>补 Lean 的 No goals to be solved 处理：检查前一步是否已关闭目标，移除该处多余的后续 tactic，而不是新增数学引理。</span>

## First Revealed Error -> Real Cause
- `Expected a single focused goal but 2 goals are focused.`
  The payload opened branches. This is a structure problem, not a math problem.
- `The LHS of ... does not match any subterm of the goal.`
  The chosen rewrite does not literally fit the current goal shape.
- `Cannot apply lemma ...`
  The theorem head or expected premise shape is wrong.
- `No assumption in ...`
  An intro pattern, view pattern, or moved hypothesis does not exist in the current context.
- A concrete goal remains with no special error.
  The original `by` was simply too optimistic. Read and solve that goal directly.

<span style="color:red">【Examples】<br><strong>本节在做什么：</strong>通过四类常见失败说明，展开证明后应该观察什么并采取什么行动。</span>

## Examples

### Example 1: `by` Hides a Rewrite Mismatch
Compressed script:

<a id="lean-review-code-11"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把常数求和连续改写成重复加法、乘法等形式，并尝试一次完成证明；其中某条改写可能与当时的表达式不匹配。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>big_const_ord、iter_addn、mul1n 组成的常数求和链。<br><strong>为什么：</strong>Mathlib 的常数求和路径不要求经过 MathComp iter；原失败链不能直接当作 Lean 故障复现。<br><strong>替换（Rocq → Lean）：</strong>以同一自然数等式为目标，换为 <code style="white-space:pre-wrap">example (n x : Nat) : (∑ _i : Fin n, x) = x * n := by&#10;  simp [Nat.mul_comm]</code>。若要保留失败教学案例，使用确实无法匹配的 Lean rw，并记录真实诊断。<br><strong>删除（仅未来 Lean 版）：</strong>删去“Lean 必先出现 iter，随后用 iter_addn”的执行要求。<br><strong>新增（Lean 适配）：</strong>为上面的求和记号补 import Mathlib 和 open scoped BigOperators。</span>

```coq
by rewrite big_const_ord iter_addn mul1n.
```

Expand to:

<a id="lean-review-code-12"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展开上一段求和改写，查看每步产生的真实目标，确定问题出在哪次表示转换。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>展开版 rewrite big_const_ord iter_addn mul1n. 的各步。<br><strong>为什么：</strong>Lean 的实际常数和改写会涉及基数倍数，不能预设旧 iter 中间态。<br><strong>替换（Rocq → Lean）：</strong>在保留的 by 块内换为 <code style="white-space:pre-wrap">rw [Finset.sum_const]&#10;trace_state&#10;simp [Nat.mul_comm]</code>，检查 card • x 的真实中间目标，再化简。<br><strong>删除（仅未来 Lean 版）：</strong>删去要求 Lean 重现 iter_addn 中间式的诊断分支。</span>

```coq
rewrite big_const_ord iter_addn mul1n.
```

What this often reveals:
- `mul1n` does not match because the goal is still in `iter` form.
- Or the multiplication appears as `n * x`, not `1 * x`.

Correct reaction:
- Stop guessing.
- Read the exact intermediate goal after `big_const_ord` and `iter_addn`.
- Decide whether you need a bridge lemma or a different arithmetic normal form.

### Example 2: `by apply:` Hides Missing Premises
Compressed script:

<a id="lean-review-code-13"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>尝试直接用不等式的传递性完成目标，但中间的界以及连接它的两条不等式可能还没给出。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>by apply: leq_trans. 使用的布尔不等式传递性接口。<br><strong>为什么：</strong>Lean 的普通 Nat 不等式是 Prop，应使用相应的命题传递性定理。<br><strong>替换（Rocq → Lean）：</strong>leq_trans → Nat.le_trans；中间界为 b 时用 <code style="white-space:pre-wrap">refine Nat.le_trans (m := b) ?_ ?_</code>，留下左右两条不等式。</span>

```coq
by apply: leq_trans.
```

Expand to:

<a id="lean-review-code-14"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展开传递性这一步，明确中间的数 b，再分别证明左边不超过 b、b 不超过右边。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>展开后的 apply: leq_trans. 及它没有显式给出的中间界。<br><strong>为什么：</strong>Lean 需要对实际生成的两个不等式目标分别给证明；明确 b 可以消除中间量的不确定性。<br><strong>替换（Rocq → Lean）：</strong>已有 hAB : a ≤ b、hBC : b ≤ c 时换为 <code style="white-space:pre-wrap">refine Nat.le_trans (m := b) ?_ ?_&#10;· exact hAB&#10;· exact hBC</code>。缺少哪项就在对应分支继续证明，保留外层 by。</span>

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

<span style="color:red"><strong>1）这段代码在干嘛：</strong>尝试证明区间内的作业处于 pending 状态；代码把目标拆成两个条件，但尚未给出这两个条件的完整证明。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>PENDING0 的结论类型、区间条件、have 语法，以及 move=&gt; ... /andP 的输入拆分。<br><strong>为什么：</strong>当前已核实的 Classic pending 仍返回 Bool，Lean 的普通区间比较则为 Prop；不能把两者一概当作 MathComp 布尔命题。<br><strong>替换（Rocq → Lean）：</strong>结论换为 pending ... = true，局部声明写 have PENDING0 : ∀ t, ... → pending ... = true := by；Prop 区间条件用 intro t h; rcases h with ⟨hGE,hLT⟩。<br><strong>删除（仅未来 Lean 版）：</strong>对这个 Prop 区间条件删去 /andP reflection；不能因此删去 pending 本身真正需要的 Bool 处理。<br><strong>新增（Lean 适配）：</strong>导入 <code style="white-space:pre-wrap">Prosa.Classic.Model.Schedule.Global.Basic.Schedule</code> 并打开 <code style="white-space:pre-wrap">Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule</code>。这套接口的 completed/pending/backlogged 返回 Bool、service_at 返回 Nat；旧显式 job_arrival/job_cost 示例应接这套参数，不能混用 Prosa.Behavior 实例参数版本。</span>

```coq
have PENDING0 : forall t, a0 <= t < a0 + R -> pending job_arrival job_cost sched j0 t by
  move=> t /andP [GE LT]; apply/andP; split.
```

Expand to:

<a id="lean-review-code-16"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展开上一段局部证明，让“已经到达”和“尚未完成”这两个条件分别显露出来，查清哪一项还没证明。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>局部证明内的 apply/andP; split，以及尚未完成的两个条件。<br><strong>为什么：</strong>Lean 中 pending ... = true 要先按真实 Bool 定义展开，再把 Bool 合取为真拆成两个命题。<br><strong>替换（Rocq → Lean）：</strong>在上一段的 have ... := by 块内换为 <code style="white-space:pre-wrap">simp only [pending, Bool.and_eq_true]&#10;constructor</code>，分别证明 has_arrived ... = true 和 !completed ... = true。Bool 否定用 simp 化为 completed ... = false，再处理服务界。<br><strong>保留：</strong>这是未完成局部证明的教学示例；补齐两支前不能称为可编译的完整证明。</span>

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

<span style="color:red"><strong>1）这段代码在干嘛：</strong>按服务量是 0 还是 k + 1 分类，并尝试用同一条加法化简完成两个分支。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>service_at 的 case 分类、/= 简化和 add0n 改写。<br><strong>为什么：</strong>service_at 是 Nat，Lean 要使用 zero/succ 分支以及实际自然数加法定理。<br><strong>替换（Rocq → Lean）：</strong>分类换成 <code style="white-space:pre-wrap">cases E : service_at sched j0 t with&#10;| zero =&gt; ...&#10;| succ k =&gt; ...</code>；add0n → Nat.zero_add，/= → 适用的 simp。省略号是待完成分支，不是完整证明。<br><strong>保留：</strong>分别检查两支，不假定同一条简化能关闭两支；这本来就是原例要教的方法。</span>

```coq
case E: (service_at sched j0 t) => [|k] /=; by rewrite add0n.
```

Expand to:

<a id="lean-review-code-18"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把服务量的两个分支拆开检查：一个分支可能已经完成，另一个仍需要额外的数值界或业务条件。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>两个分支里的 rewrite add0n. 与后面的多目标报错解释。<br><strong>为什么：</strong>Lean 正常保留多个分支；是否完成取决于各分支目标，不能套 Coq focus 故障判断。<br><strong>替换（Rocq → Lean）：</strong>沿用上一段 zero/succ 分类，在两支分别执行 simp only [Nat.zero_add] 并查看余下目标。已关闭的一支结束，另一支继续用业务界证明。<br><strong>删除（仅未来 Lean 版）：</strong>旧 Coq focused-goal 报错不再作为 Lean 的诊断依据；迁移后按具体分支和实际错误判断。<br><strong>保留：</strong>逐支检查是否完成、允许两支使用不同证明的原则。</span>

```coq
case E: (service_at sched j0 t) => [|k] /=.
- rewrite add0n.
- rewrite add0n.
```

What this reveals:
- the zero branch may close,
- the successor branch may need a different argument entirely,
- or Coq may complain about multiple focused goals if bullets were missing.

Correct reaction:
- manage the branches explicitly,
- then solve each branch from its own goal shape.

<a id="lean-review-6"></a>

<span style="color:red">【What To Do After Expansion｜中改】<br><strong>本节在做什么：</strong>根据展开后发现的是分支、改写还是参数问题，选择下一份专门 skill。<br><strong>改哪里：</strong>路由列表第 1 项的“多个目标就切换到 bullet discipline”，以及三项旧路径/接口说明。<br><strong>为什么：</strong>Lean 的多个子目标可能完全正常；旧接收 skill 的 Coq focus 规则不能继续用于判断故障。文件路径本身与语言无关。<br><strong>替换（Rocq → Lean）：</strong>误入分支或局部块未完成 → ../goal/SKILL.md；rw 形状不匹配 → ../math/SKILL.md；实例/参数推断失败 → ../parameter/SKILL.md；计数表示转换 → ../count-bridging/SKILL.md。按实际安装目录核实路径，并确认接收 skill 使用的是 Lean 规则。<br><strong>删除（仅未来 Lean 版）：</strong>取消“仅因多个目标就恢复 Coq 单一 focus”的路由条件。<br><strong>保留：</strong>按具体问题交给对应 skill 的分工。</span>

## What To Do After Expansion
- If expansion reveals multiple goals, switch to the goal-count and bullet discipline in `skill_goal.md`.
- If expansion reveals a rewrite mismatch, debug the literal goal shape as in `.github/skills/coq-proof-state-discipline/skill_math.md`.
- If expansion reveals theorem-application ambiguity before ordinary goals appear, switch to early-bound argument diagnosis instead of adding random premises.

<a id="lean-review-7"></a>

<span style="color:red">【Anti-Patterns｜重改】<br><strong>本节在做什么：</strong>列出展开诊断时应避免的做法，例如同时改动太多步骤或未验证就重新压缩。<br><strong>改哪里：</strong>第 2、4、5 条中“删 by”“have 用 braces”“重新压回 by”的措辞。<br><strong>为什么：</strong>Lean 使用保留的 by 和局部缩进块；Coq 的句点与花括号模板不能直接控制 Lean 证明范围。<br><strong>替换（Rocq → Lean）：</strong>“have 用 braces” → “have h : P := by 的缩进范围明确”；“压回 by” → “验证后可合并内部 rw 或分支 tactic”。<br><strong>删除（仅未来 Lean 版）：</strong>去掉删除 by 的操作；展开时只拆一个内部 rw/组合器。<br><strong>保留：</strong>不盲试引理、不一次展开整篇证明、不同时更换引理和改动证明结构。</span>

## Anti-Patterns
- Do not respond to a failing `by` by trying three other rewrite lists first.
- Do not remove `by` and simultaneously change the tactic payload. Expand first, then inspect.
- Do not expand the whole proof at once. Expand one compression boundary at a time.
- Do not leave `have H : P.` floating inline when its local proof can drift. Use braces.
- Do not compress back to `by` until the expanded form is known to close every resulting goal.

<a id="lean-review-8"></a>

<span style="color:red">【Minimal Debug Log｜中改】<br><strong>本节在做什么：</strong>规定记录失败行、展开结果、第一条具体错误和接下来的修复动作。<br><strong>改哪里：</strong>日志的 Expanded form、Focused goal count、Real problem class 三项及其填写规则。<br><strong>为什么：</strong>Lean 的展开对象是 by 内部步骤；日志必须能把目标和错误对应到同一位置与版本，单独统计目标数不能说明分支归属。<br><strong>替换（Rocq → Lean）：</strong>Expanded form 填拆开的 rw 或分支块；Focused goal count 改为当前目标数的观察记录；Real problem class 根据实际错误填写，不以 != 1 自动归因。<br><strong>删除（仅未来 Lean 版）：</strong>删去“Expanded form 必须是删掉 by 的脚本”的隐含要求。<br><strong>新增（Lean 适配）：</strong>为 Lean LSP 状态与源码对齐补充 <code style="white-space:pre-wrap">Failure source position:&#10;Document version:&#10;Current goal tag:&#10;First failing inner tactic:</code>。这些是适配 Lean 状态的日志字段；记录位置和版本本身属于通用调试方法。</span>

## Minimal Debug Log

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

<span style="color:red">【Success Condition｜基本重写】<br><strong>本节在做什么：</strong>说明什么时候已经找到了具体失败原因，并验证对应的修复确实完成目标。<br><strong>改哪里：</strong>“替换掉 No applicable tactic”与末段“compress it back into by”这两项成功标准。<br><strong>为什么：</strong>Lean 中同一个字符串和压回 by 都不能证明修复有效；需要核实具体目标及声明检查结果。<br><strong>替换（Rocq → Lean）：</strong>改为：能够指出哪条内部 tactic 或哪个分支失败；修复后相应目标全部关闭，当前声明通过 Lean 检查。验证后可移除临时 trace_state，保留外层 := by。<br><strong>删除（仅未来 Lean 版）：</strong>删去用“旧错误消失”或“加回 by”单独判断成功的规则。<br><strong>保留：</strong>从具体诊断选择下一步，而不是盲试。</span>

## Success Condition
This skill has worked when the flat `No applicable tactic` has been replaced by a specific, local proof-state diagnosis, and the next tactic is chosen from that diagnosis instead of from blind trial and error.

If the expanded form closes the proof cleanly, then and only then is it reasonable to compress it back into `by`.