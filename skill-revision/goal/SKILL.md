<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>一个证明拆成几个分支，或者中途开始证明一个小结论后，你可能没有注意到当前目标已经变了，仍然按原来的大目标继续写。这个 skill 用来找出“现在到底在证明哪一件事”，并整理各部分的先后顺序。<br><strong>具体例子：</strong>你先按“任务已经完成”和“任务尚未完成”分成两个情况。在第二个情况里，又提出一个小结论：“这个任务已经到达。”如果这个小结论还没有证明完，你就开始使用针对主定理的步骤，系统看到的目标和你心里想的目标就会不一致，后面的步骤会接连失败。<br><strong>它会怎么处理：</strong>它要求先查看系统当前列出的目标和可用条件，确认自己位于哪个分支、是否还在某个小结论的证明里。然后把这个局部证明做完，确认返回了预期位置，再继续外层证明；各个分支也分别处理清楚。最终要做到：每一步都用在它实际面对的目标上，而不是靠代码排版猜测证明进行到了哪里。</span>

<span style="color:red">【Lean迁移总评】先读真实目标、隔离局部证明的核心方法可保留；主要改动集中在 Lean 的目标/分支模型、SSReflect reflection 和修复模板。整体重写力度：中重。</span>

<span style="color:red">【Hard Recovery Protocol｜首要结构性问题 1】<a href="#lean-review-6">点击跳转</a>：<br><strong>原来在做什么：</strong>这份 skill 用来处理“证明脚本以为还在原来的分支，实际却进入了别的目标”的情况。原规则把 Coq 的焦点报错和 focused goal 数量作为信号，再用 bullets 和花括号恢复分支。<br><strong>改哪里：</strong>修改 Hard Recovery Protocol 的触发条件和恢复完成条件。<br><strong>为什么：</strong>两种语言都允许合法多目标；迁移后失效的是用 Coq 特定 focused-goal 报错及计数直接判断 Lean 是否走错分支。Lean 的零目标也可能表示局部块已完成。<br><strong>替换（Rocq → Lean）：</strong>if focusedGoals != 1 then recover → 比较当前 goal tag、局部上下文与预期分支；恢复结束 → 归属正确且局部 diagnostics 消失。局部证明用 have h : P := by，数据分类用 cases，选择分支用 case，合取拆分用 constructor。<br><strong>删除（仅未来 Lean 版）：</strong>删去“目标数不等于 1 就恢复”及“必须恰好一个目标才能继续”的硬条件。<br><strong>保留：</strong>先确认正在证明哪个目标、再决定继续或恢复的目的不变；只翻译 bullets 示例无法修正触发规则。<br><a href="https://lean-lang.org/doc/reference/latest/Tactic-Proofs/">Lean 官方说明</a>。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-1">When to Use</a>；<a href="#lean-review-2">Core Rule</a>；<a href="#lean-review-4">Hidden Goal Head Before Case Split</a>；<a href="#lean-review-6">Hard Recovery Protocol</a>；<a href="#lean-review-9">Anti-Patterns</a>；<a href="#lean-review-10">Trace Example From This Workspace</a>；<a href="#lean-review-11">Bullet-Based Repair Pattern</a>；<a href="#lean-review-13">Success Condition</a>。</span>

<span style="color:red">【Rocq 示例需转为 Lean 代码｜点击跳转】<a href="#lean-review-code-1">示例 1</a>；<a href="#lean-review-code-2">示例 2</a>；<a href="#lean-review-code-3">示例 3</a>；<a href="#lean-review-code-4">示例 4</a>；<a href="#lean-review-code-5">示例 5</a>；<a href="#lean-review-code-6">示例 6</a>；<a href="#lean-review-code-7">示例 7</a>；<a href="#lean-review-code-8">示例 8</a>；<a href="#lean-review-code-9">示例 9</a>。共 9 个原代码块，全部保留。</span>

---
name: goal-focus-discipline
description: 'Handle Coq and ssreflect proof-state drift by checking the current number of goals after every tactic that can split or close goals, using bullets to manage branches, and proving any have-generated sublemma inside braces before returning to the main line.'
argument-hint: 'Describe the current goal count, the previous tactic, and the branch or sublemma that introduced the drift.'
user-invocable: true
---

<span style="color:red">【Frontmatter｜中改】<br><strong>改哪里：</strong>修改 frontmatter 的技能名、description 和 braces 触发描述。<br><strong>为什么：</strong>Coq/SSReflect 的焦点报错与花括号规则不适用于 Lean 的 goal tag 和局部 by 块。<br><strong>替换（Rocq → Lean）：</strong>name 建议改为 lean-goal-focus-discipline；description 改为“按当前目标标签、局部 by 块和 diagnostics 修复误入分支或未完成的局部证明”。<br><strong>删除（仅未来 Lean 版）：</strong>删除“have 必须用 braces”的触发描述。<br><strong>保留：</strong>先检查 proof state 的用途不变。以下通用片段已按本地 Lean 4.33.1 / 项目锁定 Mathlib 核对；业务证明仍需目标上下文。h、xs、P 等是局部变量，不是新库 API。</span>

<span style="color:red">【Goal Focus Discipline】<br><strong>本节在做什么：</strong>帮助确认当前正在证明哪个目标，避免在分支或局部证明尚未结束时误写外层步骤。</span>

# Goal Focus Discipline

<a id="lean-review-1"></a>

<span style="color:red">【When to Use｜重改】<br><strong>本节在做什么：</strong>列出哪些报错或证明行为可能说明当前分支已经与预期不一致。<br><strong>改哪里：</strong>修改 When to Use 的报错触发词、分类动作和否定证明入口。<br><strong>为什么：</strong>Lean case 选择已有分支，cases/by_cases 才做分类；Coq focused-goal 报错不能当作 Lean 证据。<br><strong>替换（Rocq → Lean）：</strong>触发词 → 当前 goal tag/上下文与预期不符、局部 have 的 by 块有 unsolved goals、case 标签选错；case/destruct 数据分类→cases；命题分类→by_cases；选择已有分支→case 标签。<br><strong>删除（仅未来 Lean 版）：</strong>删除以正常多目标触发恢复的规则；普通 Prop 否定省去 apply/negP reflection。</span>

## When to Use
- Coq reports `Expected a single focused goal but 2 goals are focused.`
- A proof used to have one main line, then `case`, `have`, `apply/negP`, `split`, or `destruct` was added and later tactics stopped fitting.
- The model starts adding extra lemmas instead of first checking whether the proof state already drifted.
- A local fact such as `PENDING0` or `SLOT_BOUND` is introduced, and later tactics behave as if the main goal were still the only goal.
- The focus error appears right after `case` or another boolean split, but the split target may still be hidden under a named definition or wrapper.
- A branch "looks done" because the last line rewrote a local hypothesis, but the enclosing goal was never explicitly discharged.

<a id="lean-review-2"></a>

<span style="color:red">【Core Rule｜重改｜需重设恢复条件】<br><strong>本节在做什么：</strong>要求先看系统当前的目标和分支位置，再决定下一步证明动作。<br><strong>改哪里：</strong>修改 Core Rule 的“数量不等于 1”判定及局部引理隔离写法。<br><strong>为什么：</strong>Lean 目标列表可有多个合法待证目标；零目标需结合所在块判断是否完成，不能机械套用 Coq 焦点栈。<br><strong>替换（Rocq → Lean）：</strong>恢复判据 → 当前标签不是预期分支或局部块 diagnostics 显示未完成；局部事实写为 <code style="white-space:pre-wrap">have h : P := by&#10;  ...</code>，其中 ... 须填真实业务证明，不可提交为占位。<br><strong>删除（仅未来 Lean 版）：</strong>删除“目标数不等于 1 → recovery”和要求 Coq braces 的判据。<br><strong>保留：</strong>先读真实目标；目标数为 0 时确认当前位置属于哪个块，再判定局部或整项完成。</span>

## Core Rule
Do not choose the next tactic from proof intent alone. First check how many goals exist now, and whether the previous tactic opened or closed any goal.

If there is more than one goal, switch to bullet management immediately. Do not continue with a single-goal script.

If `have` is used to introduce a lemma, prove it inside `{ ... }` and return only after that local proof is closed.

If a `case`, `destruct`, or reflected boolean split targets a term that is still hidden under a named definition, unfold first. Otherwise the split can create branches without actually changing the enclosing goal.

If the last useful line of a branch only rewrites inside a local hypothesis, do not assume the branch is closed. Explicitly consume that hypothesis with `exact`, `apply`, or `exfalso; exact:` if it is meant to close the enclosing goal.

When the visible script structure and the live proof state disagree, trust the live proof state. Do not keep editing as if braces, bullets, or a finished-looking `have` block had already restored focus.

If the current focused goal count is not exactly one, the next step is a recovery step, not a math step.

Recovery-step whitelist when the goal count is not exactly one:
- inspect the current goals
- introduce or finish bullets
- close the current `{ ... }` subproof
- return to the parent branch
- abort and restart a noisy exploratory branch

Until focus returns to exactly one intended goal, do not:
- add a new `have`, `suff`, or helper lemma
- attempt a new `rewrite`, `apply`, `exact`, or arithmetic step for the outer theorem
- treat downstream messages such as missing hypotheses, reused names, or failed lemma applications as the main problem

Errors such as `Cannot apply lemma ...`, `No such goal`, `... already used`, and `The variable ... was not found` are often secondary effects of proof-state drift once multiple goals are live. Do not repair them before restoring focus.

<a id="lean-review-3"></a>

<span style="color:red">【Required Procedure｜中改】<br><strong>本节在做什么：</strong>给出检查上一步、确认当前分支并继续证明的操作顺序。<br><strong>改哪里：</strong>修改 Required Procedure 的步骤 1、3、4、5 及每步记录内容。<br><strong>为什么：</strong>Lean 分支由标签和局部块组织；目标是否需要展开取决于实际 tactic，by_cases 不要求命题出现在目标头。<br><strong>替换（Rocq → Lean）：</strong>步骤 1→trace_state/当前位置 LSP goal；步骤 3→<code style="white-space:pre-wrap">unfold wrapper</code> 或 <code style="white-space:pre-wrap">change 等价目标</code>；步骤 4→·/case/嵌套 by 隔离；步骤 5→<code style="white-space:pre-wrap">exact h</code>、<code style="white-space:pre-wrap">simpa using h</code> 或 <code style="white-space:pre-wrap">exact False.elim hFalse</code> 收尾。记录前后 goal tag 与上下文。<br><strong>删除（仅未来 Lean 版）：</strong>删除把“拆分项必须字面出现在目标头”当作 Lean by_cases 前提的要求。<br><strong>保留：</strong>检查前后目标并明确关闭分支的顺序不变。</span>

## Required Procedure
1. Read the current proof state before the next step.
   - Record the exact number of focused goals.
   - Record the shape of the current goal.
2. Inspect the previous tactic.
   - Did it split the proof into branches?
   - Did it create a local subgoal?
   - Did it close a branch?
3. Inspect the literal goal head before any new split.
  - If the next `case`, `destruct`, or reflection step targets a term hidden under a definition, unfold first.
  - Do not split on mathematical intent alone. Check whether the split target literally occurs in the current goal or active hypothesis.
4. If the goal count changed, respond structurally, not mathematically.
   - New branch: introduce a bullet.
   - Local lemma from `have`: open `{ ... }`, finish it, then return.
   - Closed branch: verify that focus returned to the intended outer goal.
5. When a branch seems finished, verify that the last line actually discharged the enclosing goal.
  - Rewriting inside `Hlt_succ`, `Hdone`, or another local fact is not the same as closing the branch.
  - If the branch should end from that fact, finish with `exact`, `apply`, or `exfalso; exact:`.
6. Only after focus is stable should you pick the next rewriting or reasoning step.
7. Do not add bridge lemmas, arithmetic lemmas, or helper facts just to avoid a focus problem. Fix the branch structure first.

<a id="lean-review-4"></a>

<span style="color:red">【Hidden Goal Head Before Case Split｜重改｜需重设适用范围】<br><strong>本节在做什么：</strong>说明目标藏在一个定义后面时，为什么需要先看清定义再决定怎样分情况证明。<br><strong>改哪里：</strong>修改 Hidden Goal Head 的分类前提、完成条件定义及其 imports。<br><strong>为什么：</strong>Lean by_cases 可对任意命题分类；本地已核实 Classic completed/pending/backlogged 仍是 Bool，service_at 是 Nat，不能把这些业务定义误当成已全部迁移为 Prop。<br><strong>替换（Rocq → Lean）：</strong>查看封装定义→按需要 unfold/change/simp；Global deadline 目标→Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability.job_misses_no_deadline 的 Bool = true，先 unfold 该定义和 completed，再 apply decide_eq_true。<br><strong>删除（仅未来 Lean 版）：</strong>删除原“拆分项必须在目标头”的通用硬限制；Lean by_cases 不需要它。若换用另一套真实 Prop 接口，省去 negP/Bool 反射步骤。<br><strong>新增（Lean 适配）：</strong>导入 <code style="white-space:pre-wrap">Prosa.Classic.Model.Schedule.Global.Basic.Schedule</code> 并打开 <code style="white-space:pre-wrap">Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule</code>。旧显式 job_arrival/job_cost 样例用这套 Classic API；不要混用 Prosa.Behavior 的实例参数版本，其他版本需要根据 Lean Prosa 当前实际 declaration/API 确认。</span>

## Hidden Goal Head Before Case Split
This is a common local cause of fake branch progress.

Pattern:

- the goal is a named wrapper such as `job_misses_no_deadline j`
- the script does `case Hdone: (completed ...)`
- the first branch ends with `by []`
- the second branch later reports `Expected a single focused goal but 2 goals are focused.`

What happened:

- the split target was not yet the literal head of the goal
- the `case` created branches, but did not rewrite the enclosing goal the way the script expected
- the first branch did not truly close, even if it looked trivial

Hard rule:

- before splitting a boolean goal, check whether the boolean expression is literally present in the current goal head
- if the head is still a wrapper definition, unfold first

Preferred repair:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展开“作业没有错过截止时间”的定义，再用反证法进入证明，让原本藏在定义里的完成条件显露出来。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>修改 rewrite /job_misses_no_deadline 与 apply/negP 两行。<br><strong>为什么：</strong>已核实 Classic 的截止时间条件是 Bool；Lean 需先得到普通大小关系，才能用算术或反证。<br><strong>替换（Rocq → Lean）：</strong>旧两行 → <code style="white-space:pre-wrap">unfold job_misses_no_deadline completed&#10;apply decide_eq_true</code>；此时目标为 job_cost ≤ service，可直接用已有算术界；若选择反证，再 by_contra 引入否定。<br><strong>删除（仅未来 Lean 版）：</strong>省去 SSReflect negP 入口；不能对原 Bool 目标直接 intro。<br><strong>新增（Lean 适配）：</strong>导入 Global.Schedulability 并打开其 Schedulability namespace，与上文 Classic Schedule 接口配套。</span>

```coq
rewrite /job_misses_no_deadline.
apply/negP => Hnot_done.
...
```

Acceptable repair if you still want a split:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>按作业是否完成分成两个分支，并记下每个分支的判断结果，方便化简目标和继续证明。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>修改 case Hdone: ... 的真假分类和各分支的组织。<br><strong>为什么：</strong>Lean cases 产生分支，保留的等式 hDone 可用于化简；case 本身用于选择已生成标签。<br><strong>替换（Rocq → Lean）：</strong>case Hdone: ... → <code style="white-space:pre-wrap">cases hDone : completed job_cost sched j (job_arrival j + job_deadline j) with&#10;| false =&gt;&#10;  -- 用业务条件排除未完成情况&#10;| true =&gt;&#10;  simpa [job_misses_no_deadline, hDone]</code>。false 分支仍需原业务论证，可使用 hDone : completed ... = false；这只是框架，不能作为完整证明提交。</span>

```coq
rewrite /job_misses_no_deadline.
case Hdone: (completed job_cost sched j (job_arrival j + job_deadline j)).
- by rewrite Hdone.
- have Hnot_done : ~~ completed job_cost sched j (job_arrival j + job_deadline j).
   by rewrite Hdone.
  ...
```

Do not write `case Hdone: ...` against a hidden goal head and then trust `by []` to close the first branch.

<a id="lean-review-5"></a>

<span style="color:red">【Explicit Branch Closure Rule｜轻改】<br><strong>本节在做什么：</strong>提醒改写一个假设之后，还要明确用它证明当前目标，才能结束这个分支。<br><strong>改哪里：</strong>修改 Explicit Branch Closure Rule 中改写假设后的收尾动作。<br><strong>为什么：</strong>改写只改变假设的类型，不保证它已经被用来关闭目标；Lean 的普通数值比较是 Prop。<br><strong>替换（Rocq → Lean）：</strong>类型完全相同→exact h；只差简化→simpa using h；h : False→exact False.elim h；自然数严格后继界可由 omega 使用。<br><strong>删除（仅未来 Lean 版）：</strong>普通 Prop 数值比较省去 SSReflect 布尔反射往返。<br><strong>保留：</strong>“改写假设不等于完成分支”的提醒保留。</span>

## Explicit Branch Closure Rule
A branch is not closed just because its last line simplified a local hypothesis.

Typical bad shape:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>这是一个故意展示收尾问题的例子：先证明 x 小于 n + 1，随后只改写这条假设，却没有明确用它完成当前的 x ≤ n 目标。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>修改反例里的 have 声明和只改写假设的最后一步。<br><strong>为什么：</strong>该例要展示的是“假设变了但目标还在”；Lean 版也必须实际展示未关闭目标，不能把反例改成正确证明。<br><strong>替换（Rocq → Lean）：</strong>局部声明→have h : x &lt; n + 1 := by ...；旧假设改写→只做 simp at h，不接收尾，再读取实际剩余目标 x ≤ n。省略号处需提供真实前置证明，避免用占位制造假故障。<br><strong>保留：</strong>保留这个反例的教学角色和实际剩余目标证据。</span>

```coq
have Hlt_succ : x < n + 1.
{
  ...
}
by rewrite addn1 in Hlt_succ.
```

This rewrites `Hlt_succ`, but it may not consume it to solve the enclosing goal `x <= n`.

Preferred repair:

<a id="lean-review-code-4"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>修复上一段的收尾：把 x 小于 n + 1 换成 x ≤ n，再把这条事实直接交给当前目标。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>修改 addn1/ltnS 改写及 have 的 Proof./Qed. 写法。<br><strong>为什么：</strong>已有 hlt : x &lt; n + 1 是 Lean 的 Prop 假设，omega 可直接推出 x ≤ n。<br><strong>替换（Rocq → Lean）：</strong>整个局部收尾 → <code style="white-space:pre-wrap">have hle : x ≤ n := by&#10;  omega&#10;exact hle</code>（上下文须已有 hlt）。<br><strong>删除（仅未来 Lean 版）：</strong>省去 addn1/ltnS 和 Bool↔Prop 往返；Proof./Qed. 改由 := by 缩进块组织。</span>

```coq
have Hlt_succ : x < n + 1.
{
  ...
}
rewrite addn1 ltnS in Hlt_succ.
exact: Hlt_succ.
```

Contradiction branches should also close explicitly:

<a id="lean-review-code-5"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把两个互相矛盾的假设合起来得到 False，用这个矛盾结束当前分支。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>修改矛盾收尾的 exfalso 和对否定假设的应用。<br><strong>为什么：</strong>Lean 的 ¬P 是 P → False；直接应用即可得到矛盾，但 Bool 等式不能直接当作 P/¬P。<br><strong>替换（Rocq → Lean）：</strong>若 hNot : ¬P 且 h : P，写 <code style="white-space:pre-wrap">exfalso&#10;exact hNot h</code>，或 <code style="white-space:pre-wrap">exact False.elim (hNot h)</code>。若原假设仍是 Bool，先桥接为 P/¬P，或由互斥 Bool 值等式推出 False。</span>

```coq
exfalso.
exact: (Hnlt Hlt).
```

If the branch closes by contradiction, end it with the contradiction. Do not leave the contradiction only implicit in a rewritten hypothesis.

<a id="lean-review-6"></a>

<span style="color:red">【Hard Recovery Protocol｜重改｜需基本重写恢复状态机】<br><strong>本节在做什么：</strong>规定发现分支走乱后，按什么顺序暂停、检查并回到正确的证明位置。<br><strong>改哪里：</strong>修改 Hard Recovery Protocol 步骤 4 的分流、Abort. 操作和循环出口。<br><strong>为什么：</strong>Lean 的合法多目标不代表错分支；Abort. 不是 Lean 命令，撤回探索需通过编辑版本恢复。<br><strong>替换（Rocq → Lean）：</strong>错分支→读取标签后用 case 正确标签；局部 have 未完→回到其 := by 块完成；版本不符→重开当前文档；废弃探索→恢复最近保存的文本并重新检查。循环出口改为目标归属正确且局部错误消失。<br><strong>删除（仅未来 Lean 版）：</strong>删除 Abort. 和“必须回到恰好 1 个目标”的恢复条件。<br><strong>新增（Lean 适配）：</strong>在现有恢复机制中接入 Lean 文档同步与检查；零目标需结合源位置区分局部块和整项完成，diagnostics 也须来自当前版本。</span>

## Hard Recovery Protocol
Apply this protocol as soon as the goal count is not exactly one.

1. Freeze theorem progress.
  - Do not choose the next tactic from the intended mathematics.
  - Do not edit for convenience or proof style.
2. Read the live state.
  - Record the number of focused goals.
  - Record which goal is the active one.
  - Record the immediately preceding tactic that changed the state.
3. Classify the most recent structural event.
  - `case`, `elim`, `destruct`, `split`, reflection, or another branch opener
  - `have` or `suff` opening a local subproof
  - closing a branch or returning from a local proof
4. Repair structure before content.
  - Missing bullet: insert the bullet and finish that branch.
  - Unclosed local proof: stay inside `{ ... }` until it is discharged.
  - Wrong branch: return to the correct parent branch before doing anything else.
  - Noisy exploratory branch: `Abort.` it and restart from the last stable point.
5. Re-check the live state.
  - If the goal count is still not exactly one, repeat this protocol.
  - If the goal count is exactly one, only then resume rewriting or theorem application.

Exit condition:
- You may resume ordinary proof search only when there is exactly one focused goal and you can name which branch or outer theorem goal you are in.

<a id="lean-review-7"></a>

<span style="color:red">【Bullet Policy｜中改】<br><strong>本节在做什么：</strong>说明怎样把各个分支和局部证明分开组织，避免步骤用错地方。<br><strong>改哪里：</strong>修改 Bullet Policy 的 -/+/*、花括号、case E: n 和 split 示例。<br><strong>为什么：</strong>Lean 通过 ·、标签和缩进隔离分支，也允许有意批量处理目标。<br><strong>替换（Rocq → Lean）：</strong>Coq -/+/* → · 加缩进；{ ... } → have ... := by 块；case E: n → cases E : n；合取 split→constructor；if/match 分析才考虑 Lean split。<br><strong>删除（仅未来 Lean 版）：</strong>删除“没有逐个 bullet 就一定失败”的判断。<br><strong>新增（Lean 适配）：</strong>补充 Lean &lt;;&gt; 可把同一 tactic 用到所有新目标，all_goals 可作用于当前全部目标；使用时仍需确认目标归属。<br><strong>保留：</strong>分支隔离原则不变。</span>

## Bullet Policy
- Use bullets immediately after any tactic that creates multiple branches, such as `case`, `elim`, `destruct`, `split`, or a case analysis hidden inside a boolean reflection step.
- Keep one bullet level per structural split.
- Finish each bullet completely before returning to the parent bullet.
- If a branch contains a local lemma, prove it inside braces within that branch.
- If a branch ends from a local inequality or contradiction fact, close it explicitly instead of relying on a final rewrite in that fact.

Template:

<a id="lean-review-code-6"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把当前服务量分为 0 和 k + 1 两种情况，分别证明对应分支。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>修改 service_at 上的 case 和两个分支内的 /=。<br><strong>为什么：</strong>service_at : Nat，Lean 用 cases 按 zero/succ 构造子分类，并保留等式 E。<br><strong>替换（Rocq → Lean）：</strong>原分类 → <code style="white-space:pre-wrap">cases E : service_at sched j0 t with&#10;| zero =&gt;&#10;  -- 在零分支完成证明&#10;| succ k =&gt;&#10;  -- 在 k+1 分支完成证明</code>；每个分支的 /= → 适用的 simp [E]。两个注释位置都需补真实证明，Lean case 不能独立用作分类命令。</span>

```coq
case E: (service_at sched j0 t) => [|k] /=.
- (* branch 1 *)
  ...
- (* branch 2 *)
  ...
```

Local sublemma template:

<a id="lean-review-code-7"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>单独证明一个可重复使用的小结论：在给定时间区间内，作业已经到达，而且尚未完成，因此仍在等待或执行。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>修改 PENDING0 的局部声明、区间条件拆解和 pending 结论类型。<br><strong>为什么：</strong>已核实 Classic 的 pending/completed/backlogged 返回 Bool；Lean 不能把裸 Bool 当作普通命题或自然数使用。<br><strong>替换（Rocq → Lean）：</strong>结论明确写为 <code style="white-space:pre-wrap">pending job_arrival job_cost sched j0 t = true</code>；Prop 区间条件用 intro t h; rcases h with ⟨hGE,hLT⟩，保留 decide 合取时用 simp only [Bool.and_eq_true, decide_eq_true_eq] at h；已有 hArr : has_arrived ... = true、hNot : completed ... = false 后用 <code style="white-space:pre-wrap">simp [pending, hArr, hNot]</code> 组合。局部事实用 := by 隔离。<br><strong>删除（仅未来 Lean 版）：</strong>若区间条件选择 Prop，删除原 andP/leP/ltP reflection 步骤。<br><strong>新增（Lean 适配）：</strong>导入 <code style="white-space:pre-wrap">Prosa.Classic.Model.Schedule.Global.Basic.Schedule</code> 并打开 <code style="white-space:pre-wrap">Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule</code>；service_at 返回 Nat。显式 job_arrival/job_cost 的旧样例对应这套 Classic API，不混用 Prosa.Behavior 的实例版本。</span>

```coq
have PENDING0 : forall t, a0 <= t < a0 + R -> pending job_arrival job_cost sched j0 t.
{
  move=> t /andP [GE LT].
  apply/andP; split.
  - by rewrite /has_arrived GE.
  - apply/negP => COMPt.
    ...
}
```

The braces are not cosmetic. They guarantee that the `have` proof is discharged before the main proof resumes.

<a id="lean-review-8"></a>

<span style="color:red">【Goal-Count Checklist｜中改】<br><strong>本节在做什么：</strong>提供每一步前的检查问题，确认自己还在预期的分支和局部证明中。<br><strong>改哪里：</strong>修改 Goal-Count Checklist 的 brace/bullet 字段、目标数量硬条件及分类前提。<br><strong>为什么：</strong>Lean 的重点是局部 by 块和目标标签，合法多目标不能据数量判错，by_cases 也不要求命题在目标头。<br><strong>替换（Rocq → Lean）：</strong>brace/bullet 字段 → <code style="white-space:pre-wrap">Current goal tag:&#10;Enclosing have/by block:&#10;Expected parent goal:&#10;Remaining goal targets:&#10;Current document version:</code>；数量检查 → 列表中每个目标都有已知归属；分类检查 → 确认 cases / by_cases / split 的使用场景。<br><strong>删除（仅未来 Lean 版）：</strong>删除“数量必须为 1”“have 必须带花括号”“拆分项必须在目标头”的通用硬条件。<br><strong>保留：</strong>是否需要 unfold 仍由实际定义和 tactic 决定；文档版本检查是通用一致性要求。</span>

## Goal-Count Checklist
Before every nontrivial tactic, ask these questions.

```text
How many focused goals exist right now?
What did the previous tactic do to that number?
Am I still in the same branch as one line ago?
If this is a `have`, is its proof isolated in `{ ... }`?
If this is a `case` or `split`, did I introduce bullets immediately?
Does the next split target literally occur in the current goal head?
Do I need to unfold a wrapper definition before splitting?
Did the last branch-ending line explicitly consume the closing hypothesis?
```

If any answer is unclear, stop and inspect the proof state before editing further.

<a id="lean-review-9"></a>

<span style="color:red">【Anti-Patterns｜重改】<br><strong>本节在做什么：</strong>列出会掩盖分支错误或让错误继续扩大的常见写法。<br><strong>改哪里：</strong>修改 Anti-Patterns 中的 negP、by []、假设改写和多目标禁令。<br><strong>为什么：</strong>这些旧例子依赖 SSReflect 语法；Lean case 选择标签、by 是块入口，普通 Prop 否定也不依赖反射。<br><strong>替换（Rocq → Lean）：</strong>apply/negP → Prop 否定用 intro，反证用 by_contra，Bool 目标先 simp/decide 桥接；by [] → 按目标选 simp/assumption/rfl；rewrite ... in H → rw [...] at H 后 exact/simpa using H。<br><strong>删除（仅未来 Lean 版）：</strong>删除“未恢复到一个目标就一律把后续错误视为次生错误”的硬规则；Coq case 的分类操作迁移为 cases，不能继续用 Lean case 表示产生新分支。<br><strong>保留：</strong>不掩盖分支错误、不猜测上下文、阻止上下文漂移的原则不变。</span>

## Anti-Patterns
- Do not keep writing linear tactics after a branching tactic created multiple goals.
- Do not patch a focus problem by introducing another helper lemma.
- Do not start a `have` proof inline and then continue the outer script before the local proof is clearly finished.
- Do not assume `apply/negP` is harmless; it can change the goal shape and the remaining branch structure.
- Do not `case` on a boolean term that is still hidden under a named goal definition.
- Do not trust `+ by [].` unless the preceding split actually rewrote the enclosing goal.
- Do not end a branch with `rewrite ... in Hfoo` and assume the enclosing goal is solved; explicitly use `Hfoo`.
- Do not leave a contradiction branch "morally finished"; close it with `exfalso; exact: ...` or the equivalent explicit consumer.
- Do not treat `Expected a single focused goal but 2 goals are focused` as a syntax error. It is a proof-structure error.
- Do not trust the text layout of the script over the live session state.
- Do not respond to secondary errors like `Cannot apply lemma ...` or `No such goal` before restoring the goal count to one.
- Do not keep a branch open just because the surrounding code already looks block-structured.

<a id="lean-review-10"></a>

<span style="color:red">【Trace Example From This Workspace｜重改】<br><strong>本节在做什么：</strong>用一段实际 Coq 失败记录展示，未完成的局部证明怎样影响后面的步骤。<br><strong>改哪里：</strong>修改 Trace Example 的运行轨迹来源与触发证据。<br><strong>为什么：</strong>原 JSONL、.v 路径、时间、行号和报错是 Coq 历史证据，不能证明 Lean 会出现相同焦点故障。<br><strong>替换（Rocq → Lean）：</strong>实际 Lean 教学案例改用一次真实 have/cases 局部块未完成事件，记录文件版本、源位置、操作前后 goals 和第一条 diagnostics。<br><strong>删除（仅未来 Lean 版）：</strong>从 Lean 故障判定依据中移除旧 Coq focused-goal 报错；不把旧日志换个语言标签冒充新证据。<br><strong>新增（Lean 适配）：</strong>按 Lean proof-state/diagnostics 重新采集并验证案例。<br><strong>保留：</strong>当前 JSONL 和 .v 报错保留为“旧 Coq 案例”；不改造或伪造历史日志。</span>

## Trace Example From This Workspace
The trace in `2007-RTSS-Theorem3-opencode-github-copilot_gpt-5-4-20260418145414/opencode_events.jsonl` repeatedly reached:

```text
File "./theorem.v", line 111, characters 2-25:
Error: Expected a single focused goal but 2 goals are focused.
```

The failing script shape was roughly:

<a id="lean-review-code-8"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>这是一个出问题的证明过程：先后打开两个局部证明，又在其中分类讨论，却在尚未完成这些分支时继续使用后面的定理。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>修改故障代码中的 intro、PENDING0/SLOT_BOUND 局部声明和 service_at 分类。<br><strong>为什么：</strong>Lean 局部块需要自己的目标完成；要观察的故障是局部证明未结束，不是复现 Coq focused-goal 数量。<br><strong>替换（Rocq → Lean）：</strong>结构改为 intro j0 ARR0 JOB0；PENDING0/SLOT_BOUND 用 := by；分类用 cases E : service_at ...；pending 类型包含 = true，区间条件选择 Prop 合取或显式 decide 合取。<br><strong>删除（仅未来 Lean 版）：</strong>删除用 Coq focused-goal 计数模拟 Lean 故障的步骤。<br><strong>新增（Lean 适配）：</strong>在每个关键位置读取真实 Lean goal/diagnostic，确认剩余目标属于哪个局部块。</span>

```coq
move=> j0 ARR0 JOB0.
apply/negP => NOTCOMP0.
have PENDING0 : forall t,
    a0 <= t < a0 + R -> pending job_arrival job_cost sched j0 t.
Proof.
  ...
Qed.
have SLOT_BOUND : forall t,
    a0 <= t < a0 + R ->
    1 <= backlogged job_arrival job_cost sched j0 t + service_at sched j0 t.
Proof.
  ...
  case E: (service_at sched j0 t) => [|k] /=.
  - ...
  - ...
Qed.
apply: leq_trans ...
```

Why this drifted:
- `apply/negP` changed the main goal into a reflected boolean goal.
- `have PENDING0` opened a local proof.
- `have SLOT_BOUND` opened another local proof.
- Inside `SLOT_BOUND`, `case E: ...` split the proof again.
- Later tactics resumed as if only one goal were active, but at least one branch or local proof had not been structurally closed the way the script expected.

This is why the right repair is branch management, not another lemma.

What the repair protocol should conclude at this point:
- The main theorem is frozen.
- The only valid next move is to close the currently open local proof or branch.
- Any later lemma-application mismatch is diagnostic noise until the focus count returns to one.

<a id="lean-review-11"></a>

<span style="color:red">【Bullet-Based Repair Pattern｜重改】<br><strong>本节在做什么：</strong>展示怎样依次完成三个局部结论，并在各自的分支结束后继续主证明。<br><strong>改哪里：</strong>修改三个局部事实的声明语法、backlogged 数值贡献和区间求和。<br><strong>为什么：</strong>Lean 的局部 have 块决定作用域；Classic pending/backlogged 是 Bool，求和则需要 Nat 项及明确区间。<br><strong>替换（Rocq → Lean）：</strong>pending → Bool = true；backlogged 加法项 → <code style="white-space:pre-wrap">(backlogged job_arrival job_cost sched j0 t).toNat</code>；区间求和 → <code style="white-space:pre-wrap">∑ t ∈ Finset.Ico a0 (a0 + R), ...</code>；逐点界→Finset.sum_le_sum；总量拆分→Finset.sum_add_distrib。局部证明以 have ... := by 配合 ·/case 组织。<br><strong>删除（仅未来 Lean 版）：</strong>普通 Prop 比较和合取省去反射，改用逻辑引入/消去。<br><strong>保留：</strong>依次证明 pending、逐时隙下界、总量下界的数学分解不变；其他业务接口仍需根据 Lean Prosa 当前实际 declaration/API 确认。</span>

## Bullet-Based Repair Pattern
Prefer this shape instead:

<a id="lean-review-code-9"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把上一段拆成三个依次完成的小证明：先证明作业一直未完成，再证明每个时刻的等待或服务贡献至少为 1，最后把整个区间的贡献加起来。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>修改 PENDING0、SLOT_BOUND、TOTAL_GE_R 三块中的 Bool 化简、区间求和和拼接引理。<br><strong>为什么：</strong>Lean Classic 的等待贡献需要显式 .toNat；区间采用 Finset.Ico 后，原 MathComp bigop 引理不能直接应用。<br><strong>替换（Rocq → Lean）：</strong>PENDING0 → Bool.and_eq_true/simp [pending]；SLOT_BOUND → 展开 backlogged，用 <code style="white-space:pre-wrap">rw [not_scheduled_no_service sched j0 t]</code>，再分类 service_at 并化简 .toNat；TOTAL_GE_R → 用 Finset.sum_le_sum 汇总 SLOT_BOUND，再 Finset.sum_add_distrib；unfold total_interference service_during 让两边都变成 Ico 求和，常数 1 的和用 simp。big_cat_nat → 在端点有序时用 Finset.sum_Ico_consecutive。<br><strong>新增（Lean 适配）：</strong>import Prosa.Classic.Model.Schedule.Global.Basic.Interference，并 open 其 Interference namespace 及前述 Schedule namespace；各局部 := by 块须先完成再进入下一块。</span>

```coq
move=> j0 ARR0 JOB0.
apply/negP => NOTCOMP0.

have PENDING0 : forall t,
    a0 <= t < a0 + R -> pending job_arrival job_cost sched j0 t.
{
  move=> t /andP [GE LT].
  apply/andP; split.
  - by rewrite /has_arrived GE.
  - apply/negP => COMPt.
    apply/negP: NOTCOMP0.
    rewrite /completed in COMPt *.
    apply: leq_trans COMPt _.
    rewrite /service [in X in _ <= X](@big_cat_nat _ _ _ t) //=.
    by rewrite leq_addr.
}

have SLOT_BOUND : forall t,
    a0 <= t < a0 + R ->
    1 <= backlogged job_arrival job_cost sched j0 t + service_at sched j0 t.
{
  move=> t LT.
  have PEND := PENDING0 t LT.
  move: PEND => /andP [ARRIVED NOTCOMP].
  rewrite /backlogged /pending ARRIVED NOTCOMP /=.
  rewrite (not_scheduled_no_service (sched := sched) (j := j0)).
  case E: (service_at sched j0 t) => [|k] /=.
  - by rewrite eq_refl.
  - by rewrite add0n.
}

have TOTAL_GE_R :
    R <= total_interference job_arrival job_cost sched j0 a0 (a0 + R) +
         service_during sched j0 a0 (a0 + R).
{
  apply: leq_trans.
  - apply: leq_sum => t LT.
    exact: SLOT_BOUND t LT.
  - rewrite big_split /=.
    rewrite /total_interference /service_during.
    by rewrite big_const_nat iter_addn mul1n addn0 addKn.
}
```

Why this is safer:
- Each `have` is fully discharged inside braces.
- The outer theorem resumes only after the local proof returns to one focused outer goal.
- The `case` split is handled immediately with bullets.
- The script never pretends a multi-goal state is still linear.

<a id="lean-review-12"></a>

<span style="color:red">【Minimal Debug Log｜中改】<br><strong>本节在做什么：</strong>规定调试时记录当前目标、所属分支以及上一步对证明状态的影响。<br><strong>改哪里：</strong>修改 Minimal Debug Log 的 bullet level/brace 字段和目标读取方式。<br><strong>为什么：</strong>Lean 证明归属靠 goal tag 和局部 by 源范围描述；这里的目标归属不等于 ProsaBuddy 的编辑权限 ownership。<br><strong>替换（Rocq → Lean）：</strong>日志改为 URI/version/position、当前标签、局部块类型、上一步 tactic、剩余目标摘要；可临时用 trace_state 输出真实目标；Need braces → “局部 have 的 := by 范围是否正确”。<br><strong>删除（仅未来 Lean 版）：</strong>删除用 Coq bullet level/brace 判定 Lean 分支的记录格式。<br><strong>保留：</strong>保留上一步效果和目标归属日志；版本/位置记录是通用做法，本 skill 不额外承担 certificate、transaction 或 guard 实现。</span>

## Minimal Debug Log
Keep a short log while editing.

```text
Current focused goal count:
Current active goal owner:
Previous tactic:
Did it open a branch or sublemma: yes/no
Current bullet level:
Need `{ ... }` around `have`: yes/no
Am I inside an unclosed local proof: yes/no
Is the next move a recovery step rather than a math step: yes/no
Next tactic is valid for one goal only: yes/no
Next split target literally appears in the goal head: yes/no
Need to unfold a wrapper definition before splitting: yes/no
Last closing hypothesis was explicitly consumed: yes/no
```

<a id="lean-review-13"></a>

<span style="color:red">【Success Condition｜重改】<br><strong>本节在做什么：</strong>说明什么情况下可以确认各个分支都被正确处理，证明已经回到预期位置。<br><strong>改哪里：</strong>修改 Success Condition 中的目标头、花括号、单目标要求及验证命令。<br><strong>为什么：</strong>Lean 的分支归属取决于局部块和标签，证明过程允许多个目标；成功需由当前版本的真实声明与诊断确认。<br><strong>替换（Rocq → Lean）：</strong>验收改为：每个局部 have 和分支目标已关闭；回到预期外层继续，或完整声明已结束；当前文件通过 lake env lean 并核实无未完成占位。<br><strong>删除（仅未来 Lean 版）：</strong>删除“所有拆分必须在字面目标头”“所有 have 带 braces”“恢复后恰好一个目标”的硬条件。<br><strong>保留：</strong>预期目标真正完成、归属清楚、最新版本验证通过的目的不变。</span>

## Success Condition
The proof is back on track when every branch-producing tactic is followed by bullets, every `have` proof is isolated in `{ ... }`, every split acts on a literal visible goal head rather than a hidden wrapper definition, and every branch-ending hypothesis is explicitly consumed before the script resumes the outer proof.