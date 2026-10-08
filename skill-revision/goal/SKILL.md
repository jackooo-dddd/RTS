<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>一个证明拆成几个分支，或者中途开始证明一个小结论后，你可能没有注意到当前目标已经变了，仍然按原来的大目标继续写。这个 skill 用来找出“现在到底在证明哪一件事”，并整理各部分的先后顺序。<br><strong>具体例子：</strong>你先按“任务已经完成”和“任务尚未完成”分成两个情况。在第二个情况里，又提出一个小结论：“这个任务已经到达。”如果这个小结论还没有证明完，你就开始使用针对主定理的步骤，系统看到的目标和你心里想的目标就会不一致，后面的步骤会接连失败。<br><strong>它会怎么处理：</strong>它要求先查看系统当前列出的目标和可用条件，确认自己位于哪个分支、是否还在某个小结论的证明里。然后把这个局部证明做完，确认返回了预期位置，再继续外层证明；各个分支也分别处理清楚。最终要做到：每一步都用在它实际面对的目标上，而不是靠代码排版猜测证明进行到了哪里。</span>

<span style="color:red">【When to Use / Trace Example｜首要结构性问题 1】<a href="#lean-review-10">点击跳转</a><br><strong>为什么会有结构性问题：</strong>这个 skill 用一条 Coq 焦点报错识别证明分支问题，再用工作区 JSONL 记录展示错误如何发生。换成 Lean 后，这些记录仍能解释原 Coq 案例，却不能证明 Lean 会在同一步报同一种错。因此只翻译证明代码还不够，原来的触发依据和诊断案例也要重新验证。<br><strong>Lean 中大致怎么做：</strong>用真实 Lean 证明记录中的当前目标、分支位置和诊断重建触发条件与案例；原 Coq 记录保留为历史对照。 <a href="https://lean-lang.org/doc/reference/latest/Tactic-Proofs/">Lean 官方说明</a>。</span>

<span style="color:red">【需迁移的 section｜点击跳转】<a href="#lean-review-1">When to Use</a>；<a href="#lean-review-2">Core Rule</a>；<a href="#lean-review-4">Hidden Goal Head Before Case Split</a>；<a href="#lean-review-6">Hard Recovery Protocol</a>；<a href="#lean-review-9">Anti-Patterns</a>；<a href="#lean-review-10">Trace Example From This Workspace</a>；<a href="#lean-review-11">Bullet-Based Repair Pattern</a>。</span>

<span style="color:red">【Rocq 示例需转为 Lean 代码｜点击跳转】<a href="#lean-review-code-1">示例 1</a>；<a href="#lean-review-code-2">示例 2</a>；<a href="#lean-review-code-3">示例 3</a>；<a href="#lean-review-code-4">示例 4</a>；<a href="#lean-review-code-5">示例 5</a>；<a href="#lean-review-code-6">示例 6</a>；<a href="#lean-review-code-7">示例 7</a>；<a href="#lean-review-code-8">示例 8</a>；<a href="#lean-review-code-9">示例 9</a>。共 9 个原代码块，全部保留。</span>

---
name: goal-focus-discipline
#<span style="color:red">【description】将 Coq/SSReflect 后端范围改为 Lean，并按实际 Lean 诊断描述分支与局部证明问题；原 have 的声明连接语法需换为 := by。检查目标、逐支组织和完成局部证明的用途保留。</span>
description: 'Handle Coq and ssreflect proof-state drift by checking the current number of goals after every tactic that can split or close goals, using bullets to manage branches, and proving any have-generated sublemma inside braces before returning to the main line.'
#<span style="color:red">【argument-hint】目标数量、前一步 tactic 和所在分支仍是通用输入；迁移后由实际 Lean 会话提供这些信息，字段本身不必重设。</span>
argument-hint: 'Describe the current goal count, the previous tactic, and the branch or sublemma that introduced the drift.'
user-invocable: true
---



# Goal Focus Discipline <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【帮助确认当前正在证明哪个目标，避免在分支或局部证明尚未结束时误写外层步骤。】</span>

<a id="lean-review-1"></a>



## When to Use <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出哪些报错或证明行为可能说明当前分支已经与预期不一致。｜重改】</span>

<span style="color:red"><strong>为什么要改：</strong>这是 Coq 的特定焦点报错，不能直接作为 Lean 的故障入口。<br><strong>怎么改：</strong>用实际 Lean 诊断及该位置的目标、分支状态重建触发条件。</span>

- <span style="color:gray">Coq reports `Expected a single focused goal but 2 goals are focused.`</span>

<span style="color:red"><strong>为什么要改：</strong>① Coq case/destruct 用来分类，Lean case 却选择已有分支。② Coq split 可拆合取，Lean split 主要拆 if/match。③ apply/negP 是 Bool 反射，普通 Lean ¬P 不需这一步。<br><strong>怎么改：</strong>分类用 cases/by_cases，合取用 constructor，普通否定用 intro；业务 Bool 按实际定义处理。</span>

- A proof used to have one main line, then <span style="color:gray">`case`</span>, `have`, <span style="color:gray">`apply/negP`</span>, <span style="color:gray">`split`</span>, or <span style="color:gray">`destruct`</span> was added and later tactics stopped fitting.
- The model starts adding extra lemmas instead of first checking whether the proof state already drifted.
- A local fact such as `PENDING0` or `SLOT_BOUND` is introduced, and later tactics behave as if the main goal were still the only goal.

<span style="color:red"><strong>为什么要改：</strong>这里的 focus error 指上面的 Coq 报错，case 也是 Coq 的分类命令；Lean case 用于选择已有分支。<br><strong>怎么改：</strong>分类改用 cases/by_cases，并按实际 Lean 运行记录描述错误出现的位置。</span>

- <span style="color:gray">The focus error</span> appears right after <span style="color:gray">`case`</span> or another boolean split, but the split target may still be hidden under a named definition or wrapper.
- A branch "looks done" because the last line rewrote a local hypothesis, but the enclosing goal was never explicitly discharged.

<a id="lean-review-2"></a>



## Core Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【要求先看系统当前的目标和分支位置，再决定下一步证明动作。｜中改】</span>
Do not choose the next tactic from proof intent alone. First check how many goals exist now, and whether the previous tactic opened or closed any goal.




If there is more than one goal, switch to bullet management immediately. Do not continue with a single-goal script.

If `have` is used to introduce a lemma, prove it inside `{ ... }` and return only after that local proof is closed.


<span style="color:red"><strong>为什么要改：</strong>这里的 case/destruct 是 Coq 分类命令；Lean case 选择已有分支，不负责创建分类。<br><strong>怎么改：</strong>按数据或命题选择 cases/by_cases。</span>

If a <span style="color:gray">`case`</span>, <span style="color:gray">`destruct`</span>, or reflected boolean split targets a term that is still hidden under a named definition, unfold first. Otherwise the split can create branches without actually changing the enclosing goal.




If the last useful line of a branch only rewrites inside a local hypothesis, do not assume the branch is closed.

<span style="color:red"><strong>为什么要改：</strong>这里需要替换的是 SSReflect exact: 的冒号；exfalso 和显式使用结论收尾的原则可以保留。<br><strong>怎么改：</strong>Lean 写 exfalso 后 exact h，或直接用 exact False.elim hFalse。</span>

Explicitly consume that hypothesis with `exact`, `apply`, or <span style="color:gray">`exfalso; exact:`</span> if it is meant to close the enclosing goal.

When the visible script structure and the live proof state disagree, trust the live proof state. Do not keep editing as if braces, bullets, or a finished-looking `have` block had already restored focus.




If the current focused goal count is not exactly one, the next step is a recovery step, not a math step.

Recovery-step whitelist when the goal count is not exactly one:
- inspect the current goals
- introduce or finish bullets
- close the current `{ ... }` subproof
- return to the parent branch
- abort and restart a noisy exploratory branch




Until focus returns to exactly one intended goal, do not:

<span style="color:red"><strong>为什么要改：</strong>suff 是 SSReflect 引入充分条件的语法。<br><strong>怎么改：</strong>在 Lean 用 suffices 组织相同的充分条件证明。</span>

- add a new `have`, <span style="color:gray">`suff`</span>, or helper lemma
- attempt a new `rewrite`, `apply`, `exact`, or arithmetic step for the outer theorem
- treat downstream messages such as missing hypotheses, reused names, or failed lemma applications as the main problem


<span style="color:red"><strong>为什么要改：</strong>这些字符串来自 Coq 的历史诊断，不能直接作为 Lean 报错的匹配词表。<br><strong>怎么改：</strong>用真实 Lean 诊断及对应源码位置重新核实各条分类。</span>

Errors such as <span style="color:gray">`Cannot apply lemma ...`</span>, <span style="color:gray">`No such goal`</span>, <span style="color:gray">`... already used`</span>, and <span style="color:gray">`The variable ... was not found`</span> are often secondary effects of proof-state drift once multiple goals are live. Do not repair them before restoring focus.

<a id="lean-review-3"></a>



## Required Procedure <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【给出检查上一步、确认当前分支并继续证明的操作顺序。｜中改】</span>
1. Read the current proof state before the next step.
   - Record the exact number of focused goals.
   - Record the shape of the current goal.
2. Inspect the previous tactic.
   - Did it split the proof into branches?
   - Did it create a local subgoal?
   - Did it close a branch?



3. Inspect the literal goal head before any new split.

  <span style="color:red"><strong>为什么要改：</strong>下面的 case/destruct 指 Coq 分类命令；Lean 的同名 case 只选择已有分支。<br><strong>怎么改：</strong>数据分类用 cases，命题分类按需用 by_cases。</span>

  - If the next <span style="color:gray">`case`</span>, <span style="color:gray">`destruct`</span>, or reflection step targets a term hidden under a definition, unfold first.
  - Do not split on mathematical intent alone. Check whether the split target literally occurs in the current goal or active hypothesis.



4. If the goal count changed, respond structurally, not mathematically.
   - New branch: introduce a bullet.
   - Local lemma from `have`: open `{ ... }`, finish it, then return.
   - Closed branch: verify that focus returned to the intended outer goal.
5. When a branch seems finished, verify that the last line actually discharged the enclosing goal.
  - Rewriting inside `Hlt_succ`, `Hdone`, or another local fact is not the same as closing the branch.

  <span style="color:red"><strong>为什么要改：</strong>显式收尾的原则可保留；这里灰色写法中的 exact: 冒号是 SSReflect 语法。<br><strong>怎么改：</strong>在 Lean 用 exact h 或 simpa using h；矛盾收尾可用 exfalso 后 exact。</span>

  - If the branch should end from that fact, finish with `exact`, `apply`, or <span style="color:gray">`exfalso; exact:`</span>.
6. Only after focus is stable should you pick the next rewriting or reasoning step.
7. Do not add bridge lemmas, arithmetic lemmas, or helper facts just to avoid a focus problem. Fix the branch structure first.

<a id="lean-review-4"></a>



## Hidden Goal Head Before Case Split <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【说明目标藏在一个定义后面时，怎样检查分类是否真的推进了当前证明。｜重改】</span>
This is a common local cause of fake branch progress.

Pattern:

- the goal is a named wrapper such as `job_misses_no_deadline j`

<span style="color:red"><strong>为什么要改：</strong>原 case Hdone: ... 新建分类并记录等式；Lean case 只选择已有的分支标签。<br><strong>怎么改：</strong>对 completed 的 Bool 值使用 cases hDone : completed ...，按 false/true 分支继续。</span>

- the script does <span style="color:gray">`case Hdone: (completed ...)`</span>

<span style="color:red"><strong>为什么要改：</strong>by [] 是 SSReflect 的紧凑收尾，不能作为 Lean 的同名自动完成命令。<br><strong>怎么改：</strong>查看该支实际目标，再用 rfl、assumption、simp 或需要的业务事实完成它。</span>

- the first branch ends with <span style="color:gray">`by []`</span>

<span style="color:red"><strong>为什么要改：</strong>这条焦点报错属于原 Coq 运行记录，不能假设同一 Lean 分支也给出它。<br><strong>怎么改：</strong>记录 Lean 该位置的实际诊断和未完成目标，再判断哪一支没有结束。</span>

- the second branch later reports <span style="color:gray">`Expected a single focused goal but 2 goals are focused.`</span>

What happened:

- the split target was not yet the literal head of the goal

<span style="color:red"><strong>为什么要改：</strong>这句描述的是原 Coq case 的分类效果；Lean case 不负责创建这些分支。<br><strong>怎么改：</strong>用 cases/by_cases 分类后，检查等式或假设是否已作用到当前目标，必要时再简化。</span>

- the <span style="color:gray">`case`</span> created branches, but did not rewrite the enclosing goal the way the script expected
- the first branch did not truly close, even if it looked trivial

Hard rule:




- before splitting a boolean goal, check whether the boolean expression is literally present in the current goal head
- if the head is still a wrapper definition, unfold first

Preferred repair:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展开“作业没有错过截止时间”的定义，再用反证法进入证明，让原本藏在定义里的完成条件显露出来。<br><strong>2）怎么换成 Lean 代码：</strong>Classic 的截止时间条件仍是 Bool，原 negP 入口不能照搬。导入 Global.Schedulability 并打开其 Schedulability namespace 后，用 <code style="white-space:pre-wrap">unfold job_misses_no_deadline completed&#10;apply decide_eq_true</code> 得到自然数比较，再用算术界或 by_contra。通用片段已按本地 Lean 4.33.1 / 锁定 Mathlib 核对，版本变化后重新 #check；完整业务证明仍需实际上下文。</span>

```coq
rewrite /job_misses_no_deadline.
apply/negP => Hnot_done.
...
```

Acceptable repair if you still want a split:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>按作业是否完成分成两个分支，并记下每个分支的判断结果，方便化简目标和继续证明。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 用 cases 产生真假分支，case 只选择已有分支。改用 <code style="white-space:pre-wrap">cases hDone : completed job_cost sched j (job_arrival j + job_deadline j) with</code>，分别完成 false/true 分支；true 分支可 simpa [job_misses_no_deadline, hDone]，false 分支仍须原业务论证。</span>

```coq
rewrite /job_misses_no_deadline.
case Hdone: (completed job_cost sched j (job_arrival j + job_deadline j)).
- by rewrite Hdone.
- have Hnot_done : ~~ completed job_cost sched j (job_arrival j + job_deadline j).
   by rewrite Hdone.
  ...
```


<span style="color:red"><strong>为什么要改：</strong>case Hdone: ... 与 by [] 分别是 Coq 分类语法和 SSReflect 收尾语法。<br><strong>怎么改：</strong>用 cases 记录分类等式，再用适用的 simp、rfl 或 exact 完成分支。</span>

Do not write <span style="color:gray">`case Hdone: ...`</span> against a hidden goal head and then trust <span style="color:gray">`by []`</span> to close the first branch.

<a id="lean-review-5"></a>



## Explicit Branch Closure Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【提醒改写一个假设之后，还要明确用它证明当前目标，才能结束这个分支。｜轻改】</span>
A branch is not closed just because its last line simplified a local hypothesis.

Typical bad shape:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>这是一个故意展示收尾问题的例子：先证明 x 小于 n + 1，随后只改写这条假设，却没有明确用它完成当前的 x ≤ n 目标。<br><strong>2）怎么换成 Lean 代码：</strong>这个反例要保留“改了假设却没完成目标”的故障，不能直接改成成功证明。用 have h : x &lt; n + 1 := by 建立真实局部证明，只执行 simp at h，再展示实际剩余目标；不以占位伪造失败。</span>

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

<span style="color:red"><strong>1）这段代码在干嘛：</strong>修复上一段的收尾：把 x 小于 n + 1 换成 x ≤ n，再把这条事实直接交给当前目标。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 的 hlt : x &lt; n + 1 已是 Prop，原 addn1/ltnS 和反射步骤可省去。已有 hlt 时可写 <code style="white-space:pre-wrap">have hle : x ≤ n := by&#10;  omega&#10;exact hle</code>；局部证明由 := by 缩进块组织。</span>

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

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把两个互相矛盾的假设合起来得到 False，用这个矛盾结束当前分支。<br><strong>2）怎么换成 Lean 代码：</strong>矛盾收尾的方法保留，只需替换 exact:；若假设仍是 Bool，不能直接套用命题及其否定的写法。对于 hNot : ¬P 和 h : P，使用 <code style="white-space:pre-wrap">exact False.elim (hNot h)</code>；Bool 假设先桥接或由互斥值等式推出 False。</span>

```coq
exfalso.
exact: (Hnlt Hlt).
```

If the branch closes by contradiction, end it with the contradiction. Do not leave the contradiction only implicit in a rewritten hypothesis.

<a id="lean-review-6"></a>



## Hard Recovery Protocol <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【规定发现分支走乱后，按什么顺序暂停、检查并回到正确的证明位置。｜中改】</span>



Apply this protocol as soon as the goal count is not exactly one.

1. Freeze theorem progress.
  - Do not choose the next tactic from the intended mathematics.
  - Do not edit for convenience or proof style.
2. Read the live state.
  - Record the number of focused goals.
  - Record which goal is the active one.
  - Record the immediately preceding tactic that changed the state.
3. Classify the most recent structural event.

  <span style="color:red"><strong>为什么要改：</strong>下面两行列的是 Coq 分类、归纳、合取与充分条件命令；在 Lean 中同名命令的职责可能不同。<br><strong>怎么改：</strong>分类用 cases，归纳按需用 induction，合取用 constructor，充分条件用 suffices；局部 have 用 := 连接证明。</span>

  - <span style="color:gray">`case`</span>, <span style="color:gray">`elim`</span>, <span style="color:gray">`destruct`</span>, <span style="color:gray">`split`</span>, reflection, or another branch opener
  - `have` or <span style="color:gray">`suff`</span> opening a local subproof
  - closing a branch or returning from a local proof
4. Repair structure before content.
  - Missing bullet: insert the bullet and finish that branch.
  - Unclosed local proof: stay inside `{ ... }` until it is discharged.
  - Wrong branch: return to the correct parent branch before doing anything else.

  <span style="color:red"><strong>为什么要改：</strong>Abort. 是 Coq 的放弃命令，不能作为 Lean 的声明结束语句直接使用。<br><strong>怎么改：</strong>恢复已保存的源码并重新检查，再从可靠位置继续。</span>

  - Noisy exploratory branch: <span style="color:gray">`Abort.`</span> it and restart from the last stable point.
5. Re-check the live state.

  

  - If the goal count is still not exactly one, repeat this protocol.
  - If the goal count is exactly one, only then resume rewriting or theorem application.

Exit condition:



- You may resume ordinary proof search only when there is exactly one focused goal and you can name which branch or outer theorem goal you are in.

<a id="lean-review-7"></a>



## Bullet Policy <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【说明怎样把各个分支和局部证明分开组织，避免步骤用错地方。｜中改】</span>

<span style="color:red"><strong>为什么要改：</strong>逐支纪律和花括号隔离可以保留；灰色处需要按命令职责迁移，示例中的 Coq -/+/* 与句点也需替换。<br><strong>怎么改：</strong>分类用 cases、归纳用 induction、合取用 constructor；分支可用 ·/case。Lean 也支持花括号。</span>

- Use bullets immediately after any tactic that creates multiple branches, such as <span style="color:gray">`case`</span>, <span style="color:gray">`elim`</span>, <span style="color:gray">`destruct`</span>, <span style="color:gray">`split`</span>, or a case analysis hidden inside a boolean reflection step.
- Keep one bullet level per structural split.
- Finish each bullet completely before returning to the parent bullet.
- If a branch contains a local lemma, prove it inside braces within that branch.
- If a branch ends from a local inequality or contradiction fact, close it explicitly instead of relying on a final rewrite in that fact.

Template:

<a id="lean-review-code-6"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把当前服务量分为 0 和 k + 1 两种情况，分别证明对应分支。<br><strong>2）怎么换成 Lean 代码：</strong>service_at 返回 Nat，但 Lean 的分类命令是 cases，原 case ... /= 不能直接使用。写 <code style="white-space:pre-wrap">cases E : service_at sched j0 t with</code>，按 zero/succ k 完成两个分支；/= 改为适用的 simp [E]，不能只留下分支框架。</span>

```coq
case E: (service_at sched j0 t) => [|k] /=.
- (* branch 1 *)
  ...
- (* branch 2 *)
  ...
```

Local sublemma template:

<a id="lean-review-code-7"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>单独证明一个可重复使用的小结论：在给定时间区间内，作业已经到达，而且尚未完成，因此仍在等待或执行。<br><strong>2）怎么换成 Lean 代码：</strong>这套 Classic pending 仍返回 Bool；普通 Prop 区间条件则无需 andP/leP/ltP。需要改的是原 have 声明的连接语法和句点；Lean 花括号本身可保留。推荐用 have ... := by，结论明确为 <code style="white-space:pre-wrap">pending job_arrival job_cost sched j0 t = true</code>。Prop 区间用 rcases 拆开；已有到达为 true、完成为 false 的事实后，用 simp [pending, hArr, hNot] 组合。保留 Bool 合取时再做对应桥接。</span>

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



## Goal-Count Checklist <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【提供每一步前的检查问题，确认自己还在预期的分支和局部证明中。｜中改】</span>
Before every nontrivial tactic, ask these questions.

<span style="color:red"><strong>为什么要改：</strong>表中的 case/split 指 Coq 分类与合取拆分；Lean 同名命令的职责不同。<br><strong>怎么改：</strong>按 cases/by_cases/constructor 的实际用途替换命令名；目标数量和局部隔离的记录方式可保留。</span>

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



## Anti-Patterns <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出会掩盖分支错误或让错误继续扩大的常见写法。｜重改】</span>



- Do not keep writing linear tactics after a branching tactic created multiple goals.
- Do not patch a focus problem by introducing another helper lemma.
- Do not start a `have` proof inline and then continue the outer script before the local proof is clearly finished.

<span style="color:red"><strong>为什么要改：</strong>apply/negP 处理的是 SSReflect Bool 反射；Lean 普通 ¬P 本来就是命题。<br><strong>怎么改：</strong>普通否定用 intro；若实际前提是业务 Bool，则按其定义或真值等式处理。</span>

- Do not assume <span style="color:gray">`apply/negP`</span> is harmless; it can change the goal shape and the remaining branch structure.

<span style="color:red"><strong>为什么要改：</strong>这里的 case 指 Coq 的分类命令；Lean case 只选择已有分支。<br><strong>怎么改：</strong>数据或 Bool 值分类用 cases，命题分类按需用 by_cases。</span>

- Do not <span style="color:gray">`case`</span> on a boolean term that is still hidden under a named goal definition.

<span style="color:red"><strong>为什么要改：</strong>+ by []. 是 Coq bullet 加 SSReflect 收尾语法，不能作为 Lean 的分支证明。<br><strong>怎么改：</strong>用 · 或 case 进入分支，再用适用的 rfl/simp/exact 等步骤完成目标。</span>

- Do not trust <span style="color:gray">`+ by [].`</span> unless the preceding split actually rewrote the enclosing goal.

<span style="color:red"><strong>为什么要改：</strong>改写假设后仍须显式使用它，这一点可保留；Lean 的改写位置语法用 at，不用此处的 in。<br><strong>怎么改：</strong>写 rw [等式] at Hfoo 或 simp at Hfoo，再 exact Hfoo / simpa using Hfoo。</span>

- Do not end a branch with <span style="color:gray">`rewrite ... in Hfoo`</span> and assume the enclosing goal is solved; explicitly use `Hfoo`.

<span style="color:red"><strong>为什么要改：</strong>矛盾收尾可保留，需要去掉 exact: 的 SSReflect 冒号。<br><strong>怎么改：</strong>可用 exfalso 后 exact hFalse，或 exact False.elim hFalse。</span>

- Do not leave a contradiction branch "morally finished"; close it with <span style="color:gray">`exfalso; exact: ...`</span> or the equivalent explicit consumer.

<span style="color:red"><strong>为什么要改：</strong>这条分类结论针对 Coq 的特定焦点报错，不能直接套在 Lean 的诊断文字上。<br><strong>怎么改：</strong>根据实际 Lean 错误和发生位置建立对应的诊断说明。</span>

- Do not treat <span style="color:gray">`Expected a single focused goal but 2 goals are focused`</span> as a syntax error. It is a proof-structure error.
- Do not trust the text layout of the script over the live session state.

<span style="color:red"><strong>为什么要改：</strong>这里列的是旧 Coq 报错词汇，不能直接作为 Lean 的错误匹配规则。<br><strong>怎么改：</strong>替换为实际观察到的 Lean 诊断，并保留对应上下文。</span>

- Do not respond to secondary errors like <span style="color:gray">`Cannot apply lemma ...`</span> or <span style="color:gray">`No such goal`</span> before restoring the goal count to one.
- Do not keep a branch open just because the surrounding code already looks block-structured.

<a id="lean-review-10"></a>



## Trace Example From This Workspace <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【用一段实际 Coq 失败记录展示，未完成的局部证明怎样影响后面的步骤。｜重改】</span>

<span style="color:red"><strong>为什么要改：</strong>这份 JSONL 和下方 .v 输出是 Coq 历史证据；重写证明代码不会自动得到 Lean 的同类运行记录。<br><strong>怎么改：</strong>保留为历史案例；未来 Lean 版另采集真实前后目标、源码位置及诊断。</span>

The trace in <span style="color:gray">`2007-RTSS-Theorem3-opencode-github-copilot_gpt-5-4-20260418145414/opencode_events.jsonl`</span> repeatedly reached:

```text
File "./theorem.v", line 111, characters 2-25:
Error: Expected a single focused goal but 2 goals are focused.
```

The failing script shape was roughly:

<a id="lean-review-code-8"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>这是一个出问题的证明过程：先后打开两个局部证明，又在其中分类讨论，却在尚未完成这些分支时继续使用后面的定理。<br><strong>2）怎么换成 Lean 代码：</strong>① 原 Proof./Qed. 局部边界和句点不能直接用于 Lean，以 := by 连接证明。② 原 Coq 焦点故障不保证在 Lean 复现，必须读取实际诊断。以 := by 组织 PENDING0/SLOT_BOUND，用 cases 分类，并读取各处真实目标；pending 明确为 Bool = true。保留“局部块未完成”的教学问题，不模拟旧 focused-goal 计数。</span>

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

<span style="color:red"><strong>为什么要改：</strong>原步骤通过 negP 把 Bool 否定接到命题推理；Lean 普通 ¬P 无须该反射入口，但业务 Bool 仍可能需要处理。<br><strong>怎么改：</strong>普通否定直接引入假设；实际 Bool 前提按定义或相应真值事实证明。</span>

- <span style="color:gray">`apply/negP` changed the main goal into a reflected boolean goal</span>.
- `have PENDING0` opened a local proof.
- `have SLOT_BOUND` opened another local proof.

<span style="color:red"><strong>为什么要改：</strong>这里的 Coq case 在创建数据分类；Lean case 只选择已有分支。<br><strong>怎么改：</strong>用 cases E : ... 创建分类，再用分支标签或 · 分别处理。</span>

- Inside `SLOT_BOUND`, <span style="color:gray">`case E: ...`</span> split the proof again.
- Later tactics resumed as if only one goal were active, but at least one branch or local proof had not been structurally closed the way the script expected.

This is why the right repair is branch management, not another lemma.

What the repair protocol should conclude at this point:
- The main theorem is frozen.
- The only valid next move is to close the currently open local proof or branch.



- Any later lemma-application mismatch is diagnostic noise until the focus count returns to one.

<a id="lean-review-11"></a>



## Bullet-Based Repair Pattern <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【展示怎样依次完成三个局部结论，并在各自的分支结束后继续主证明。】</span>
Prefer this shape instead:

<a id="lean-review-code-9"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把上一段拆成三个依次完成的小证明：先证明作业一直未完成，再证明每个时刻的等待或服务贡献至少为 1，最后把整个区间的贡献加起来。<br><strong>2）怎么换成 Lean 代码：</strong>Classic 的等待贡献是 Bool，而区间和需要 Nat 项；原 MathComp 求和与反射不能直接套用。保留三个局部证明：pending ... = true；等待贡献用 <code style="white-space:pre-wrap">(backlogged job_arrival job_cost sched j0 t).toNat</code>；区间采用 Finset.Ico。导入 Prosa.Classic.Model.Schedule.Global.Basic.Interference 并打开其 Interference namespace；逐时隙证明可用 not_scheduled_no_service，汇总用 Finset.sum_le_sum、Finset.sum_add_distrib；端点有序时才用 Finset.sum_Ico_consecutive。每个 := by 块完成后再继续。</span>

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

<span style="color:red"><strong>为什么要改：</strong>原 Coq case 负责分类；Lean 的 case 只选择已有标签，不能只保留同名命令。<br><strong>怎么改：</strong>用 cases 创建分支，再以 · 或 case 组织；逐支完成的原则保留。</span>

- The <span style="color:gray">`case`</span> split is handled immediately with bullets.
- The script never pretends a multi-goal state is still linear.

<a id="lean-review-12"></a>



## Minimal Debug Log <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【规定调试时记录当前目标、所属分支以及上一步对证明状态的影响。】</span>
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



## Success Condition <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【说明什么情况下可以确认各个分支都被正确处理，证明已经回到预期位置。】</span>



The proof is back on track when every branch-producing tactic is followed by bullets, every `have` proof is isolated in `{ ... }`, every split acts on a literal visible goal head rather than a hidden wrapper definition, and every branch-ending hypothesis is explicitly consumed before the script resumes the outer proof.