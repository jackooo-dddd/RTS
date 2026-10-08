<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>你要证明“满足某个条件的对象最多有多少个”，但当前证明把这个数量写成了加法，而手头的定理用的是“对象个数”的写法，直接套用时对不上。这个 skill 帮你把两种写法接起来。<br><strong>具体例子：</strong>假设有 A、B、C、D 四个任务，其中 A、C 没完成，B、D 已完成。计算未完成任务数，可以逐个检查：没完成就记 1，完成就记 0，最后得到 1 + 0 + 1 + 0 = 2；也可以先挑出 A、C，再数出有 2 个任务。两种做法算的是同一个数量，但证明代码里的表达式不同。<br><strong>它会怎么处理：</strong>如果接下来要用的定理讨论“未完成任务有几个”，它就指导你先证明“逐项加起来的结果，等于挑出来的任务个数”，把当前目标换成定理能够使用的写法，再证明这个个数不超过某个限制。如果后续定理仍然讨论求和，就保留求和写法。它的重点是安排这些转换，避免证明一直在几种写法之间来回切换。</span>

<span style="color:red">【Lean迁移总评】本 skill 的核心 proof methodology 可保留约 80%（定性估计）；主要修改集中在：① MathComp 计数与求和表示 ② SSReflect 证明模板 ③ Bool/Prop reflection 与报错签名。整体重写力度：中重。</span>

<span style="color:red">【Bool / Prop Separation｜首要结构性问题】<a href="#lean-review-bool-prop">点击跳转</a><br><strong>改哪里：</strong>Bool / Prop Separation 子模块及其后面的层级表、交接流程、模板 4/5；这里负责把计数界交给最后的算术证明。<br><strong>为什么：</strong>MathComp 的自然数比较通常返回 Bool，原来要先转为 Prop 才做算术；Lean 普通 Nat 的 &lt;、≤ 本来就是 Prop。只换 tactic 会把已经没有必要的往返流程也搬过去，受影响的是这个子模块，不是整份计数方法。<br><strong>替换（Rocq → Lean）：</strong>实际输入为 <code style="white-space:pre-wrap">hb : decide P = true</code> 时，用 <code style="white-space:pre-wrap">have hp : P := of_decide_eq_true hb</code>；实际输出为 <code style="white-space:pre-wrap">decide P = true</code> 时，用 <code style="white-space:pre-wrap">exact decide_eq_true hp</code>。<br><strong>删除（仅未来 Lean 版）：</strong>删除普通 Nat 不等式的 ltP/leP 转换及算完后转回 Bool 的固定要求。<br><strong>新增（Lean 适配）：</strong>入口先分三类：普通 Prop 比较直接证明；decide 包装提取命题；业务 Bool 先展开实际定义再确认能否桥接。本地 Prosa 的 pending/completed 仍返回 Bool，必须保留这类真实入口。<br><strong>保留：</strong>先把计数写法稳定下来、再做算术；必要桥接后不反复切换表示。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-bool-prop">Bool / Prop Separation</a>；<a href="#lean-review-problem-shape">Problem Shape</a>；<a href="#lean-review-layer-map">Layer Map</a>；<a href="#lean-review-handoff">One-Way Handoff Protocol</a>；<a href="#lean-review-local-bridges">Common Local Bridges</a>；<a href="#lean-review-failure-signatures">Failure Signatures For This Skill</a>。重写 Rocq 执行内容，保留核心证明方法。</span>

<span style="color:red">【Rocq 示例需转为 Lean 代码｜点击跳转】<a href="#lean-review-template-1">Template 1</a>；<a href="#lean-review-template-2">Template 2</a>；<a href="#lean-review-template-3">Template 3</a>；<a href="#lean-review-template-4">Template 4</a>；<a href="#lean-review-template-5">Template 5</a>；<a href="#lean-review-contradiction">Contradiction Pattern With ltnNge</a>。共 6 个 coq 代码块。</span>

<span style="color:red">【行内代码与表示需转换｜点击跳转】<a href="#lean-review-layer-map">Layer Map</a>；<a href="#lean-review-handoff">One-Way Handoff Protocol</a>；<a href="#lean-review-local-bridges">Common Local Bridges</a>；<a href="#lean-review-normal-form">Normal-Form Decision</a>；<a href="#lean-review-bridge-order">Canonical Bridge Order</a>；<a href="#lean-review-procedure">Required Procedure</a>；<a href="#lean-review-anti-patterns">Anti-Patterns</a>。当前仅标注迁移任务，原示例保留。</span>

---
name: ssreflect-count-bridging
description: 'Handle ssreflect and MathComp proof branches where the same quantity appears as an indicator sum, a filtered big operator, a count, and then a min-bound or arithmetic inequality. Use when `big_mkcond`, `sum1_count`, `big_filter`, `count`, `Nat.min` or `minn`, or `if ... then 1 else 0` appear together and rewrites keep failing because the branch has no stable counting normal form.'
argument-hint: 'Describe the current indicator or count shape, the target equality or inequality, and the first failed rewrite or bridge step.'
user-invocable: true
---

<span style="color:red">【Frontmatter｜中改】<br><strong>改哪里：</strong>frontmatter 的 name、description 及其语言/引理触发词；argument-hint、user-invocable 保留。<br><strong>为什么：</strong>旧触发词指向 SSReflect/MathComp，无法识别 Lean 里对应的计数表示。<br><strong>替换（Rocq → Lean）：</strong>建议 name → lean-count-bridging；description 中 MathComp 触发词 → List.countP、List.filter、List.sum、Finset.filter、Finset.card、Finset.sum、Nat.min 和 if/Bool.toNat。<br><strong>新增（Lean 适配）：</strong>给例子注明导入：通用例子用 import Mathlib；项目列表求和封装用 import Prosa.Util.Sum。以下通用片段已按本地 Lean 4.33.1 / 项目锁定的 Mathlib 核对；版本变化后重新 #check。代码中的 h、xs、P 是局部变量，完整业务证明仍需目标上下文。</span>

<span style="color:red">【Ssreflect Count Bridging】<br><strong>本节在做什么：</strong>帮助把求和、筛选后的数量和计数结果接起来，让后面的数量上界证明能够继续。</span>

# Ssreflect Count Bridging

<span style="color:red">【When to Use｜中改】<br><strong>本节在做什么：</strong>列出哪些计数证明卡住的情况适合使用这份 skill。<br><strong>改哪里：</strong>When to Use 第一条的求和、计数、过滤和 min 名称，以及它们对应的容器/谓词类型。<br><strong>为什么：</strong>MathComp 的 seq 允许重复；Lean 的 List 保留重复而 Finset 去重，直接替换容器可能改变数量。<br><strong>替换（Rocq → Lean）：</strong><code style="white-space:pre-wrap">seq α → List α；count P s → List.countP P s；filter P s → s.filter P</code>，这里 P : α → Bool；列表求和 → <code style="white-space:pre-wrap">(s.map f).sum</code>。原对象已经是 Finset 时，计数 → <code style="white-space:pre-wrap">(s.filter P).card</code>，求和 → <code style="white-space:pre-wrap">∑ x ∈ s, f x</code>；minn → Nat.min。<br><strong>新增（Lean 适配）：</strong>若 List 的业务条件 q : α → Prop，写 <code style="white-space:pre-wrap">s.countP (fun x =&gt; decide (q x))</code> 并提供 [DecidablePred q]；Finset.filter 使用 Prop 谓词及 [DecidablePred P]。不可为套定理把有重复的 List 去重；业务封装需按 Lean Prosa 当前实际 declaration/API 确认。<br><strong>保留：</strong>“同一数量有多种写法、后续定理因此用不上”的触发条件。</span>

## When to Use
- A branch mixes `\sum_`, `big_filter`, `big_mkcond`, `sum1_count`, `count`, and `Nat.min` or `minn`.
- The current term is an indicator sum such as `if P x then 1 else 0`, but the intended lemma is about `count`.
- The proof is trying to bound how many elements satisfy a predicate and then feed that bound into a strict inequality or a `min` bound.
- The same quantity is being rewritten back and forth as a filtered sequence, a filtered big operator, and a raw count.
- A large model keeps proposing arithmetic or transitivity steps before the counting shape is stable.

<span style="color:red">【Core Rule｜轻改】<br><strong>本节在做什么：</strong>规定先选好一种计数写法，再一步步转到它，最后处理数量上界。<br><strong>改哪里：</strong>Core Rule 中通常采用的四步表示顺序，以及“最后是 count 还是 bigop”的判断。<br><strong>为什么：</strong>Lean 的后续定理可能直接接受指示和或基数，不一定需要先生成所有中间表达式。<br><strong>替换（Rocq → Lean）：</strong>后续定理要求列表计数时固定成 <code style="white-space:pre-wrap">s.countP P</code>；要求有限集合基数时固定成 <code style="white-space:pre-wrap">(s.filter P).card</code>；要求求和时留在原 List/Finset 的 sum。<br><strong>保留：</strong>选定后续定理需要的表示、单向完成必要桥接、最后处理算术；原文四步是通常顺序，Lean 若有直接连接等式，也不必人为添加中间步骤。</span>

## Core Rule
For this proof class, choose one counting normal form and move toward it monotonically.

Do not jump directly from an indicator sum to a `min` inequality or a final arithmetic step. First normalize the branch into one stable representation, usually:

1. indicator sum
2. filtered big operator
3. count
4. arithmetic or `min` bound

If the next theorem is a theorem about `count`, normalize to `count` first. If the next theorem is a theorem about big operators, stay in filtered big-operator form. Do not oscillate between both.

<span style="color:red">【High-Signal Surface Cues｜中改】<br><strong>本节在做什么：</strong>列出目标中常见的符号和引理名，帮助判断是否遇到了同一个数量有多种写法的问题。<br><strong>改哪里：</strong>High-Signal Surface Cues 的引理名/符号清单；保留末段“必须出现同一数量的多种写法”这一限制。<br><strong>为什么：</strong>旧清单匹配的是 MathComp 表面形式，Lean 的同一数学问题会显示另一套声明和表达式。<br><strong>替换（Rocq → Lean）：</strong>big_mkcond → 指示函数求和/Finset.sum_filter；sum1_count → List.countP_eq_length_filter、Finset.sum_boole 或 Finset.card_eq_sum_ones；big_filter → List.filter/Finset.filter；count → List.countP 或过滤集合的 .card；minn → Nat.min。<br><strong>新增（Lean 适配）：</strong>把 Bool.toNat、<code style="white-space:pre-wrap">decide (P x)</code> 和项目现有 sumSeq/sumFiltered 加为辅助信号。已核实 <code style="white-space:pre-wrap">Prosa.Util.Sum.sumSeq s F</code> = (s.map F).sum，<code style="white-space:pre-wrap">Prosa.Util.Sum.sumFiltered s P F</code> = ((s.filter P).map F).sum；使用封装时，过滤常数 1 求和到 countP 可用 <code style="white-space:pre-wrap">simp [Prosa.Util.Sum.sumFiltered, List.countP_eq_length_filter]</code>。<br><strong>保留：</strong>局部业务名称只作语义线索；不能看到任意 filter 就启动。</span>

## High-Signal Surface Cues
This skill is likely the right one if the failing branch contains several of these at once:

- `big_mkcond`
- `sum1_count`
- `big_filter`
- `count`
- `filter`
- `Nat.min` or `minn`
- `if P x then 1 else 0`
- local names like `count_exceeding`, `other_tasks`, `rest_tasks`, or similar “count selected elements of a remainder list” helper facts

One cue alone is not enough. The class appears when the same quantity is drifting across these different shapes.

<a id="lean-review-normal-form"></a>

## Normal-Form Decision
Before rewriting, answer this first:

- Is the endgame a count theorem, a cardinality theorem, or an arithmetic inequality about how many elements satisfy a predicate?
- Or is the endgame still a big-operator identity?

If the endgame is about how many elements satisfy a predicate, prefer this target normal form:

<span style="color:red">【Normal-Form Decision｜中改】<br><strong>本节在做什么：</strong>帮助决定接下来把表达式整理成“有多少个”还是“把这些项加起来”。<br><strong>改哪里：</strong>下方 count P s 这一目标范式。<br><strong>为什么：</strong>Lean 中 List 计数使用 Bool 谓词；Finset 过滤基数使用可判定的 Prop 谓词，且两者对重复项的含义不同。<br><strong>替换（Rocq → Lean）：</strong><code style="white-space:pre-wrap">count P s → s.countP P</code>，其中 s : List α、P : α → Bool；若原对象已是 Finset，改成 <code style="white-space:pre-wrap">(s.filter P).card</code>。<br><strong>新增（Lean 适配）：</strong>列表条件若是 q : α → Prop，使用 <code style="white-space:pre-wrap">s.countP (fun x =&gt; decide (q x))</code> 并提供 [DecidablePred q]。先记录容器和谓词类型，不能通过去重改变原计数；项目封装需按实际 Lean Prosa 声明确认。</span>

```text
count P s
```

If the endgame is still a summation theorem, prefer this target normal form:

<span style="color:red">【Normal-Form Decision｜中改】<br><strong>改哪里：</strong>下方过滤常数 1 求和的 MathComp bigop 写法。<br><strong>为什么：</strong>Lean 的求和记号与容器接口不同；保持原序列的重复项和自然数求和值是等价迁移的前提。<br><strong>替换（Rocq → Lean）：</strong>List 路线：<code style="white-space:pre-wrap">((s.filter P).map (fun _ =&gt; (1 : Nat))).sum</code>；Finset 路线：<code style="white-space:pre-wrap">∑ x ∈ s.filter P, (1 : Nat)</code>。已核实 <code style="white-space:pre-wrap">Prosa.Util.Sum.sumSeq s F</code> = (s.map F).sum，<code style="white-space:pre-wrap">Prosa.Util.Sum.sumFiltered s P F</code> = ((s.filter P).map F).sum；使用封装时，过滤常数 1 求和到 countP 可用 <code style="white-space:pre-wrap">simp [Prosa.Util.Sum.sumFiltered, List.countP_eq_length_filter]</code>。<br><strong>新增（Lean 适配）：</strong>Finset 求和前启用 <code style="white-space:pre-wrap">open scoped BigOperators</code>；List 的 P : α → Bool，Finset 的 P : α → Prop 并需 [DecidablePred P]。</span>

```text
\sum_(x <- s | P x) 1
```

Once chosen, keep the whole branch moving toward that form only.

<span style="color:red">【Required Procedure｜中改】<br><strong>本节在做什么：</strong>给出从查看当前写法、连接不同表达式到证明最终上界的操作顺序。<br><strong>改哪里：</strong>Required Procedure 的步骤 3/4 引理、步骤 5 上界、步骤 6 Bool 边界、步骤 7 局部事实语法。<br><strong>为什么：</strong>步骤的数学作用仍相同，但 MathComp 引理和 SSReflect have 语法不能直接执行；普通 Lean Nat 比较也无需 reflection。<br><strong>替换（Rocq → Lean）：</strong>步骤 3：Finset 用 <code style="white-space:pre-wrap">rw [Finset.sum_filter]</code>，List 用归纳并按 P x 分情况。步骤 4：Finset 常数 1 求和用 simp，List 用 <code style="white-space:pre-wrap">simp [List.countP_eq_length_filter]</code>。步骤 5：列表拆分/上界用 List.countP_append、List.countP_le_length，集合包含界用 Finset.card_le_card。步骤 6 的自然数算术用 omega。步骤 7：have -> → <code style="white-space:pre-wrap">have h : 左侧 = 右侧 := by&#10;  完成局部证明</code> 后 <code style="white-space:pre-wrap">rw [h]</code>，这里中文是证明占位说明。<br><strong>删除（仅未来 Lean 版）：</strong>当输入和目标都为 Prop 时，删除步骤 6 的 Bool → Prop → Bool 往返要求。<br><strong>新增（Lean 适配）：</strong>在步骤 6 前检查真实类型；只有 decide 包装或业务 Bool 定义才按下文桥接。<br><strong>保留：</strong>先确认当前表示，再选择目标表示并建立必要连接的顺序。</span>

<a id="lean-review-procedure"></a>

## Required Procedure
1. Freeze the branch and name the current shape.
   - indicator sum
   - filtered big operator
   - count
   - `min` or arithmetic layer
2. Decide the target normal form.
   - If the next useful fact is about `count`, normalize toward `count`.
   - If the next useful fact is about big operators, normalize toward filtered big operators.
3. If the branch still contains `if P x then 1 else 0`, remove the indicator encoding first.
   - Use `big_mkcond` or an equivalent bridge step to expose the predicate as a filter condition.
4. If the branch is now a filtered sum of ones, collapse it to a count.
   - Use `sum1_count` or an equivalent local bridge fact.
5. Only after the count shape is stable should you apply list-splitting, subset, or `min` lemmas.
6. Only after the count bound is stable should you perform the final arithmetic step.
   - Keep boolean comparisons and Prop arithmetic separate until you explicitly bridge them.
7. If the branch needs a local connector fact, name it and keep it local.
   - Prefer a named connector fact over a brittle inline `have ->` chain.

<span style="color:red">【Canonical Bridge Order｜中改】<br><strong>本节在做什么：</strong>展示通常怎样从逐项记 0 或 1 的求和，走到计数，再走到数量上界。<br><strong>改哪里：</strong>Canonical Bridge Order 的流程图节点和箭头。<br><strong>为什么：</strong>MathComp 的 bigop/count 写法要更换；Lean 已有直接的指示和—基数等式时，中间的过滤和节点可省。<br><strong>替换（Rocq → Lean）：</strong>List 路线 → <code style="white-space:pre-wrap">(s.map (fun x =&gt; if P x then (1 : Nat) else 0)).sum → s.countP P → 计数界 → Nat.min 界</code>；Finset 路线 → <code style="white-space:pre-wrap">(∑ x ∈ s, if P x then (1 : Nat) else 0) → (s.filter P).card → 计数界</code>，后一条可使用 Finset.sum_boole。<br><strong>保留：</strong>“下一定理需要另一表示时必须有连接”等式要求；有直接连接定理时，图中允许省略过滤和节点。<br><strong>新增（Lean 适配）：</strong>List 条件明确为 Bool，Finset 条件明确为可判定 Prop，指示函数结果标注 (1 : Nat)。</span>

<a id="lean-review-bridge-order"></a>

## Canonical Bridge Order
Preferred bridge sequence:

```text
\sum_(x <- s) (if P x then 1 else 0)
  ->
\sum_(x <- s | P x) 1
  ->
count P s
  ->
bound on count P s
  ->
bound on Nat.min / minn / final arithmetic expression
```

The hard rule is: do not skip a bridge when the next lemma lives in a different layer.

<span style="color:red">【Bridge Templates】<br><strong>本节在做什么：</strong>提供几种常见转换的证明框架，说明每一步需要先建立什么等式或上界。</span>

## Bridge Templates

<a id="lean-review-template-1"></a>

### Template 1: Indicator Sum To Filtered Big Operator
Use this when the branch still hides the predicate in `if ... then 1 else 0`.

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把列表中每个对象变成一个数：满足条件记 1，不满足记 0。这里要证明，把这些数相加，等于先挑出满足条件的对象，再给每个对象加一次 1。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>Template 1 的 have/Proof./Qed. 结构、big_mkcond 及两个求和表达式。<br><strong>为什么：</strong>Lean 使用 have ... := by，求和等式按 List/Finset 接口证明；换容器前要保持重复项语义。<br><strong>替换（Rocq → Lean）：</strong>Finset 版本可写：<code style="white-space:pre-wrap">have hIndicator : (∑ x ∈ s, if P x then (1 : Nat) else 0) =&#10;    ∑ x ∈ s.filter P, (1 : Nat) := by&#10;  rw [Finset.sum_filter]</code>。List 版本比较两个 map/sum，证明体用 <code style="white-space:pre-wrap">induction s with&#10;| nil =&gt; simp&#10;| cons x xs ih =&gt; cases hx : P x &lt;;&gt; simp [hx, ih]</code>。使用前声明集合/列表类型以及谓词类型。</span>

```coq
have H_indicator_filter :
  \sum_(x <- s) (if P x then 1 else 0) = \sum_(x <- s | P x) 1.
(* Prove this local fact immediately with big_mkcond or the equivalent
   branch-local rewrite; do not leave a placeholder proof. *)
```

<a id="lean-review-template-2"></a>

### Template 2: Filtered Ones Sum To Count
Use this when the branch is already a filtered sum of ones.

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把“挑出符合条件的对象，每个加一次 1”改写成“符合条件的对象有多少个”，让后面的计数定理能够直接使用。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>Template 2 的 sum1_count 证明及过滤和/计数两端。<br><strong>为什么：</strong>Lean 的列表计数和集合基数由不同接口提供，不能把保留重复的序列直接当成集合。<br><strong>替换（Rocq → Lean）：</strong>所选表示必须保留原序列中重复元素的计数方式，以及求和值的类型。List 版本：<code style="white-space:pre-wrap">have hCount : ((s.filter P).map (fun _ =&gt; (1 : Nat))).sum = s.countP P := by&#10;  simp [List.countP_eq_length_filter]</code>。Finset 版本：<code style="white-space:pre-wrap">have hCount : (∑ x ∈ s.filter P, (1 : Nat)) = (s.filter P).card := by&#10;  simp</code>。若直接连接指示和与基数，使用 <code style="white-space:pre-wrap">simpa using (Finset.sum_boole (R := Nat) P s)</code>；相关声明由 Mathlib.Algebra.BigOperators.Ring.Finset 提供。<br>另已核实 Lean Prosa 现有 <code style="white-space:pre-wrap">Prosa.Util.Sum.sumSeq s F</code> 等于 (s.map F).sum，<code style="white-space:pre-wrap">Prosa.Util.Sum.sumFiltered s P F</code> 等于 ((s.filter P).map F).sum；可保留这些封装，以 <code style="white-space:pre-wrap">simp [Prosa.Util.Sum.sumFiltered, List.countP_eq_length_filter]</code> 证明过滤常数 1 求和等于 countP。</span>

```coq
have H_filter_count :
  \sum_(x <- s | P x) 1 = count P s.
(* Prove this local fact immediately with sum1_count or a branch-local variant;
   do not leave a placeholder proof. *)
```

<a id="lean-review-template-3"></a>

### Template 3: Count Bound Before Min Bound
Use this when the final statement mentions `Nat.min` or `minn`.

<span style="color:red"><strong>1）这段代码在干嘛：</strong>先证明符合条件的对象不超过 k 个，再利用这个上界，证明包含 min 的表达式也不会超过相应的界。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>Template 3 的两个局部证明：先得到计数上界，再把上界传给 min。<br><strong>为什么：</strong>Lean 局部事实语法不同；min 上界使用实际序关系引理，计数界本身仍取决于原数学论证。<br><strong>替换（Rocq → Lean）：</strong>原 have ... Proof./Qed. → have ... := by。先沿用业务论证得到 <code style="white-space:pre-wrap">hCount : s.countP P ≤ k</code>；第二段换成 <code style="white-space:pre-wrap">have hMin : Nat.min m (s.countP P) ≤ Nat.min m k := by&#10;  exact min_le_min_left m hCount</code>。min_le_min_left 是 Mathlib 通用引理，不是 Nat.min_le_min_left。<br><strong>保留：</strong>原来证明计数不超过 k 的数学理由，不能用占位代码代替。</span>

```coq
have Hcount_bound : count P s <= k.
Proof.
  ...
Qed.

have Hmin_bound : Nat.min m (count P s) <= Nat.min m k.
Proof.
  ...
Qed.
```

Do not try to prove the `Nat.min` statement while the branch is still in indicator-sum form.

<span style="color:red">【Local Connector Fact Policy｜轻改】<br><strong>本节在做什么：</strong>要求把不同写法之间的等式单独命名，方便后面的步骤明确引用。<br><strong>改哪里：</strong>Local Connector Fact Policy 的局部引理声明和调用写法。<br><strong>为什么：</strong>局部连接等式的作用不变，只有 SSReflect 声明/改写语法要换。这里的 local 指证明作用域，不是 session ownership 或 checkpoint。<br><strong>替换（Rocq → Lean）：</strong>H_indicator_filter/H_filter_count 等名称可保留；声明写成 <code style="white-space:pre-wrap">have H_filter_count : 左侧 = 右侧 := by&#10;  完成局部等式证明</code>，再 <code style="white-space:pre-wrap">rw [H_filter_count]</code>；中文部分是待完成证明的说明。<br><strong>保留：</strong>为转换命名、检查方向、只改目标中需要的位置；无需新增 transaction 等协议。</span>

## Local Connector Fact Policy
For this proof class, local connector facts are usually better than long inline rewrites.

Preferred names:

- `H_indicator_filter`
- `H_filter_count`
- `Hcount_rest_tasks`
- `Hcount_exceeding_bound`
- `Hmin_count_bound`

Avoid a long script that repeatedly changes representation without naming the bridge.

<span style="color:red">【Bool / Prop Separation｜重改｜需重新定位子模块】<br><strong>本节在做什么：</strong>说明计数完成后，怎样把布尔比较转换成算术证明能够使用的逻辑命题。<br><strong>改哪里：</strong>Bool / Prop Separation 的触发条件、成功标准及下文协议/模板的默认往返要求。<br><strong>为什么：</strong>MathComp 普通自然数比较通常是 Bool；Lean 普通 Nat 的 &lt;、≤ 是 Prop。这个子模块需要重新定位，计数与求和的核心转换仍然有效。<br><strong>替换（Rocq → Lean）：</strong>把统一往返流程改成三类入口：① 普通 Nat 比较直接用于算术；② <code style="white-space:pre-wrap">h : decide (a &lt; b) = true</code> 用 <code style="white-space:pre-wrap">have hlt : a &lt; b := of_decide_eq_true h</code>；③ 业务 Bool 先 unfold/simp 实际定义，确认对应命题再桥接。输出为 decide (...) = true 时才用 <code style="white-space:pre-wrap">exact decide_eq_true hlt</code>。<br><strong>删除（仅未来 Lean 版）：</strong>普通 Prop 不等式上的 ltP/leP 和 Bool → Prop → Bool 固定往返。<br><strong>新增（Lean 适配）：</strong>明确纯 b : Bool 在没有定义对应关系时只能保留 b = true，不能凭空提取算术命题。本地 pending/completed 仍是 Bool，不能把该子模块整体删除。<br><strong>保留：</strong>完成必要转换后保持算术表示稳定。</span>

<a id="lean-review-bool-prop"></a>

## Bool / Prop Separation
These branches often have a second failure mode after the counting shape is already stable. The branch is no longer stuck on `big_mkcond` or `sum1_count`, but it still fails because it keeps switching between:

- boolean comparison and ssreflect reflection
- Prop-level arithmetic needed for `lia`, `Nat.min`, or the final strict inequality

This section covers only the count-branch version of that problem. Use it when the branch is already about `count`, `Nat.min` or `minn`, or a final arithmetic inequality derived from a count bound. If the branch is still drifting between indicator sum, filtered big operator, and count, finish that normalization first.

<span style="color:red">【Problem Shape｜重改｜需重写执行内容】<br><strong>本节在做什么：</strong>用一个常见失败过程说明，为什么计数已经做完，最后的不等式仍可能卡住。<br><strong>改哪里：</strong>Problem Shape 的四步失败例及 ltnW/ltnNge/%coq_nat 等说明。<br><strong>为什么：</strong>旧例假定自然数比较先处于 MathComp Bool 层；Lean 中卡点应由实际假设类型判断。<br><strong>替换（Rocq → Lean）：</strong>失败例改为：若 <code style="white-space:pre-wrap">h : decide (s.countP P &lt; k) = true</code>，先 <code style="white-space:pre-wrap">have hlt := of_decide_eq_true h</code> 再 omega；若 h 已是 <code style="white-space:pre-wrap">s.countP P &lt; k</code>，直接用于算术。<br><strong>删除（仅未来 Lean 版）：</strong>“普通比较默认是 bool”的判断和 %coq_nat scope 切换。<br><strong>新增（Lean 适配）：</strong>在例子中展示假设的实际类型；业务 Bool 或 Nat/Int 不一致时先展开定义/核对转换，不把一切失败归因于缺少 reflection。</span>

<a id="lean-review-problem-shape"></a>

### Problem Shape
Typical sequence:

1. The proof establishes a boolean fact such as `count P s < k`, `count P s <= k`, or `0 < x`.
2. The next step needs Prop arithmetic, a `Nat.min` side condition, or a contradiction argument.
3. The script bounces among `ltnW`, `ltnNge`, `move/ltP`, `move/leP`, `%coq_nat`, and `lia` without committing to one layer.
4. The final arithmetic step fails even though the count argument is already essentially done.

The root cause is not that one specific lemma is missing. The branch crossed the bool/Prop boundary without deciding which layer should own the rest of the proof.

<span style="color:red">【Boundary Rule｜中改】<br><strong>本节在做什么：</strong>规定什么时候把布尔条件交给命题层处理，以及何时才需要转回布尔结果。<br><strong>改哪里：</strong>Boundary Rule 的 bool/Prop 二选一和“进入算术前转一次”的强制规则。<br><strong>为什么：</strong>Lean 普通不等式已经能用于算术和 Nat.min 侧条件，不需要人为建立另一层。<br><strong>替换（Rocq → Lean）：</strong>lia → 适用的 omega；Nat.min 侧条件使用 Nat.min_eq_left/right 所要求方向的 ≤。实际输入为 decide (a ≤ b) = true 时用 of_decide_eq_true，输出仍带 decide 时才用 decide_eq_true。<br><strong>删除（仅未来 Lean 版）：</strong>对 h : a ≤ b 等普通 Prop 假设强制 reflection 的步骤。<br><strong>新增（Lean 适配）：</strong>入口先检查真实类型；业务 Bool 先确认定义到命题的对应关系。<br><strong>保留：</strong>真正跨层后保持稳定，不来回转换。</span>

### Boundary Rule
Once the branch has a stable `count` or `Nat.min` expression, decide whether the rest of the branch should finish in:

- ssreflect boolean comparison form
- Prop arithmetic form

If the remaining work is final arithmetic, `Nat.min` side conditions, or `lia`, move to Prop exactly once and stay there until that subproof closes. Do not alternate between boolean reflection and Prop arithmetic after the handoff.

<span style="color:red">【Layer Map｜基本重写】<br><strong>本节在做什么：</strong>并排列出布尔比较和普通命题的典型写法，帮助识别当前事实属于哪一类。<br><strong>改哪里：</strong>Layer Map 整张 bool/Prop 分类表及表后的 ltnW 建议。<br><strong>为什么：</strong>Lean 的同样符号 &lt;、≤ 通常属于 Prop；%coq_nat 不是 Lean scope，所以旧分类依据失效。<br><strong>替换（Rocq → Lean）：</strong>新表列三行：① Bool 值 b；② 命题 b = true，其中 b = decide P 时可用 of_decide_eq_true 提取 P；③ 普通命题 a &lt; b、a ≤ b、a = b。ltnW → Nat.le_of_lt；本节 lia 算术 → omega；min 侧条件 → Nat.min_eq_left/right。<br><strong>删除（仅未来 Lean 版）：</strong>%coq_nat 语法，以及“ltnW 必须在 Bool 层交接前使用”的固定位置要求。</span>

<a id="lean-review-layer-map"></a>

### Layer Map
Use this rough split.

- bool layer
  - `count P s < k`
  - `count P s <= k`
  - `ltnW`
  - `ltnNge`
  - boolean rewriting and reflection views
- Prop layer
  - `(count P s < k)%coq_nat`
  - `(count P s <= k)%coq_nat`
  - `lia`
  - `have -> : Nat.min a b = ... by lia`
  - contradictions and transitivity using ordinary `<`, `<=`, or `=` hypotheses

`ltnW` is usually a bool-side preparation step. Use it before the Prop handoff if you need a non-strict boolean fact.

<span style="color:red">【One-Way Handoff Protocol｜重改｜需重写执行内容】<br><strong>本节在做什么：</strong>给出整理计数、转换必要的布尔条件、完成算术并提交结果的具体顺序。<br><strong>改哪里：</strong>One-Way Handoff Protocol 的步骤 2/3 类型入口、步骤 4 tactic、步骤 5 返回动作。<br><strong>为什么：</strong>Lean 普通比较不经过 reflection，只有实际带 Bool 包装的输入/输出才需要跨层。<br><strong>替换（Rocq → Lean）：</strong>输入确为 decide (...) = true 时，步骤 3 的 move/ltP → <code style="white-space:pre-wrap">have hlt : a &lt; b := of_decide_eq_true hBool</code>，move/leP 同理改为 ≤；步骤 4 的 lia → omega；步骤 5 的 apply/ltP、apply/leP → <code style="white-space:pre-wrap">exact decide_eq_true hProp</code>。<br><strong>删除（仅未来 Lean 版）：</strong>输入/目标已是 Prop 时的步骤 3/5；步骤 2 不再默认 count 的比较属于 Bool。<br><strong>新增（Lean 适配）：</strong>步骤 2 记录输入类型；业务 Bool 先按实际定义建立对应命题，Nat.min 改写前仍需相应 ≤ 侧条件。<br><strong>保留：</strong>先稳定计数表示，再完成算术。</span>

<a id="lean-review-handoff"></a>

### One-Way Handoff Protocol
1. Finish count normalization first.
   - The branch should already be in `count`, plain nat arithmetic, or `Nat.min` form.
2. Isolate the last boolean fact you need.
   - Typical examples: `Hcount_lt : count P s < k`, `Hcount_le : count P s <= k`, `Hpos : 0 < x`.
3. Convert that fact into Prop exactly once.
   - `move/ltP: Hcount_lt => Hcount_lt_prop.`
   - `move/leP: Hcount_le => Hcount_le_prop.`
4. Finish the remaining arithmetic entirely in Prop.
   - Use `lia`.
   - Rewrite `Nat.min` only after the side condition is already a Prop inequality.
5. Reflect back only if the final goal itself is a boolean comparison.
   - `apply/ltP. exact Hgoal_prop.`
   - `apply/leP. exact Hgoal_prop.`

<span style="color:red">【Common Local Bridges｜基本重写】<br><strong>本节在做什么：</strong>列出几种小步骤，用来转换比较形式或把严格上界变成非严格上界。<br><strong>改哪里：</strong>Common Local Bridges 三组行内 tactic 示例。<br><strong>为什么：</strong>exact:、move/view、apply/view 是 SSReflect 机制；Lean 使用局部事实和具体 Bool/Prop 对应定理。<br><strong>替换（Rocq → Lean）：</strong>严格界转非严格界 → <code style="white-space:pre-wrap">have hle : a ≤ b := Nat.le_of_lt hlt</code>；hb : decide P = true 时，move/view → <code style="white-space:pre-wrap">have hp : P := of_decide_eq_true hb</code>；最终 decide P = true 目标的 apply/view → <code style="white-space:pre-wrap">exact decide_eq_true hp</code>。<br><strong>删除（仅未来 Lean 版）：</strong>普通 Prop 比较上多余的 Bool 往返。<br><strong>新增（Lean 适配）：</strong>若实际假设是 Bool 合取为 true，先 <code style="white-space:pre-wrap">simp only [Bool.and_eq_true] at h</code>，再 <code style="white-space:pre-wrap">rcases h with ⟨h1, h2⟩</code>；这条只用于真正 Bool 合取。<br><strong>保留：</strong>桥接只在需要时执行，不变成循环改写。</span>

<a id="lean-review-local-bridges"></a>

### Common Local Bridges
Use small local connectors rather than bouncing back and forth across the boundary.

- strict to non-strict on the bool side
  - `have Hle_bool : a <= b by exact: ltnW Hlt_bool.`
- bool to Prop
  - `move/ltP: Hlt_bool => Hlt_prop.`
  - `move/leP: Hle_bool => Hle_prop.`
- Prop back to a final bool goal
  - `apply/ltP. exact Hlt_prop.`
  - `apply/leP. exact Hle_prop.`

Do not use these bridges as an open-ended rewrite loop. Use them once to transfer ownership of the branch.

<a id="lean-review-template-4"></a>

### Template 4: Count Bound To Prop Arithmetic
Use this when the count bound is done and only arithmetic remains.

<span style="color:red"><strong>1）这段代码在干嘛：</strong>先得到计数小于 k，再推出它小于 k + 1。原代码为使用算术工具，先把布尔比较转成命题，算完后又转回布尔比较。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>Template 4 从 Hcount_lt 到 Hcount_lt_prop、算术 Hgoal、再 apply/ltP 的整段流程。<br><strong>为什么：</strong>Lean 普通 Nat 比较已是 Prop，复制两个反射方向会制造不必要的中间事实。<br><strong>替换（Rocq → Lean）：</strong>已有普通计数界时，后续算术改为 <code style="white-space:pre-wrap">have hGoal : s.countP P &lt; k + 1 := by&#10;  omega</code>。<br><strong>删除（仅未来 Lean 版）：</strong>普通不等式的 Hcount_lt_prop 中转证明和最后 apply/ltP。<br><strong>新增（Lean 适配）：</strong>只有输入是 <code style="white-space:pre-wrap">hBool : decide (s.countP P &lt; k) = true</code> 时，先 <code style="white-space:pre-wrap">have hCount : s.countP P &lt; k := of_decide_eq_true hBool</code>；只有目标仍带 decide 时，最后 <code style="white-space:pre-wrap">exact decide_eq_true hGoal</code>。</span>

```coq
have Hcount_lt : count P s < k.
Proof.
  ...
Qed.

have Hcount_lt_prop : (count P s < k)%coq_nat.
Proof.
  by move/ltP: Hcount_lt.
Qed.

have Hgoal_prop : (count P s < k + 1)%coq_nat.
Proof.
  lia.
Qed.

have Hgoal : count P s < k + 1.
Proof.
  apply/ltP.
  exact Hgoal_prop.
Qed.
```

<a id="lean-review-template-5"></a>

### Template 5: Prop Side Condition For Nat.min
Use this when the count bound is already known, but `Nat.min` needs a Prop side condition.

<span style="color:red"><strong>1）这段代码在干嘛：</strong>利用“计数不超过 k”这个事实，把“计数和 k 中较小的那个数”直接改写成计数本身。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>Template 5 中 leP 侧条件转换及 have -> ... by lia。<br><strong>为什么：</strong>Lean 的 ≤ 已是 Prop；min 化简可以直接使用带条件的等式。<br><strong>替换（Rocq → Lean）：</strong>已有 <code style="white-space:pre-wrap">hCount : s.countP P ≤ k</code> 后，用 <code style="white-space:pre-wrap">have hMin : Nat.min (s.countP P) k = s.countP P := Nat.min_eq_left hCount&#10;rw [hMin]</code> 代替匿名 have -> 和 lia。<br><strong>删除（仅未来 Lean 版）：</strong>hCount 已是普通不等式时的 leP 转换。<br><strong>新增（Lean 适配）：</strong>只有 hCount 是 decide (...) = true 时，才先用 of_decide_eq_true 提取 ≤。</span>

```coq
have Hcount_le : count P s <= k.
Proof.
  ...
Qed.

have Hcount_le_prop : (count P s <= k)%coq_nat.
Proof.
  by move/leP: Hcount_le.
Qed.

have -> : Nat.min (count P s) k = count P s by lia.
```

<span style="color:red">【Template 5: Prop Side Condition For Nat.min｜中改】<br><strong>改哪里：</strong>模板后面 PeanoNat.Nat.min_l/min_r 的引理提示。<br><strong>为什么：</strong>两条是 Coq 声明，Lean 名称和侧条件方向需按实际声明重写。<br><strong>替换（Rocq → Lean）：</strong>PeanoNat.Nat.min_l → <code style="white-space:pre-wrap">Nat.min_eq_left h</code>，h : a ≤ b；PeanoNat.Nat.min_r → <code style="white-space:pre-wrap">Nat.min_eq_right h</code>，h : b ≤ a。调用可写 <code style="white-space:pre-wrap">rw [Nat.min_eq_left h]</code> 或右侧对应形式。<br><strong>保留：</strong>先具备正确方向的侧条件，再化简 min。</span>

If you prefer `PeanoNat.Nat.min_l` or `PeanoNat.Nat.min_r`, discharge the side condition only after it is already in Prop form.

<a id="lean-review-contradiction"></a>

### Contradiction Pattern With `ltnNge`
Use `ltnNge` as a boundary-specific contradiction tool, not as a general rewrite strategy.

<span style="color:red"><strong>1）这段代码在干嘛：</strong>用反证法证明 a 小于 b：先假设 b 不超过 a，再用已有的数值界推出矛盾。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>反证模板中的 ltnNge、negP/leP 和最后的自然数算术。<br><strong>为什么：</strong>Lean 直接对 Prop 的 a &lt; b 反证，不使用 MathComp 的 Bool 否定视图。<br><strong>替换（Rocq → Lean）：</strong>Prop 目标改为 <code style="white-space:pre-wrap">by_contra hNot&#10;have hge : b ≤ a := Nat.le_of_not_gt hNot&#10;omega</code>；omega 要求上下文确实有能导出矛盾的界，这不是脱离上下文的完整证明。<br><strong>删除（仅未来 Lean 版）：</strong>ltnNge 改写及 negP/leP 的 Bool 反射步骤。<br><strong>新增（Lean 适配）：</strong>只有目标为 decide (a &lt; b) = true 时，先 <code style="white-space:pre-wrap">apply decide_eq_true</code>，再执行上述反证。</span>

```coq
rewrite ltnNge.
apply/negP => /leP Hge_prop.
lia.
```

This is appropriate when the goal is a boolean strict inequality and the contradiction should finish in Prop arithmetic.

<span style="color:red">【Boundary Failure Signs｜中改】<br><strong>本节在做什么：</strong>列出几种症状，帮助判断最后的算术是否仍卡在布尔条件的转换上。<br><strong>改哪里：</strong>Boundary Failure Signs 中按 lia、ltn/leq/reflection 识别故障的症状清单。<br><strong>为什么：</strong>迁移后普通比较不再是 Bool；Lean 失败可能来自未展开业务 Bool、数值类型不一致或未整理的计数表达式。<br><strong>替换（Rocq → Lean）：</strong>旧症状 → 核对真实类型的检查项：omega 前 trace_state；含 decide 的假设用 of_decide_eq_true；封装业务 Bool 用 <code style="white-space:pre-wrap">simp [实际定义] at h</code> 后再检查；Nat/Int 不一致先明确转换，再判断 exact_mod_cast 是否适用。实际定义须替换为项目声明。<br><strong>删除（仅未来 Lean 版）：</strong>按 ltn/leq 名称直接判为 Bool 故障的规则。<br><strong>保留：</strong>日志记录真实假设和当前表示；检查类型和数值域是通用调试方法，只需在 Lean 中执行。</span>

### Boundary Failure Signs
The boundary was crossed at the wrong time if:

- `lia` sees no usable arithmetic hypotheses because all comparisons are still boolean facts.
- `Nat.min` or `minn` side conditions do not discharge because the branch still only has `ltn` or `leq` facts.
- the script proves a Prop inequality, immediately reflects it back to bool, then needs to move back to Prop again.
- the count argument is complete, but the strict inequality still fails because the branch never committed to one final layer.

<span style="color:red">【Failure Signatures For This Skill｜重改｜需重写执行内容】<br><strong>本节在做什么：</strong>把计数转换中的常见报错对应到需要检查的表达式和缺失步骤。<br><strong>改哪里：</strong>Failure Signatures For This Skill 中每条 Coq 报错与 big_mkcond/sum1_count 修复动作。<br><strong>为什么：</strong>Lean 不报告这些 Coq/SSReflect 字符串，中间求和形式也不同；直接保留旧表会误导下一步。<br><strong>替换（Rocq → Lean）：</strong>改写匹配失败 → trace_state 后核对改写式/位置；类型不匹配 → 比较 expected/actual；未知名称 → #check 全限定名并核对 import；实例合成失败 → #synth 实例类型；未解决目标 → 检查剩余目标。big_mkcond 行 → 检查 Finset.sum_filter 方向；sum1_count 行 → 检查 List.countP_eq_length_filter 或过滤和目标。<br><strong>删除（仅未来 Lean 版）：</strong>旧 Coq 字符串作为 Lean 触发条件的规则；本文件并没有 coq_session/petanque/snapshot 调用，无需杜撰工具替换。<br><strong>新增（Lean 适配）：</strong>用目标 Lean 版本实际 diagnostics 和 proof state 填新条目并验证修复动作，未观察到的错误不能写成既有案例。<br><strong>保留：</strong>错误 → 当前表示/缺失连接 → 下一步的框架。</span>

<a id="lean-review-failure-signatures"></a>

## Failure Signatures For This Skill
- `The LHS of big_mkcond ... does not match any subterm`
  The branch is not yet in the expected indicator-sum head form.
- `The LHS of sum1_count ... does not match any subterm`
  The branch is not yet a filtered sum of ones.
- `Unable to unify ... count ... with ... \sum_ ...`
  The count bridge has not been established yet.
- `No applicable tactic` after several bigop rewrites in a count argument
  The proof is drifting across indicator, filter, and count forms without a stable target.
- A strict inequality fails after a count argument “should already be done”
  The arithmetic step is too early; the count layer or the bool-to-Prop bridge is not finished.

<span style="color:red">【Anti-Patterns｜中改】<br><strong>本节在做什么：</strong>列出会让计数证明反复绕路的做法，提醒先完成必要的表示转换。<br><strong>改哪里：</strong>Anti-Patterns 中关于 minn、lia、ltn/leq、ltnW 和 reflection 的条目。<br><strong>为什么：</strong>这些限制原来针对 MathComp 表示；Lean 普通 Prop 不等式不应被当作待反射的 Bool。<br><strong>替换（Rocq → Lean）：</strong>“lia 面对 ltn/leq” → “omega 前确认是否仍有 decide/业务 Bool 包装”；“在 Prop 用 ltnW” → “自然数严格界转非严格界用 Nat.le_of_lt”；minn → Nat.min，化简前准备 Nat.min_eq_left/right 所需方向的 ≤。<br><strong>删除（仅未来 Lean 版）：</strong>把普通 &lt;、≤ 当作 Bool 的诊断，以及对它们强制转换的规则。<br><strong>保留：</strong>稳定表示、命名局部事实、真实 Bool 条件需要时仍做桥接。</span>

<a id="lean-review-anti-patterns"></a>

## Anti-Patterns
- Do not feed an indicator sum directly to a count lemma.
- Do not apply `Nat.min` or `minn` lemmas before the raw count expression is stable.
- Do not bounce between filtered sequence form and count form without naming the connector fact.
- Do not start the final strict inequality proof while the branch still contains `if ... then 1 else 0`.
- Do not call `lia` while the main inequalities still only exist as `ltn` or `leq` facts.
- Do not reflect back to bool in the middle of a Prop arithmetic subproof.
- Do not use `ltnW` after the branch has already moved into Prop unless you are deliberately rebuilding a final bool goal.
- Do not rewrite `Nat.min` or `minn` while the only available side condition is still in boolean form.
- Do not encode theorem-local names such as `Hsum_slack` or `Hsum_succ` into the skill. Keep the skill at the proof-pattern level.
- Do not use this skill for focus drift or early-bound theorem application failures. Those are different problem classes.

<span style="color:red">【Minimal Debug Log｜轻改】<br><strong>本节在做什么：</strong>给出一份简短记录表，写清当前计数写法、目标写法和下一步缺少的连接。<br><strong>改哪里：</strong>Minimal Debug Log 的字段内容和计数表示记录。<br><strong>为什么：</strong>记录方法与语言无关；Lean 中 List/Finset 和 Bool/Prop 的选择直接决定接口，不能只记一个 count 名称。<br><strong>替换（Rocq → Lean）：</strong>Next intended lemma 填全限定 Lean 声明；Current shape 从 trace_state 或 Lean LSP 的当前 proof state 获取。<br><strong>新增（Lean 适配）：</strong>在原字段后补 <code style="white-space:pre-wrap">Collection type: List / Finset&#10;Predicate type: Bool / Prop&#10;Actual count expression:&#10;Bool wrapper remaining: yes/no</code>，用于记录这一迁移的实际类型选择；这些是适配字段，并非 Lean 独有的调试方法。<br><strong>保留：</strong>原调试字段；本文件没有 proof_region、guard、transaction、certificate 或 checkpoint 实现，不需要新增此类协议。</span>

## Minimal Debug Log

```text
Current counting shape:
Target normal form:
Next intended lemma:
Does that lemma live in indicator / filtered bigop / count / min-arithmetic layer:
Missing bridge step:
Named local connector fact:
Is the final arithmetic step still premature: yes/no
```

<span style="color:red">【Success Condition】<br><strong>本节在做什么：</strong>说明怎样确认计数表示已经稳定，后续证明可以顺利使用它。</span>

## Success Condition
This skill has worked when the branch stops oscillating between indicator sums, filtered big operators, counts, and `min` bounds, and every subsequent step stays inside one chosen counting normal form until the final arithmetic handoff.
