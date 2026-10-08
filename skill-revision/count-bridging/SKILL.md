<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>你要证明“满足某个条件的对象最多有多少个”，但当前证明把这个数量写成了加法，而手头的定理用的是“对象个数”的写法，直接套用时对不上。这个 skill 帮你把两种写法接起来。<br><strong>具体例子：</strong>假设有 A、B、C、D 四个任务，其中 A、C 没完成，B、D 已完成。计算未完成任务数，可以逐个检查：没完成就记 1，完成就记 0，最后得到 1 + 0 + 1 + 0 = 2；也可以先挑出 A、C，再数出有 2 个任务。两种做法算的是同一个数量，但证明代码里的表达式不同。<br><strong>它会怎么处理：</strong>如果接下来要用的定理讨论“未完成任务有几个”，它就指导你先证明“逐项加起来的结果，等于挑出来的任务个数”，把当前目标换成定理能够使用的写法，再证明这个个数不超过某个限制。如果后续定理仍然讨论求和，就保留求和写法。它的重点是安排这些转换，避免证明一直在几种写法之间来回切换。</span>

<span style="color:red">【Bool / Prop Separation｜首要结构性问题】<a href="#lean-review-bool-prop">点击跳转</a><br><strong>为什么会有结构性问题：</strong>这一部分原本把“计数小于某个数”从布尔判断转成逻辑命题，做完算术后再转回。MathComp 的普通自然数比较采用这种布尔表示；Lean 的普通 &lt;、≤ 本身就是命题，可以直接用于证明，所以这段固定往返流程已没有必要。受影响的是计数之后的交接流程，计数证明的方法仍然适用。<br><strong>Lean 中大致怎么做：</strong>普通不等式直接用于算术证明；只有业务定义确实返回 Bool 时，才处理它与“结果为 true”这个命题的关系。仍然先整理好计数表示，再做最后的算术。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-bool-prop">Bool / Prop Separation</a>；<a href="#lean-review-problem-shape">Problem Shape</a>；<a href="#lean-review-layer-map">Layer Map</a>；<a href="#lean-review-handoff">One-Way Handoff Protocol</a>；<a href="#lean-review-local-bridges">Common Local Bridges</a>；<a href="#lean-review-failure-signatures">Failure Signatures For This Skill</a>。重写 Rocq 执行内容，保留核心证明方法。</span>

<span style="color:red">【Rocq 示例需转为 Lean 代码｜点击跳转】<a href="#lean-review-template-1">Template 1</a>；<a href="#lean-review-template-2">Template 2</a>；<a href="#lean-review-template-3">Template 3</a>；<a href="#lean-review-template-4">Template 4</a>；<a href="#lean-review-template-5">Template 5</a>；<a href="#lean-review-contradiction">Contradiction Pattern With ltnNge</a>。共 6 个 coq 代码块。</span>

<span style="color:red">【行内代码与表示需转换｜点击跳转】<a href="#lean-review-layer-map">Layer Map</a>；<a href="#lean-review-handoff">One-Way Handoff Protocol</a>；<a href="#lean-review-local-bridges">Common Local Bridges</a>；<a href="#lean-review-normal-form">Normal-Form Decision</a>；<a href="#lean-review-bridge-order">Canonical Bridge Order</a>；<a href="#lean-review-procedure">Required Procedure</a>；<a href="#lean-review-anti-patterns">Anti-Patterns</a>。当前仅标注迁移任务，原示例保留。</span>

---
name: ssreflect-count-bridging
#<span style="color:red">【description】建议改为“处理 Lean 4 中指示求和、过滤计数和数量上界之间的表示转换；当 List.countP、List.filter 后的长度、Finset 求和或基数混用，导致改写或上界证明卡住时使用”。理由：用 Lean 的实际表达式识别任务，替换 MathComp 引理触发词。</span>
description: 'Handle ssreflect and MathComp proof branches where the same quantity appears as an indicator sum, a filtered big operator, a count, and then a min-bound or arithmetic inequality. Use when `big_mkcond`, `sum1_count`, `big_filter`, `count`, `Nat.min` or `minn`, or `if ... then 1 else 0` appear together and rewrites keep failing because the branch has no stable counting normal form.'
argument-hint: 'Describe the current indicator or count shape, the target equality or inequality, and the first failed rewrite or bridge step.'
user-invocable: true
---



# Ssreflect Count Bridging <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【帮助把求和、筛选后的数量和计数结果接起来，让后面的数量上界证明能够继续。】</span>



## When to Use <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出哪些计数证明卡住的情况适合使用这份 skill。｜中改】</span>

<span style="color:red"><strong>为什么要改：</strong>① 灰色的求和、big_filter/big_mkcond/sum1_count、count、minn 是 MathComp 的具体记号或接口，不能只靠同名词识别 Lean 任务。<br>② 原序列允许重复；选成去重的 Finset 会改变数量。这是选错容器的风险，不是 Lean 不能保留重复。<br><strong>怎么改：</strong>计数按原语义选 List.countP 或 Finset.filter 后的 card，求和选相应 List/Finset 接口，minn 换 Nat.min。仍只在同一数量混用多种表示时触发。</span>

- A branch mixes <span style="color:gray">`\sum_`, `big_filter`, `big_mkcond`, `sum1_count`, `count`</span>, and `Nat.min` or <span style="color:gray">`minn`</span>.
- The current term is an indicator sum such as `if P x then 1 else 0`, but the intended lemma is about <span style="color:gray">`count`</span>.
- The proof is trying to bound how many elements satisfy a predicate and then feed that bound into a strict inequality or a `min` bound.
- The same quantity is being rewritten back and forth as a filtered sequence, a filtered big operator, and a raw count.
- A large model keeps proposing arithmetic or transitivity steps before the counting shape is stable.



## Core Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【规定先选好一种计数写法，再一步步转到它，最后处理数量上界。｜轻改】</span>
For this proof class, choose one counting normal form and move toward it monotonically.

Do not jump directly from an indicator sum to a `min` inequality or a final arithmetic step. First normalize the branch into one stable representation, usually:

1. indicator sum
2. filtered big operator
3. count
4. arithmetic or `min` bound

<span style="color:red"><strong>为什么要改：</strong>count、bigop 的具体写法需要换库，但“按后续定理选定一种表示”是通用方法，无须重设原则。<br><strong>怎么改：</strong>计数分别用 List.countP 或过滤 Finset 的 .card；后续仍是求和定理就保留 sum。四步是常见顺序，有直接连接等式时不强加中间步骤。</span>

If the next theorem is a theorem about <span style="color:gray">`count`</span>, normalize to <span style="color:gray">`count`</span> first. If the next theorem is a theorem about big operators, stay in filtered big-operator form. Do not oscillate between both.



## High-Signal Surface Cues <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出目标中常见的符号和引理名，帮助判断是否遇到了同一个数量有多种写法的问题。｜中改】</span>
This skill is likely the right one if the failing branch contains several of these at once:

<span style="color:red"><strong>为什么要改：</strong>原清单用 MathComp 引理名识别任务；Lean 的同一计数问题不会自动出现这些名称。<br><strong>怎么改：</strong>big_mkcond/sum1_count 改看指示函数求和、List.countP_eq_length_filter、Finset.sum_filter/sum_boole；big_filter/count/minn 改看 filter、countP/card、Nat.min。Bool.toNat、decide 和项目 sumSeq/sumFiltered 可作辅助信号，单一词出现仍不足以触发。</span>

- <span style="color:gray">`big_mkcond`</span>
- <span style="color:gray">`sum1_count`</span>
- <span style="color:gray">`big_filter`</span>
- <span style="color:gray">`count`</span>
- <span style="color:gray">`filter`</span>
- `Nat.min` or <span style="color:gray">`minn`</span>
- `if P x then 1 else 0`
- local names like `count_exceeding`, `other_tasks`, `rest_tasks`, or similar “count selected elements of a remainder list” helper facts

One cue alone is not enough. The class appears when the same quantity is drifting across these different shapes.

<a id="lean-review-normal-form"></a>



## Normal-Form Decision <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【帮助决定接下来把表达式整理成“有多少个”还是“把这些项加起来”。｜中改】</span>
Before rewriting, answer this first:

- Is the endgame a count theorem, a cardinality theorem, or an arithmetic inequality about how many elements satisfy a predicate?
- Or is the endgame still a big-operator identity?

If the endgame is about how many elements satisfy a predicate, prefer this target normal form:

<span style="color:red"><strong>为什么要改：</strong>下方 count P s 统计序列中满足 Bool 条件的项；Lean 的 Finset.card 统计不重复元素，不能直接当同一个接口。<br><strong>怎么改：</strong>原序列用 <code style="white-space:pre-wrap">s.countP P</code>（P : α → Bool）；现成有限集合用 <code style="white-space:pre-wrap">(s.filter P).card</code>（可判定 Prop 谓词）。列表条件若为 Prop，使用 decide 并提供 DecidablePred；不要去重。</span>

```text
count P s
```

If the endgame is still a summation theorem, prefer this target normal form:

<span style="color:red"><strong>为什么要改：</strong>这条过滤求和使用 MathComp bigop；Lean 必须按原容器表达求和，保留重复项与自然数值类型。<br><strong>怎么改：</strong>List 写 <code style="white-space:pre-wrap">((s.filter P).map (fun _ =&gt; (1 : Nat))).sum</code>；Finset 写 <code style="white-space:pre-wrap">∑ x ∈ s.filter P, (1 : Nat)</code>。前者用 Bool 谓词，后者用可判定 Prop；求和记号需 open scoped BigOperators。</span>

```text
\sum_(x <- s | P x) 1
```

Once chosen, keep the whole branch moving toward that form only.


<a id="lean-review-procedure"></a>


## Required Procedure <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【给出从查看当前写法、连接不同表达式到证明最终上界的操作顺序。｜中改】</span>
1. Freeze the branch and name the current shape.
   - indicator sum
   - filtered big operator
   - count
   - `min` or arithmetic layer
2. Decide the target normal form.

   <span style="color:red"><strong>为什么要改：</strong>这里的 count 是 MathComp 接口；按后续定理选择表示的判断仍适用。<br><strong>怎么改：</strong>列表计数用 List.countP，现成有限集合用过滤后的 card；后续仍做求和就保持相应 sum。</span>

   - If the next useful fact is about <span style="color:gray">`count`</span>, normalize toward <span style="color:gray">`count`</span>.
   - If the next useful fact is about big operators, normalize toward filtered big operators.
3. If the branch still contains `if P x then 1 else 0`, remove the indicator encoding first.

   <span style="color:red"><strong>为什么要改：</strong>big_mkcond 是 MathComp 的桥接引理，Lean 需要同一等式的实际接口。<br><strong>怎么改：</strong>Finset 可用 Finset.sum_filter；List 可用归纳并按谓词值分情况。</span>

   - Use <span style="color:gray">`big_mkcond`</span> or an equivalent bridge step to expose the predicate as a filter condition.
4. If the branch is now a filtered sum of ones, collapse it to a count.

   <span style="color:red"><strong>为什么要改：</strong>sum1_count 的名称和计数表示属于旧库；“过滤后每项加 1 等于项数”的数学事实可保留。<br><strong>怎么改：</strong>列表用 List.countP_eq_length_filter 配合 simp，Finset 常数 1 求和用 simp。后续拆分/上界可查 List.countP_append、List.countP_le_length、Finset.card_le_card。</span>

   - Use <span style="color:gray">`sum1_count`</span> or an equivalent local bridge fact.
5. Only after the count shape is stable should you apply list-splitting, subset, or `min` lemmas.
6. Only after the count bound is stable should you perform the final arithmetic step.
   - Keep boolean comparisons and Prop arithmetic separate until you explicitly bridge them.
7. If the branch needs a local connector fact, name it and keep it local.

   <span style="color:red"><strong>为什么要改：</strong>匿名 have -> 是 SSReflect 写法，Lean 不能直接照搬；为桥接命名的原则不变。<br><strong>怎么改：</strong>用 have hBridge : lhs = rhs := by ... 建立局部等式，再 rw [hBridge]；省略号表示待完成证明。</span>

   - Prefer a named connector fact over a brittle inline <span style="color:gray">`have ->`</span> chain.


<a id="lean-review-bridge-order"></a>


## Canonical Bridge Order <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【展示通常怎样从逐项记 0 或 1 的求和，走到计数，再走到数量上界。｜中改】</span>
Preferred bridge sequence:

<span style="color:red"><strong>为什么要改：</strong>图中的 \sum_、count 和 minn 是旧表示；需要换的是节点写法，不是“先接好等式，再使用数量界”的证明顺序。<br><strong>怎么改：</strong>列表路线改为 map/sum → countP → 上界，有限集合路线改为指示和 → 过滤集合的 card → 上界。Finset.sum_boole 可直接连接后一路线；列表重复项、谓词类型和自然数值仍须保持。</span>

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



## Bridge Templates <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【提供几种常见转换的证明框架，说明每一步需要先建立什么等式或上界。】</span>

<a id="lean-review-template-1"></a>

### Template 1: Indicator Sum To Filtered Big Operator
Use this when the branch still hides the predicate in `if ... then 1 else 0`.

<span style="color:red"><strong>1）这段代码在干嘛：</strong>证明“满足条件记 1，否则记 0”的总和，等于筛选后每项加一次 1。<br><strong>2）怎么换成 Lean 代码：</strong>① 这里需替换的是 MathComp 求和、big_mkcond 及以句点结尾的 have 声明。Lean 可用 have ... := by 证明同一等式。<br>② Finset 版本用 <code style="white-space:pre-wrap">rw [Finset.sum_filter]</code>；保留重复项的 List 版本对列表归纳，再按 P x 分情况并 simp。不能为换库而去重。通用例子使用 import Mathlib、open scoped BigOperators；已核对本地 Lean 4.33.1 / 锁定 Mathlib，完整证明仍需变量声明和业务上下文。</span>

```coq
have H_indicator_filter :
  \sum_(x <- s) (if P x then 1 else 0) = \sum_(x <- s | P x) 1.
(* Prove this local fact immediately with big_mkcond or the equivalent
   branch-local rewrite; do not leave a placeholder proof. *)
```

<a id="lean-review-template-2"></a>

### Template 2: Filtered Ones Sum To Count
Use this when the branch is already a filtered sum of ones.

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把“筛选后每个对象加一次 1”化成“符合条件的对象有多少个”。<br><strong>2）怎么换成 Lean 代码：</strong>sum1_count 不是 Lean 接口；List 计数与 Finset 基数也不能混用。列表等式用 <code style="white-space:pre-wrap">simp [List.countP_eq_length_filter]</code>；过滤 Finset 的常数 1 求和用 simp，指示和可用 <code style="white-space:pre-wrap">simpa using (Finset.sum_boole (R := Nat) P s)</code>。本地 Prosa.Util.Sum.sumSeq/sumFiltered 封装的是列表 map/sum；若用后者，导入 Prosa.Util.Sum 并用 <code style="white-space:pre-wrap">simp [Prosa.Util.Sum.sumFiltered, List.countP_eq_length_filter]</code>。</span>

```coq
have H_filter_count :
  \sum_(x <- s | P x) 1 = count P s.
(* Prove this local fact immediately with sum1_count or a branch-local variant;
   do not leave a placeholder proof. *)
```

<a id="lean-review-template-3"></a>

### Template 3: Count Bound Before Min Bound

<span style="color:red"><strong>为什么要改：</strong>minn 是 MathComp 名称；Nat.min 这个名字在 Lean 中仍可使用。<br><strong>怎么改：</strong>只将 minn 换为 Nat.min，数量上界的证明仍按下方模板处理。</span>

Use this when the final statement mentions `Nat.min` or <span style="color:gray">`minn`</span>.

<span style="color:red"><strong>1）这段代码在干嘛：</strong>先得到计数不超过 k，再把这个上界传给 min 表达式。<br><strong>2）怎么换成 Lean 代码：</strong>① 原局部证明的 have/Proof./Qed. 和 count 表达式需换成 Lean 写法；minn 换 Nat.min，但已有 Nat.min 字样不必改名。计数界仍需原业务论证。<br>② 已有 hCount : s.countP P ≤ k 时，可写 <code style="white-space:pre-wrap">have hMin : Nat.min m (s.countP P) ≤ Nat.min m k :=&#10;  min_le_min_left m hCount</code>；该声明是通用序关系引理，不叫 Nat.min_le_min_left。</span>

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



## Local Connector Fact Policy <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【要求把不同写法之间的等式单独命名，方便后面的步骤明确引用。命名与局部作用域规则可保留；实际 Lean 声明的写法见上面的模板。】</span>
For this proof class, local connector facts are usually better than long inline rewrites.

Preferred names:

- `H_indicator_filter`
- `H_filter_count`
- `Hcount_rest_tasks`
- `Hcount_exceeding_bound`
- `Hmin_count_bound`

Avoid a long script that repeatedly changes representation without naming the bridge.


<a id="lean-review-bool-prop"></a>


## Bool / Prop Separation <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【说明计数完成后，如何处理布尔条件和普通不等式，让最后的算术证明继续。】</span>

These branches often have a second failure mode after the counting shape is already stable.

<span style="color:red"><strong>为什么要改：</strong>此句的 big_mkcond/sum1_count 指向旧库。<br><strong>怎么改：</strong>换用当前 List/Finset 的桥接接口。</span>

The branch is no longer stuck on <span style="color:gray">`big_mkcond`</span> or <span style="color:gray">`sum1_count`</span>, but it still fails because it keeps switching between:

<span style="color:red"><strong>为什么要改：</strong>ssreflect reflection 指向旧库的反射机制；真实 Bool 与算术之间来回切换的现象仍可能发生。<br><strong>怎么改：</strong>先看是否实际存在 Bool；普通 Lean 不等式无需反射。当前 Lean 已有 lia，不必因同名而改掉它。</span>

- boolean comparison and <span style="color:gray">ssreflect reflection</span>
- Prop-level arithmetic needed for `lia`, `Nat.min`, or the final strict inequality

This section covers only the count-branch version of that problem.

<span style="color:red"><strong>为什么要改：</strong>下方灰色触发句只要求出现计数、min 或算术目标；这些在 Lean 中通常已经是 Prop，不足以说明存在 Bool/Prop 问题。<br><strong>怎么改：</strong>把入口收窄到实际出现 Bool 定义或包装、且其与命题的关系影响当前证明时。计数还未稳定时先规范化的末句保留。</span>

<span style="color:gray">Use it when the branch is already about `count`, `Nat.min` or `minn`, or a final arithmetic inequality derived from a count bound.</span> If the branch is still drifting between indicator sum, filtered big operator, and count, finish that normalization first.


<a id="lean-review-problem-shape"></a>


### Problem Shape <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【用一个常见失败过程说明，为什么计数已经做完，最后的不等式仍可能卡住。｜重改】</span>
Typical sequence:

<span style="color:red"><strong>为什么要改：</strong>原例把自然数比较当作 Bool；Lean 的普通 &lt;、≤ 已经是 Prop。<br><strong>怎么改：</strong>区分普通比较、decide 包装与业务 Bool，不能仅凭出现计数不等式就安排转层。</span>

1. The proof establishes <span style="color:gray">a boolean fact such as `count P s < k`, `count P s <= k`, or `0 < x`</span>.
2. The next step needs Prop arithmetic, a `Nat.min` side condition, or a contradiction argument.

<span style="color:red"><strong>为什么要改：</strong>灰色接口、视图和 %coq_nat 是 MathComp/SSReflect 执行细节；它们不是 Lean 的转换步骤。<br><strong>怎么改：</strong>普通比较直接证明；真实包装需要显式连接时可用 of_decide_eq_true 或业务定义。Lean 4.33.1 已有 lia，omega 也可按目标选用。</span>

3. The script bounces among <span style="color:gray">`ltnW`, `ltnNge`, `move/ltP`, `move/leP`, `%coq_nat`</span>, and `lia` without committing to one layer.
4. The final arithmetic step fails even though the count argument is already essentially done.

The root cause is not that one specific lemma is missing.

<span style="color:red"><strong>为什么要改：</strong>原段落沿用 MathComp 比较的 Bool→Prop 跨层背景；Lean 普通自然数比较已经是 Prop，不会经历同一过程。<br><strong>怎么改：</strong>只在实际业务 Bool 或包装确实影响证明时保留这段跨层说明；普通不等式省去该转换。</span>

<span style="color:gray">The branch crossed the bool/Prop boundary</span> without deciding which layer should own the rest of the proof.



### Boundary Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【规定什么时候把布尔条件交给命题层处理，以及何时才需要转回布尔结果。｜中改】</span>

<span style="color:red"><strong>为什么要改：</strong>“计数或 min 已稳定”不足以要求在 Bool/Prop 两种结束方式之间选择；普通 Lean 比较已经在 Prop。<br><strong>怎么改：</strong>普通不等式直接继续证明；真实业务 Bool 才处理对应命题。本地 Classic pending/completed 仍返回 Bool，不能连这些入口一起删掉。</span>

<span style="color:gray">Once the branch has a stable `count` or `Nat.min` expression, decide whether the rest of the branch should finish in:</span>

- <span style="color:gray">ssreflect boolean comparison form</span>
- Prop arithmetic form

<span style="color:red"><strong>为什么要改：</strong>灰色部分把算术前转一次 Prop 设为必经步骤；Lean 普通不等式无需这一动作。<br><strong>怎么改：</strong>省去多余转换，保留必要转换后维持稳定的原则。当前 Lean 有 lia，omega 只是可选工具。</span>

<span style="color:gray">If the remaining work is final arithmetic, `Nat.min` side conditions, or `lia`, move to Prop exactly once</span> and stay there until that subproof closes. Do not alternate between boolean reflection and Prop arithmetic after the handoff.


<a id="lean-review-layer-map"></a>


### Layer Map <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【并排列出布尔比较和普通命题的典型写法，帮助识别当前事实属于哪一类。｜基本重写】</span>
Use this rough split.

- bool layer

  <span style="color:red"><strong>为什么要改：</strong>下面灰色比较在 MathComp 中属于 Bool，在 Lean 中同样外观通常属于 Prop，原分类必须重排；ltnW/ltnNge 与反射视图也属于旧接口。<br><strong>怎么改：</strong>按 b : Bool、命题 b = true、普通比较分三类。b = decide P 时可提取 P；无已知定义对应关系时，不能凭空得到算术命题。</span>

  - <span style="color:gray">`count P s < k`</span>
  - <span style="color:gray">`count P s <= k`</span>
  - <span style="color:gray">`ltnW`</span>
  - <span style="color:gray">`ltnNge`</span>
  - boolean rewriting and <span style="color:gray">reflection views</span>
- Prop layer

  <span style="color:red"><strong>为什么要改：</strong>%coq_nat 是 Coq 作用域写法，不能照搬成 Lean 的换层步骤。<br><strong>怎么改：</strong>去掉 Coq scope，普通比较直接用 Prop。</span>

  - <span style="color:gray">`(count P s < k)%coq_nat`</span>
  - <span style="color:gray">`(count P s <= k)%coq_nat`</span>
  - `lia`

  <span style="color:red"><strong>为什么要改：</strong>have -> 是旧局部证明语法，不能直接照搬。<br><strong>怎么改：</strong>局部等式用具名 have 后 rw。lia 本身在当前 Lean 中存在。</span>

  - <span style="color:gray">`have -> : Nat.min a b = ... by lia`</span>
  - contradictions and transitivity using ordinary `<`, `<=`, or `=` hypotheses

<span style="color:red"><strong>为什么要改：</strong>Lean 自然数的严格界已是命题，放宽上界不需要先留在 Bool 层，因此这里规定的位置失效。<br><strong>怎么改：</strong>用 Nat.le_of_lt 得到非严格界；是否还需 Bool 包装由实际目标决定。</span>

<span style="color:gray">`ltnW` is usually a bool-side preparation step. Use it before the Prop handoff if you need a non-strict boolean fact.</span>


<a id="lean-review-handoff"></a>


### One-Way Handoff Protocol <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【给出整理计数、转换必要的布尔条件、完成算术并提交结果的具体顺序。｜重改】</span>
1. Finish count normalization first.

   <span style="color:red"><strong>为什么要改：</strong>这里只需替换 MathComp count 的接口，不改“先稳定计数”的要求。<br><strong>怎么改：</strong>根据容器使用 List.countP 或过滤 Finset 的 card。</span>

   - The branch should already be in <span style="color:gray">`count`</span>, plain nat arithmetic, or `Nat.min` form.

<span style="color:red"><strong>为什么要改：</strong>步骤 2 默认还存在 Bool 比较，紧接着步骤 3 要求手工转 Prop；普通 Lean 计数不等式并不经过这条路线。<br><strong>怎么改：</strong>普通 Prop 跳过转换。实测当前 lia 可直接处理 decide (a &lt; b) = true；业务 Bool 是否也能自动处理仍看定义与结果，必要时才显式 of_decide_eq_true。</span>

2. <span style="color:gray">Isolate the last boolean fact you need.</span>
   - Typical examples: <span style="color:gray">`Hcount_lt : count P s < k`, `Hcount_le : count P s <= k`, `Hpos : 0 < x`</span>.
3. <span style="color:gray">Convert that fact into Prop exactly once.</span>
   - <span style="color:gray">`move/ltP: Hcount_lt => Hcount_lt_prop.`</span>
   - <span style="color:gray">`move/leP: Hcount_le => Hcount_le_prop.`</span>
4. Finish the remaining arithmetic entirely in Prop.
   - Use `lia`.
   - Rewrite `Nat.min` only after the side condition is already a Prop inequality.
5. Reflect back only if the final goal itself is a boolean comparison.

   <span style="color:red"><strong>为什么要改：</strong>这两条 apply/view 是 SSReflect 反射写法；“仅最终目标要求 Bool 时才返回”的条件仍然有效。<br><strong>怎么改：</strong>目标确为 decide P = true 时，可用 decide_eq_true；普通 Prop 目标不添加返回步骤。</span>

   - <span style="color:gray">`apply/ltP. exact Hgoal_prop.`</span>
   - <span style="color:gray">`apply/leP. exact Hgoal_prop.`</span>


<a id="lean-review-local-bridges"></a>


### Common Local Bridges <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出几种小步骤，用来转换比较形式或把严格上界变成非严格上界。｜基本重写】</span>
Use small local connectors rather than bouncing back and forth across the boundary.

<span style="color:red"><strong>为什么要改：</strong>原例的 exact:、ltnW 以及“在 Bool 一侧放宽界”依赖 MathComp。<br><strong>怎么改：</strong>自然数 Prop 严格界用 Nat.le_of_lt；局部结论写 have hle : a ≤ b := ...。</span>

- strict to non-strict <span style="color:gray">on the bool side</span>
  - <span style="color:gray">`have Hle_bool : a <= b by exact: ltnW Hlt_bool.`</span>
- bool to Prop

  <span style="color:red"><strong>为什么要改：</strong>move/ltP、move/leP 是旧视图；Lean 只对实际包装的条件讨论转换。<br><strong>怎么改：</strong>decide P = true 可用 of_decide_eq_true。真正的 Bool 合取可先 simp only [Bool.and_eq_true] at h 再 rcases；普通 Prop 不做额外往返。</span>

  - <span style="color:gray">`move/ltP: Hlt_bool => Hlt_prop.`</span>
  - <span style="color:gray">`move/leP: Hle_bool => Hle_prop.`</span>
- Prop back to a final bool goal

  <span style="color:red"><strong>为什么要改：</strong>apply/ltP、apply/leP 的 SSReflect 语法不能直接作为 Lean 指令。<br><strong>怎么改：</strong>仅当最终目标为 decide P = true 时用 decide_eq_true；已有 Prop 证明时直接提交。</span>

  - <span style="color:gray">`apply/ltP. exact Hlt_prop.`</span>
  - <span style="color:gray">`apply/leP. exact Hle_prop.`</span>

Do not use these bridges as an open-ended rewrite loop. Use them once to transfer ownership of the branch.

<a id="lean-review-template-4"></a>

### Template 4: Count Bound To Prop Arithmetic
Use this when the count bound is done and only arithmetic remains.

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把“计数小于 k”加强为“小于 k + 1”；原代码先转到命题层做算术，再转回。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 普通自然数比较已是 Prop，因此原 Hcount_lt_prop 中转与 apply/ltP 往返可省。已有普通计数界后，可用 <code style="white-space:pre-wrap">have hGoal : s.countP P &lt; k + 1 := by&#10;  omega</code>；当前 Lean 的 lia 也可用于适合的算术目标。实际 decide 包装需要显式处理时，再用 of_decide_eq_true/decide_eq_true，不要求每次手工往返。</span>

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

<span style="color:red"><strong>1）这段代码在干嘛：</strong>利用计数不超过 k，把“计数与 k 的较小值”改写成计数。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 的 ≤ 已是 Prop，所以普通计数界无需原 leP 中转。已有 hCount : s.countP P ≤ k 时用 <code style="white-space:pre-wrap">rw [Nat.min_eq_left hCount]</code>；若输入仍带 decide 包装，可先提取命题。原 have -> 的匿名改写语法要换，但当前 Lean 并非没有 lia。</span>

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

<span style="color:red"><strong>为什么要改：</strong>PeanoNat.Nat.min_l/min_r 是 Coq 声明，Lean 不能直接引用；左右两条引理所需的 ≤ 方向也应分别核对。<br><strong>怎么改：</strong>左边较小时用 Nat.min_eq_left h（h : a ≤ b），右边较小时用 Nat.min_eq_right h（h : b ≤ a）。先证明条件，再 rw；其余思路保留。</span>

If you prefer <span style="color:gray">`PeanoNat.Nat.min_l`</span> or <span style="color:gray">`PeanoNat.Nat.min_r`</span>, discharge the side condition only after it is already in Prop form.

<a id="lean-review-contradiction"></a>

### Contradiction Pattern With `ltnNge`

<span style="color:red"><strong>为什么要改：</strong>ltnNge 是 MathComp 的布尔不等式接口。<br><strong>怎么改：</strong>普通 Lean 不等式可直接反证；下方代码批注给出相应 Prop 证明步骤。</span>

Use <span style="color:gray">`ltnNge`</span> as a boundary-specific contradiction tool, not as a general rewrite strategy.

<span style="color:red"><strong>1）这段代码在干嘛：</strong>反设 b 不超过 a，用已有数值界推出矛盾，从而证明 a 小于 b。<br><strong>2）怎么换成 Lean 代码：</strong>ltnNge、negP/leP 是 Bool 反射步骤；Lean 的 Prop 目标可直接 <code style="white-space:pre-wrap">by_contra hNot&#10;have hge : b ≤ a := Nat.le_of_not_gt hNot&#10;omega</code>。最后一步须有足够的上下文界；若目标是 decide (a &lt; b) = true，先 apply decide_eq_true。</span>

```coq
rewrite ltnNge.
apply/negP => /leP Hge_prop.
lia.
```

This is appropriate when the goal is a boolean strict inequality and the contradiction should finish in Prop arithmetic.



### Boundary Failure Signs <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出几种症状，帮助判断最后的算术是否仍卡在布尔条件的转换上。｜中改】</span>



The boundary was crossed at the wrong time if:

<span style="color:red"><strong>为什么要改：</strong>实测当前 Lean lia 能直接使用 decide (a &lt; b) = true，而 omega 在同一测试中不能；“有 Bool 包装就没有可用前提”不是固定判据。<br><strong>怎么改：</strong>根据实际自动化结果决定是否显式桥接；不能机械把 lia 换成 omega。</span>

- <span style="color:gray">`lia` sees no usable arithmetic hypotheses because all comparisons are still boolean facts.</span>

<span style="color:red"><strong>为什么要改：</strong>minn、ltn/leq 是旧接口；普通 Lean ≤ 已可用作 min 侧条件。<br><strong>怎么改：</strong>minn 换 Nat.min，先核实已有比较是否已是 Prop，真实业务 Bool 才按定义处理。</span>

- `Nat.min` or <span style="color:gray">`minn`</span> side conditions do not discharge because the branch still only has <span style="color:gray">`ltn`</span> or <span style="color:gray">`leq`</span> facts.
- the script proves a Prop inequality, immediately reflects it back to bool, then needs to move back to Prop again.



- the count argument is complete, but the strict inequality still fails because the branch never committed to one final layer.


<a id="lean-review-failure-signatures"></a>


## Failure Signatures For This Skill <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【把计数转换中的常见报错对应到需要检查的表达式和缺失步骤。｜重改】</span>

<span style="color:red"><strong>为什么要改：</strong>下面三个错误串点名 MathComp 的 big_mkcond、sum1_count 和旧求和/计数表示；Lean 不会直接使用这些签名。<br><strong>怎么改：</strong>换成目标 Lean 版本的实际诊断及表达式。过滤和接口可核对 Finset.sum_filter / List.countP_eq_length_filter，保留原数学数量的含义。</span>

- <span style="color:gray">`The LHS of big_mkcond ... does not match any subterm`</span>
  The branch is not yet in the expected indicator-sum head form.
- <span style="color:gray">`The LHS of sum1_count ... does not match any subterm`</span>
  The branch is not yet a filtered sum of ones.
- <span style="color:gray">`Unable to unify ... count ... with ... \sum_ ...`</span>
  The count bridge has not been established yet.

<span style="color:red"><strong>为什么要改：</strong>No applicable tactic 是这里采用的 Coq/SSReflect 故障签名，不能原样充当 Lean 的匹配入口。<br><strong>怎么改：</strong>按当前 Lean 的实际 diagnostic 与证明状态重建该条目，不机械替换报错文字。</span>

- <span style="color:gray">`No applicable tactic` after several bigop rewrites in a count argument</span>
  The proof is drifting across indicator, filter, and count forms without a stable target.
- A strict inequality fails after a count argument “should already be done”

  <span style="color:red"><strong>为什么要改：</strong>原句中的 Bool→Prop 桥接依赖 MathComp 比较背景；普通 Lean 不等式已是 Prop，这个待完成步骤可能根本不存在。<br><strong>怎么改：</strong>普通比较不安排额外跨层；只有实际存在业务 Bool 或包装时，才处理对应命题。</span>

  The arithmetic step is too early; the count layer or <span style="color:gray">the bool-to-Prop bridge</span> is not finished.


<a id="lean-review-anti-patterns"></a>


## Anti-Patterns <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出会让计数证明反复绕路的做法，提醒先完成必要的表示转换。｜中改】</span>
- Do not feed an indicator sum directly to a count lemma.

<span style="color:red"><strong>为什么要改：</strong>灰色 minn 是 MathComp 名称；先稳定计数再处理上界的原则可保留。<br><strong>怎么改：</strong>使用 Nat.min 及符合当前侧条件的 Lean 引理。</span>

- Do not apply `Nat.min` or <span style="color:gray">`minn`</span> lemmas before the raw count expression is stable.
- Do not bounce between filtered sequence form and count form without naming the connector fact.
- Do not start the final strict inequality proof while the branch still contains `if ... then 1 else 0`.

<span style="color:red"><strong>为什么要改：</strong>当前 Lean lia 可直接处理部分 decide 比较，不能因 Bool 包装就一律禁用；ltn/leq 也不是普通 Lean 比较的表示。<br><strong>怎么改：</strong>按实际前提与 tactic 结果判断是否需要桥接。改的是调用条件，不是 lia 名称。</span>

- <span style="color:gray">Do not call `lia` while the main inequalities still only exist as `ltn` or `leq` facts.</span>
- Do not reflect back to bool in the middle of a Prop arithmetic subproof.

<span style="color:red"><strong>为什么要改：</strong>这条位置限制依赖 MathComp 的 ltnW 与反射流程；Lean 严格界本来就是 Prop。<br><strong>怎么改：</strong>普通自然数界直接用 Nat.le_of_lt，不人为恢复 Bool 层。</span>

- <span style="color:gray">Do not use `ltnW` after the branch has already moved into Prop unless you are deliberately rebuilding a final bool goal.</span>

<span style="color:red"><strong>为什么要改：</strong>这里仍需替换 minn 的旧库接口；准备正确侧条件的要求不受语言变化影响。<br><strong>怎么改：</strong>换为 Nat.min，按实际条件使用对应引理；真实 Bool 条件需要时再建立命题关系。</span>

- Do not rewrite `Nat.min` or <span style="color:gray">`minn`</span> while the only available side condition is still in boolean form.
- Do not encode theorem-local names such as `Hsum_slack` or `Hsum_succ` into the skill. Keep the skill at the proof-pattern level.
- Do not use this skill for focus drift or early-bound theorem application failures. Those are different problem classes.



## Minimal Debug Log <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【给出一份简短记录表，写清当前计数写法、目标写法和下一步缺少的连接。原字段可保留，填写实际 List/Finset、Bool/Prop、当前 Lean 目标与引理声明即可。】</span>

```text
Current counting shape:
Target normal form:
Next intended lemma:
Does that lemma live in indicator / filtered bigop / count / min-arithmetic layer:
Missing bridge step:
Named local connector fact:
Is the final arithmetic step still premature: yes/no
```



## Success Condition <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【说明怎样确认计数表示已经稳定，后续证明可以顺利使用它。】</span>
This skill has worked when the branch stops oscillating between indicator sums, filtered big operators, counts, and `min` bounds, and every subsequent step stays inside one chosen counting normal form until the final arithmetic handoff.
