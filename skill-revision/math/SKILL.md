<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>你想把一个式子改写成与它相等的另一个式子，但系统说选用的等式定理不匹配。这个 skill 尤其处理求和、反复相加和乘法之间的转换，帮助你判断当前还缺哪一步整理。<br><strong>具体例子：</strong>“把 x 加四次”和“4 × x”表示同一个数。但如果当前左边仍然写成求和或重复执行加法的形式，你直接要求在这一侧使用乘法交换律，可能找不到可以改写的乘法。你需要先把这一侧证明成“4 × x”，之后才能把它改成“x × 4”。<br><strong>它会怎么处理：</strong>先看系统实际显示的表达式，再查看准备使用的等式需要什么形式。如果两者之间还差一步，就先用已有定理完成这一步；必要时单独证明一个小等式作为连接。每次改写后重新查看结果，再决定下一步。它希望证明沿着明确的路线前进，而不是不断尝试看起来相关、实际却对不上当前式子的定理。</span>

<span style="color:red">【Lean迁移总评】真实目标驱动、局部桥接和稳定正规形的方法可保留；主要改动是 MathComp 正规形路线、Bool-as-Nat 表示、库模板及诊断映射。整体重写力度：中重。</span>

<span style="color:red">【Bigop Endgame Discipline｜首要结构性问题 1】<a href="#lean-review-6">点击跳转</a><br><strong>原来在做什么：</strong>这份 skill 教证明者逐步整理求和。例如 MathComp 可能先把“同一个数加 n 次”的求和改成 iter（重复执行加法），然后才改成乘法；原文据此决定下一条改写该做什么。<br><strong>改哪里：</strong>顶部到 Procedure、Bigop Endgame 贯穿使用的“当前形状→下一步”路线，尤其用 MathComp iter 识别中间态的流程分支。<br><strong>为什么：</strong>Lean 的求和定理可能直接给出乘法，也可能先给出基数的标量乘法；它不承诺经过 MathComp iter。只翻译代码却保留旧分类，skill 仍可能用未出现的 MathComp iter 状态解释 Lean 错误，给出不适用的下一步。<br><strong>替换（Rocq → Lean）：</strong>big_const_ord/iter_addn 的常数和任务 → simp [Nat.mul_comm] 或 Finset.sum_const 后化简；big_distrr 的分配任务 → Finset.sum_mul/Finset.mul_sum；big_split → Finset.sum_add_distrib；mulnC → Nat.mul_comm。每条规则的后续状态用真实 Lean proof state 确认。<br><strong>删除（仅未来 Lean 版）：</strong>撤下专门识别 MathComp iter 的默认流程分支；只有实际 Lean 目标出现 Function.iterate 时，再提供针对该表示的规则。<br><strong>保留：</strong>先选择表示、每步查看实际结果、保持表达式稳定的证明方法。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-3">Procedure</a>；<a href="#lean-review-6">Bigop Endgame Discipline</a>；<a href="#lean-review-9">Common Failure Signatures</a>。</span>

<span style="color:red">【Rocq 示例需转为 Lean 代码｜点击跳转】<a href="#lean-review-code-1">示例 1</a>；<a href="#lean-review-code-2">示例 2</a>；<a href="#lean-review-code-3">示例 3</a>。共 3 个原代码块，全部保留。</span>

---
name: coq-proof-state-discipline
description: 'Debug Coq and ssreflect proofs by following the exact proof state, choosing rewrites only when their left-hand side literally matches the goal, and adding small bridge lemmas for bigop, iter, and multiplication mismatches. Use when rewrites fail, big_const_ord or big_distrr are involved, or a proof seems mathematically obvious but Coq reports that the lemma does not match any subterm.'
argument-hint: 'Describe the goal, the failed rewrite, and the current goal shape.'
user-invocable: true
---

<span style="color:red">【Frontmatter｜中改】<br><strong>改哪里：</strong>frontmatter 的 name、description，以及 big_const_ord/big_distrr/iter/addn/muln 等触发词。<br><strong>为什么：</strong>这些名称指向 Coq/MathComp 的声明；Lean 的求和表示和改写入口不同，旧词表不能识别对应任务。<br><strong>替换（Rocq → Lean）：</strong>name 建议改为 lean-proof-state-discipline；description 的库名和信号换成 Finset.sum_const、Finset.sum_mul、Finset.mul_sum、List.sum、Prosa.Util.Sum.sumSeq/sumFiltered 及 rw 匹配失败。以下通用片段已按本地 Lean 4.33.1 / 项目锁定的 Mathlib 核对；完整业务证明仍需目标上下文。h、xs、P 等是局部变量，不是新库接口。<br><strong>保留：</strong>调试真实 proof state 的用途及 argument-hint。已核实 <code style="white-space:pre-wrap">Prosa.Util.Sum.sumSeq s F</code> 等于 (s.map F).sum，<code style="white-space:pre-wrap">Prosa.Util.Sum.sumFiltered s P F</code> 等于 ((s.filter P).map F).sum；过滤常数 1 求和与 countP 的桥接可用 <code style="white-space:pre-wrap">simp [Prosa.Util.Sum.sumFiltered, List.countP_eq_length_filter]</code>，无需另造封装 API。</span>

<span style="color:red">【Coq Proof-State Discipline】<br><strong>本节在做什么：</strong>帮助根据系统实际显示的表达式选择改写步骤，避免凭数学直觉盲试引理。</span>

# Coq Proof-State Discipline

<a id="lean-review-1"></a>

<span style="color:red">【When to Use｜中改】<br><strong>本节在做什么：</strong>列出求和、重复加法和乘法之间改写失败时适合使用本 skill 的情况。<br><strong>改哪里：</strong>适用情形中的求和记号、mul1n/mulnC、big_ord_recr/big_const_ord 名称及 Coq 报错字符串。<br><strong>为什么：</strong>Lean 使用不同的求和声明，常数求和也不保证经过 MathComp 的 iter 中间态。<br><strong>替换（Rocq → Lean）：</strong>序列求和改用 (s.map f).sum 或 Prosa.Util.Sum.sumSeq s f；有限集合求和用对应 Finset 表达式。mul1n/mulnC → Nat.one_mul/Nat.mul_comm，big_const_ord → Finset.sum_const。按声明及真实目标形状触发；报错字符串从当前 Lean diagnostics 采集。<br><strong>保留：</strong>改写失败时先对齐当前式子与引理的用途。</span>

## When to Use
- A rewrite should work mathematically, but Coq rejects it.
- A proof oscillates between `\sum_`, `iter`, addition, and multiplication forms.
- `mul1n`, `mulnC`, `big_ord_recr`, or `big_const_ord` fail with “does not match any subterm”.
- You need a small bridge lemma between a local goal shape and the intended algebraic form.
- A large model is proposing steps from intuition instead of from the literal current goal.

<a id="lean-review-2"></a>

<span style="color:red">【Core Rule｜轻改】<br><strong>本节在做什么：</strong>要求先核对当前式子和准备使用的等式，再决定是否改写。<br><strong>改哪里：</strong>Core Rule 中“引理左侧不是目标的字面子项，就先补桥接”的硬条件。<br><strong>为什么：</strong>打印出的字面形状只能初筛；Lean 的实际匹配还受类型、隐式参数和定义展开影响。此类核对在 Coq 中也有价值，不是 Lean 独有问题。<br><strong>替换（Rocq → Lean）：</strong>先 <code style="white-space:pre-wrap">trace_state</code> 读目标，用 <code style="white-space:pre-wrap">#check 候选引理</code> 核对类型，再试 <code style="white-space:pre-wrap">rw [h]</code> 或 <code style="white-space:pre-wrap">rw [←h]</code>。只差封装定义时用 change 等价目标 或 simp only [定义]；确实缺少等式时再证明局部 have。<br><strong>删除（仅未来 Lean 版）：</strong>删除“不逐字相同就必须新建引理”的绝对判据。<br><strong>保留：</strong>依据实际目标选择改写，避免仅凭数学直觉猜引理。</span>

## Core Rule
Choose the next lemma from the exact current goal syntax, not from mathematical intent alone.

If the left-hand side of the next lemma is not a literal subterm of the current goal, do not rewrite yet. First normalize one side or add a bridge lemma.

<a id="lean-review-3"></a>

<span style="color:red">【Procedure｜重改｜需重建正规形路线】<br><strong>本节在做什么：</strong>给出查看表达式、检查改写条件、补连接等式并逐步验证的顺序。<br><strong>改哪里：</strong>Procedure 的步骤 1（记录目标）、步骤 3（匹配检查）、步骤 5—6（规范化及查看结果）。<br><strong>为什么：</strong>原分类和 bigop→iter 路线依赖 MathComp；Lean 的求和结果取决于选定声明，不能预填旧中间态。<br><strong>替换（Rocq → Lean）：</strong>步骤 1 从当前 Lean 源位置的 proof state 记录 List.sum、Prosa.Util.Sum.sumSeq/sumFiltered、Finset.sum、Nat 乘法或 Bool.toNat；步骤 3 核对 rw 方向和类型；步骤 5 常数和用 simp 或 Finset.sum_const；步骤 6 用 trace_state 记录实际结果。这里的 snapshot 只是诊断记录。<br><strong>删除（仅未来 Lean 版）：</strong>原步骤 6 的 bigop→iter 检查和步骤 7 的 iter n (addn x) 0 表示不作为 Lean 默认分支；只有真实目标出现 Function.iterate 才处理它。本节 snapshot 是诊断记录，无需另建持久 session。<br><strong>保留：</strong>最小局部桥接、每次改写后验证、选定一种稳定表示。</span>

## Procedure
1. Snapshot the exact goal.
   - Quote the full goal or the smallest relevant subterm.
   - Record the head form: `bigop`, `iter`, `addn`, `muln`, or boolean-as-nat.
2. Name the intended rewrite.
   - Write the lemma you want to use.
   - Write its exact left-hand side.
3. Run the shape check.
   - Ask whether that left-hand side occurs syntactically in the current goal.
   - If the answer is no, stop and choose a bridge step instead.
4. Add the smallest bridge lemma that fixes the mismatch.
   - Prefer a local lemma when the mismatch is specific to a fixed variable, branch, or index.
   - Prefer a generic lemma only when the same mismatch recurs across proofs.
5. Normalize inside-out.
   - First settle constant or boolean-valued inner sums.
   - Then distribute or factor outer sums.
   - Use arithmetic rewrites such as `mulnC` only after multiplication is literally present.
6. Validate after each nontrivial rewrite.
   - Re-read the new goal head form.
   - If the goal moved from `bigop` to `iter`, update the plan before continuing.
7. Keep one stable normal form.
   - Avoid oscillating between `\sum_(i < n) x`, `iter n (addn x) 0`, `x * n`, and `n * x` in the same branch.

## Bridge Lemma Strategy

<a id="lean-review-4"></a>

<span style="color:red">【Prefer a local bridge lemma when｜中改】<br><strong>本节在做什么：</strong>说明什么时候只需为当前变量或分支证明一个小等式。<br><strong>改哪里：</strong>局部桥接条件中的 boolean-valued 常数，以及下面 backlog 求和模板所用的库接口和数值表示。<br><strong>为什么：</strong>原模板把 MathComp Bool 直接用于自然数求和；本地已核实 Lean Classic 的 completed/pending/backlogged 仍为 Bool，service_at 为 Nat，求和时需明确 Bool 的数值。<br><strong>替换（Rocq → Lean）：</strong>导入 <code style="white-space:pre-wrap">Prosa.Classic.Model.Schedule.Global.Basic.Schedule</code> 并打开 <code style="white-space:pre-wrap">Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule</code>；把自然数求和中的 backlogged ... 改为 (backlogged ...).toNat。优先使用这套显式 job_arrival/job_cost 接口，不与 Prosa.Behavior 的实例参数版混用。<br><strong>删除（仅未来 Lean 版）：</strong>对于这一常数和，去掉为得到 0/1 而先按 Bool 分类的固定步骤；simp [Nat.mul_comm] 即可处理。<br><strong>保留：</strong>只给当前变量或分支需要的事实建立局部等式。</span>

### Prefer a local bridge lemma when
- The expression depends on a fixed local variable such as `t`, `cpu`, or a branch condition.
- A boolean-valued term becomes a constant over an index.
- The proof only needs the lemma once.

Template:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>证明某一时刻的同一个 backlog 数值在所有处理器上相加，等于这个数值乘以处理器数量；原代码先按 backlog 的真假分类。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>代码中的 have/Proof/Qed、序数求和、Bool 项与 case/rewrite 收尾。<br><strong>为什么：</strong>Lean 局部证明使用 := by；该和的每项相同，只需常数求和化简，并不需要 MathComp 的真假分类和 iter 路线。<br><strong>替换（Rocq → Lean）：</strong>用 Classic 的 Schedule 接口，并写 open scoped BigOperators；模板换为 <code style="white-space:pre-wrap">have cpu_sum_of_backlogged (t : Nat) :&#10;    (∑ _cpu : Fin num_cpus, (backlogged job_arrival job_cost sched j t).toNat) =&#10;      (backlogged job_arrival job_cost sched j t).toNat * num_cpus := by&#10;  simp [Nat.mul_comm]</code>。其中 Bool 项显式改成 .toNat。<br><strong>删除（仅未来 Lean 版）：</strong>去掉先对 backlog 真假分类的额外步骤；将值写成 .toNat 后，常数和可以直接化简。</span>

```coq
have cpu_sum_of_backlogged t :
  \sum_(cpu < num_cpus) (backlogged job_arrival job_cost sched j t) =
  backlogged job_arrival job_cost sched j t * num_cpus.
Proof.
  by case: (backlogged job_arrival job_cost sched j t);
     rewrite big_const_ord ?iter_addn ?mul1n ?mul0n ?addn0.
Qed.
```

<a id="lean-review-5"></a>

<span style="color:red">【Prefer a generic bridge lemma when｜中改】<br><strong>本节在做什么：</strong>说明什么时候值得把反复使用的求和等式整理成通用引理。<br><strong>改哪里：</strong>通用桥接的库查询对象，以及“已有常数和还需要补什么引理”的判断。<br><strong>为什么：</strong>Lean 已有常数求和定理，不能只为重现 MathComp 的 iter 中间态新增一层 helper。<br><strong>替换（Rocq → Lean）：</strong>先查 Finset.sum_const、Finset.card_eq_sum_ones；Nat 值的有限常数和可尝试 simp。确有重复复用需要时，使用下方经验证的 Fin 索引辅助等式。<br><strong>保留：</strong>同一连接等式反复出现时才整理成通用引理。</span>

### Prefer a generic bridge lemma when
- The same normalization gap appears in multiple proofs.
- The goal has already become a literal constant sum.

Template:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把“同一个自然数 x 加 n 次等于 x × n”做成通用辅助定理，让多个证明都可以复用。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>Lemma/Proof/Qed 声明、\sum_(i &lt; n) 和 big_const_ord/iter_addn/mulnC 证明体。<br><strong>为什么：</strong>Lean 可以在 Fin n 上表达恰好 n 项的和，并直接用常数求和化简得到乘法，无需旧 iter 中间层。<br><strong>替换（Rocq → Lean）：</strong>自然数版换为 <code style="white-space:pre-wrap">theorem sum_const_fin_nat (n x : Nat) :&#10;    (∑ _i : Fin n, x) = x * n := by&#10;  simp [Nat.mul_comm]</code>。sum_const_fin_nat 是建议新建的本地辅助名，不是声称已有的 Mathlib API；无需复用时直接使用同一证明体。<br><strong>删除（仅未来 Lean 版）：</strong>去掉显式 iter_addn 转换步骤。</span>

```coq
Lemma big_const_ord_muln n x :
  \sum_(i < n) x = x * n.
Proof.
  by rewrite big_const_ord iter_addn mulnC.
Qed.
```

<span style="color:red">【Bridge Lemma Strategy｜中改】<br><strong>本节在做什么：</strong>帮助判断缺少的连接等式应该只在当前证明中使用，还是整理成可复用的引理。<br><strong>改哪里：</strong>本节末尾指向 assets/bridge-lemma-templates.v 的模板资源及入口链接。<br><strong>为什么：</strong>.v 模板不能作为 Lean 的可编译示例；扩展名、imports 和证明内容需要一起迁移。<br><strong>替换（Rocq → Lean）：</strong>未来资源改为 assets/bridge-lemma-templates.lean，放入已核实的 List/Finset 例子及实际 imports，以 lake env lean 验证后再更新链接。<br><strong>保留：</strong>本轮只记录资源迁移任务，不创建文件、不改原链接，也不假定该资源已存在。</span>

More ready-to-copy templates are in [bridge-lemma-templates](./assets/bridge-lemma-templates.v).

<a id="lean-review-6"></a>

<span style="color:red">【Bigop Endgame Discipline｜重改】<br><strong>本节在做什么：</strong>安排求和证明的收尾顺序，先整理内部项，再处理外层求和和乘法。<br><strong>改哪里：</strong>Bigop Endgame 的常数和、Bool-as-Nat、分配及乘法交换四类具体步骤。<br><strong>为什么：</strong>求和表示和中间态由 Lean 的 List/Finset/Prosa 封装决定；MathComp 的处理顺序及具体引理不能直接复用。<br><strong>替换（Rocq → Lean）：</strong>Finset 的二重和交换 → Finset.sum_comm；常数和 → Finset.sum_const/simp；Bool 数值 → b.toNat；右乘分配 → Finset.sum_mul，左乘分配 → Finset.mul_sum；拆合加法和 → Finset.sum_add_distrib；Nat 乘法交换 → Nat.mul_comm。List/Prosa sumSeq 按实际目标展开并用 List 规则，不硬套 Finset 定理。<br><strong>保留：</strong>先稳定内层表达式，再处理外层组合，不来回切换表示。</span>

## Bigop Endgame Discipline
For ssreflect big operator proofs, use this order.

1. Exchange or rearrange sums only while the goal is still clearly a big operator.
2. Collapse branch-local constant sums.
3. Introduce local bridge lemmas for boolean-as-nat constants.
4. Use `big_distrr` or similar outer distribution only after inner normalization is stable.
5. Use algebraic rewrites such as `mulnC` only when multiplication is literally present.

<a id="lean-review-7"></a>

<span style="color:red">【When To Switch To Count Bridging｜中改】<br><strong>本节在做什么：</strong>说明什么时候问题已经从求和恒等式变成对象个数的上界，需要转到计数 skill。<br><strong>改哪里：</strong>转到 count-bridging 的触发词、minn 名称及 skill_count.md 入口。<br><strong>为什么：</strong>MathComp 引理名不能识别 Lean 的计数目标；目标 skill 的旧 Bool/Prop reflection 管线也需重审。<br><strong>替换（Rocq → Lean）：</strong>触发词换成 List.countP、List.filter 后的 length、Finset.filter 后的 card、Finset.sum_boole、Bool.toNat；minn → Nat.min。按当前布局将未来链接改为 ../count-bridging/SKILL.md。业务接口需要根据 Lean Prosa 当前实际 declaration/API 确认。<br><strong>保留：</strong>只有下一步确实讨论“多少个”或计数上界时才切换 skill。</span>

## When To Switch To Count Bridging
This skill handles generic big-operator, `iter`, and multiplication mismatches.

If the branch has clearly become a counting proof, switch to [ssreflect-count-bridging](./skill_count.md) instead of staying here.

High-signal cues for switching:
- the branch mixes `big_mkcond`, `sum1_count`, `big_filter`, `count`, and `Nat.min` or `minn`
- the same quantity appears both as `if P x then 1 else 0` and as a `count`
- the endgame is no longer a pure big-operator identity, but a bound on how many elements satisfy a predicate
- the next intended theorem lives in the `count` or `min` layer rather than in the generic `bigop` or `iter` layer

Use this generic skill only up to the point where the proof class is clear. Once the branch is really about indicator-sum to count normalization, the count-bridging skill has the stricter pipeline.

<a id="lean-review-8"></a>

<span style="color:red">【Side-Specific Normalization｜中改】<br><strong>本节在做什么：</strong>展示怎样只改写等式的一侧，让它与另一侧或下一条定理的写法一致。<br><strong>改哪里：</strong>只改写一侧的 SSReflect [in RHS] 选择器，以及为了避免 iter 而恢复求和的理由。<br><strong>为什么：</strong>Lean 用 conv 指定等式左/右侧；是否恢复成求和应由下一条引理需要的表示决定。<br><strong>替换（Rocq → Lean）：</strong>已有 hSum : 求和 = 乘法 时，[in RHS] 反向改写换为 <code style="white-space:pre-wrap">conv =&gt;&#10;  rhs&#10;  rw [←hSum]</code>；也可以先证明该局部等式再定向改写。<br><strong>删除（仅未来 Lean 版）：</strong>去掉“Lean 必须避免 Coq iter 中间态”的理由。<br><strong>保留：</strong>只调整需要的一侧，避免两边反复变形。</span>

## Side-Specific Normalization
Sometimes the cleanest fix is to rewrite only one side into the other side’s syntax.

Example:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>只改写等式的右边，把它变回求和形式，让两边使用同一种表示，同时保留左边的原有结构。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>rewrite [in RHS]-big_const_ord 这一条单侧反向改写。<br><strong>为什么：</strong>Lean 不使用 SSReflect 的 [in RHS] 或前缀 - 来选侧、反向；应明确定位右侧，并用真实等式反向改写。<br><strong>替换（Rocq → Lean）：</strong>已有 <code style="white-space:pre-wrap">hSum : (∑ _i : Fin n, x) = x * n</code> 时，换为 <code style="white-space:pre-wrap">conv =&gt;&#10;  rhs&#10;  rw [←hSum]</code>。hSum 承担“乘法恢复为和”的桥接任务。</span>

```coq
rewrite [in RHS]-big_const_ord.
```

Use this when the goal is naturally a big operator and forcing the other side into multiplication would create an unstable `iter` intermediate.

<a id="lean-review-9"></a>

<span style="color:red">【Common Failure Signatures｜重改】<br><strong>本节在做什么：</strong>把常见改写报错对应到当前表达式可能尚未完成的整理步骤。<br><strong>改哪里：</strong>Common Failure Signatures 的 Coq 错误串、原因映射和所引用的故障表。<br><strong>为什么：</strong>旧错误文本及 MathComp 中间态无法给 Lean 错误分类；必须按当前 Lean 实际输出重建“错误→检查→动作”。<br><strong>替换（Rocq → Lean）：</strong>匹配失败 → trace_state 后检查改写式和出现位置；类型不匹配 → 比较 expected/actual type；未知名称 → #check 全限定名 并检查 import；实例合成失败 → #synth 实例类型；未解决目标 → 查看剩余目标并分支证明。英文错误串按目标 Lean 版本采集。常数和案例改为 Finset.sum_const 后观察 card • x，再 simp [Nat.mul_comm]；Fin 索引拆第一项用 Fin.sum_univ_succ，range 拆最后项用 Finset.sum_range_succ。<br><strong>删除（仅未来 Lean 版）：</strong>去掉把 big_const_ord→iter、big_mkcond 或 sum1_count 当作默认 Lean 故障信号的规则。<br><strong>保留：</strong>先解释错误对应的可核实条件，再给下一步动作。</span>

## Common Failure Signatures
See [failure-signatures](./references/failure-signatures.md) for a mapping from common error messages to the missing normalization step.

Short version:
- `Unable to unify "X * n" with "iter n (addn X) 0"` means the goal is still in `iter` form.
- `The LHS of mul1n ... does not match any subterm` means there is no literal `1 * _` yet.
- `The LHS of mulnC ... does not match any subterm` means there is no multiplication node yet, or not the one you think.
- `The LHS of big_ord_recr ... does not match any subterm` means the goal is no longer a standard ordinal big operator head.
- `No applicable tactic` after several rewrites usually means the proof drifted across multiple normal forms without a stable bridge.

If the branch now mentions `big_mkcond`, `sum1_count`, filtered sums of ones, or `count` bounds, stop here and switch to [ssreflect-count-bridging](./skill_count.md). That is no longer a generic bigop mismatch; it is a counting-normalization proof.

<a id="lean-review-10"></a>

<span style="color:red">【Anti-Patterns｜中改】<br><strong>本节在做什么：</strong>列出会让表达式来回变形、却没有推进证明的常见改写习惯。<br><strong>改哪里：</strong>Anti-Patterns 中 big_const_ord/iter_addn/mul1n/mulnC 的盲目串联案例。<br><strong>为什么：</strong>这些是 MathComp 的具体引理；Lean 仍需避免不看中间结果就连续改写。<br><strong>替换（Rocq → Lean）：</strong>示例名单换成 Finset.sum_const、Finset.sum_mul、Nat.mul_comm；调试时每次执行一个 rw 并记录结果，目标明确时允许 simp [已知定义] 完成整步。<br><strong>保留：</strong>不要盲串引理、不要反复切换表示。逐步验证是通用方法，不标成 Lean 独有功能。</span>

## Anti-Patterns
- Do not rewrite because two expressions are mathematically equal if the target lemma does not literally match the goal.
- Do not chain `big_const_ord`, `iter_addn`, `mul1n`, and `mulnC` blindly without checking the intermediate goal.
- Do not use a generic arithmetic lemma when a branch-local bridge lemma is simpler and more robust.
- Do not switch normal forms repeatedly inside one proof branch.

<a id="lean-review-11"></a>

<span style="color:red">【Minimal Debug Log｜轻改】<br><strong>本节在做什么：</strong>提供记录表，写清当前式子、打算用的等式以及改写后的实际结果。<br><strong>改哪里：</strong>调试表的 Literal match in goal 和 Resulting goal head form 两个字段。<br><strong>为什么：</strong>仅记录 yes/no 字面匹配不足以解释 Lean 的实际 rw 结果；还需说明所选索引、求和值类型和改写方向。这些也是通用调试信息。<br><strong>替换（Rocq → Lean）：</strong>Literal match in goal 改为 Matching check，填写索引类型、值类型、改写规则和方向；Resulting goal head form 填执行后的 Lean proof state。例如 <code style="white-space:pre-wrap">Index: Fin n / Finset.range n / List α&#10;Value type: Nat&#10;Rule: Finset.sum_const&#10;Direction: forward / backward&#10;Observed result: 当前 proof state</code>。失败时另记录实际 Lean diagnostic 及源码位置。<br><strong>保留：</strong>Current goal subterm、Desired lemma 等记录用途；不因打印文本不同就自动要求 hBridge。</span>

## Minimal Debug Log
Keep a short log while debugging.

```text
Current goal subterm:
Desired lemma:
Lemma left-hand side:
Literal match in goal: yes/no
If no, bridge lemma or normalization step:
Resulting goal head form:
```

<a id="lean-review-12"></a>

<span style="color:red">【Success Condition｜中改】<br><strong>本节在做什么：</strong>说明怎样确认每次改写都在朝选定的表达式前进。<br><strong>改哪里：</strong>Success Condition 中“每次改写都必须有 literal syntactic match”的验收条件。<br><strong>为什么：</strong>Lean 的打印形式不是实际改写是否合法的唯一依据；是否完成应由 tactic 的结果和编译检查确认。<br><strong>替换（Rocq → Lean）：</strong>验收改为“表达式已变成后续定理所需形式，下一次 rw/apply 实际成功，当前声明通过 Lean 检查”。记录真实路线，例如 List.sum→List.countP 或 Finset.sum→Nat 乘法。<br><strong>删除（仅未来 Lean 版）：</strong>去掉“打印文本必须字面匹配”这一唯一标准。<br><strong>保留：</strong>每一步都向同一个稳定表示推进。</span>

## Success Condition
The proof is on track when each rewrite is justified by a literal syntactic match, and every bridge lemma moves the branch toward a single stable normal form instead of introducing another oscillation.