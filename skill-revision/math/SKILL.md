<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>你想把一个式子改写成与它相等的另一个式子，但系统说选用的等式定理不匹配。这个 skill 尤其处理求和、反复相加和乘法之间的转换，帮助你判断当前还缺哪一步整理。<br><strong>具体例子：</strong>“把 x 加四次”和“4 × x”表示同一个数。但如果当前左边仍然写成求和或重复执行加法的形式，你直接要求在这一侧使用乘法交换律，可能找不到可以改写的乘法。你需要先把这一侧证明成“4 × x”，之后才能把它改成“x × 4”。<br><strong>它会怎么处理：</strong>先看系统实际显示的表达式，再查看准备使用的等式需要什么形式。如果两者之间还差一步，就先用已有定理完成这一步；必要时单独证明一个小等式作为连接。每次改写后重新查看结果，再决定下一步。它希望证明沿着明确的路线前进，而不是不断尝试看起来相关、实际却对不上当前式子的定理。</span>

<span style="color:red">【Bigop Endgame Discipline｜首要结构性问题 1】<a href="#lean-review-6">点击跳转</a><br><strong>为什么会有结构性问题：</strong>这份 skill 会根据求和已经变成什么表达式，决定下一步用哪条等式。例如 MathComp 可能先得到 iter 表示的重复加法，再转成乘法；Lean 的常数求和却可能直接变成乘法，或先出现“项数乘这个值”的表达式。旧中间状态不一定出现，所以原来的判断路线不能只靠更换引理名字迁移。<br><strong>Lean 中大致怎么做：</strong>先确定使用列表求和还是有限集合求和，再根据每一步实际得到的目标继续化简。常数求和按“项数与常数的乘积”处理；只有目标真的出现重复函数应用时，才走对应路线。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-3">Procedure</a>；<a href="#lean-review-6">Bigop Endgame Discipline</a>；<a href="#lean-review-9">Common Failure Signatures</a>。</span>

<span style="color:red">【Rocq 示例需转为 Lean 代码｜点击跳转】<a href="#lean-review-code-1">示例 1</a>；<a href="#lean-review-code-2">示例 2</a>；<a href="#lean-review-code-3">示例 3</a>。共 3 个原代码块，全部保留。</span>

---
name: coq-proof-state-discipline
#<span style="color:red">【description】建议改为“根据 Lean 的真实目标选择改写和局部连接等式；用于 List、Finset 或 Prosa 求和封装与乘法等写法不匹配、rw 失败，或证明在多种等价表示之间反复切换的情况”。理由：以 Lean 的求和表示和改写失败识别任务，更新 MathComp 引理的固定触发。</span>
description: 'Debug Coq and ssreflect proofs by following the exact proof state, choosing rewrites only when their left-hand side literally matches the goal, and adding small bridge lemmas for bigop, iter, and multiplication mismatches. Use when rewrites fail, big_const_ord or big_distrr are involved, or a proof seems mathematically obvious but Coq reports that the lemma does not match any subterm.'
argument-hint: 'Describe the goal, the failed rewrite, and the current goal shape.'
user-invocable: true
---



# Coq Proof-State Discipline <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【帮助根据系统实际显示的表达式选择改写步骤，避免凭数学直觉盲试引理。】</span>

<a id="lean-review-1"></a>



## When to Use <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出求和、重复加法和乘法之间改写失败时适合使用本 skill 的情况。｜中改】</span>

<span style="color:red"><strong>为什么要改：</strong>改写被拒绝、表示反复切换都是通用触发；这里要换的是 Coq 后端名称和下一行的 MathComp 表示。<br><strong>怎么改：</strong>改用 Lean 当前目标与 List/Finset 求和表示，不要求出现旧 iter 中间态。</span>

- A rewrite should work mathematically, but <span style="color:gray">Coq</span> rejects it.
- A proof oscillates between <span style="color:gray">`\sum_`, `iter`</span>, addition, and multiplication forms.

<span style="color:red"><strong>为什么要改：</strong>这条“MathComp 引理＋Coq 错误串”组合不能直接识别 Lean 故障。<br><strong>怎么改：</strong>用实际 Lean 报错和声明重建信号；mul1n/mulnC 对应 Nat.one_mul/Nat.mul_comm，常数和查看 Finset.sum_const。</span>

- <span style="color:gray">`mul1n`, `mulnC`, `big_ord_recr`, or `big_const_ord` fail with “does not match any subterm”</span>.
- You need a small bridge lemma between a local goal shape and the intended algebraic form.
- A large model is proposing steps from intuition instead of from the literal current goal.

<a id="lean-review-2"></a>



## Core Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【要求先核对当前式子和准备使用的等式，再决定是否改写。】</span>
Choose the next lemma from the exact current goal syntax, not from mathematical intent alone.



If the left-hand side of the next lemma is not a literal subterm of the current goal, do not rewrite yet. First normalize one side or add a bridge lemma.

<a id="lean-review-3"></a>



## Procedure <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【给出查看表达式、检查改写条件、补连接等式并逐步验证的顺序。｜重改｜需重建正规形路线】</span>
1. Snapshot the exact goal.
   - Quote the full goal or the smallest relevant subterm.

   <span style="color:red"><strong>为什么要改：</strong>这份目标头分类采用 MathComp 的 bigop/iter/addn/muln，不能当作 Lean 的实际状态分类。<br><strong>怎么改：</strong>记录当前 List.sum、Finset.sum、Prosa 封装或 Bool.toNat，用 trace_state 核实；前面的 snapshot 在这里只是诊断记录。</span>

   - Record the head form: <span style="color:gray">`bigop`, `iter`, `addn`, `muln`, or boolean-as-nat</span>.
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

   <span style="color:red"><strong>为什么要改：</strong>mulnC 是 MathComp 的声明名，Lean 使用自己的自然数乘法引理。<br><strong>怎么改：</strong>将该调用换为 Nat.mul_comm。</span>

   - Use arithmetic rewrites such as <span style="color:gray">`mulnC`</span> only after multiplication is literally present.
6. Validate after each nontrivial rewrite.
   - Re-read the new goal head form.

   <span style="color:red"><strong>为什么要改：</strong>这条条件针对 MathComp 的 bigop→iter 结果；Lean 常数和未必产生该中间态。<br><strong>怎么改：</strong>按实际改写结果更新计划，只有目标确实出现 Function.iterate 才处理重复函数应用。</span>

   - <span style="color:gray">If the goal moved from `bigop` to `iter`</span>, update the plan before continuing.
7. Keep one stable normal form.

   <span style="color:red"><strong>为什么要改：</strong>避免表示来回切换可保留，灰色的两种具体表示属于旧 MathComp 路线。<br><strong>怎么改：</strong>换成当前采用的 Lean 求和及其实际结果，保留选定一种稳定表示的要求。</span>

   - Avoid oscillating between <span style="color:gray">`\sum_(i < n) x`, `iter n (addn x) 0`</span>, `x * n`, and `n * x` in the same branch.



## Bridge Lemma Strategy <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【帮助判断缺少的连接等式应该只在当前证明中使用，还是整理成可复用的引理。】</span>

<a id="lean-review-4"></a>



### Prefer a local bridge lemma when <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【说明什么时候只需为当前变量或分支证明一个小等式。｜中改】</span>
- The expression depends on a fixed local variable such as `t`, `cpu`, or a branch condition.
- A boolean-valued term becomes a constant over an index.
- The proof only needs the lemma once.


Template:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>为什么要改：</strong>原模板把 MathComp Bool 当自然数求和；已核实 Lean Classic 的 completed/pending/backlogged 返回 Bool，service_at 返回 Nat。<br><strong>怎么改：</strong>下面模板使用 (backlogged ...).toNat；导入 Prosa.Classic.Model.Schedule.Global.Basic.Schedule 并打开其 Schedule 子命名空间。这套接口显式传 job_arrival/job_cost，不与 Prosa.Behavior 实例版混用。</span>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>证明固定时刻的 backlog 值在所有处理器上的和，等于该值乘处理器数。<br><strong>2）怎么换成 Lean 代码：</strong>局部证明改用 have ... := by；Lean 需将 Bool 显式变成 Nat；每项相同，直接化简常数和即可，省去真假分类与 iter 步骤。沿用上面的 Classic 接口并 open scoped BigOperators：<code style="white-space:pre-wrap">have cpu_sum_of_backlogged (t : Nat) :&#10;    (∑ _cpu : Fin num_cpus, (backlogged job_arrival job_cost sched j t).toNat) =&#10;      (backlogged job_arrival job_cost sched j t).toNat * num_cpus := by&#10;  simp [Nat.mul_comm]</code>。本文件通用片段按 Lean 4.33.1/锁定 Mathlib 核过；业务前提仍需原上下文，升级后复核，示意变量不是库接口。</span>

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



### Prefer a generic bridge lemma when <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【说明什么时候值得把反复使用的求和等式整理成通用引理。｜中改】</span>
- The same normalization gap appears in multiple proofs.
- The goal has already become a literal constant sum.


Template:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>为什么要改：</strong>常数和在 Lean 已有现成化简，不必为了重现 MathComp iter 新建 helper。<br><strong>怎么改：</strong>先查 Finset.sum_const/Finset.card_eq_sum_ones，仅在反复复用时提取下面的辅助引理。</span>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把“x 加 n 次等于 x × n”做成可复用的辅助定理。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 的 Fin n 表示 n 个索引，常数和可直接化简，不必经过 iter：<code style="white-space:pre-wrap">theorem sum_const_fin_nat (n x : Nat) :&#10;    (∑ _i : Fin n, x) = x * n := by&#10;  simp [Nat.mul_comm]</code>。sum_const_fin_nat 是建议新建的本地名，不是已有 Mathlib API。</span>

```coq
Lemma big_const_ord_muln n x :
  \sum_(i < n) x = x * n.
Proof.
  by rewrite big_const_ord iter_addn mulnC.
Qed.
```

<span style="color:red"><strong>为什么要改：</strong>链接指向的 .v 模板不能直接作为 Lean 可编译资源。<br><strong>怎么改：</strong>迁移时将 assets/bridge-lemma-templates.v 换为 .lean，补实际 imports，经 lake env lean 验证后更新链接；本轮只记录任务。</span>

More ready-to-copy templates are in [bridge-lemma-templates](./assets/bridge-lemma-templates.v).

<a id="lean-review-6"></a>



## Bigop Endgame Discipline <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【安排求和证明的收尾顺序，先整理内部项，再处理外层求和和乘法。｜重改】</span>

<span style="color:red"><strong>为什么要改：</strong>先稳定内层再处理外层的顺序可保留，具体规则须匹配 Lean 的 List/Finset 表示，而不是套用 SSReflect bigop。<br><strong>怎么改：</strong>Finset 重排、常数和、拆和分别查 sum_comm、sum_const、sum_add_distrib；List/Prosa 封装使用其实际定义与对应定理。</span>

<span style="color:gray">For ssreflect big operator proofs</span>, use this order.

1. Exchange or rearrange sums only while the goal is still clearly a big operator.
2. Collapse branch-local constant sums.

<span style="color:red"><strong>为什么要改：</strong>MathComp 的 Bool-as-Nat 在 Lean 要显式表达；常数和可直接化简，不必固定另造局部桥接。<br><strong>怎么改：</strong>Bool 用 .toNat。已核实 Prosa.Util.Sum.sumSeq s F = (s.map F).sum、sumFiltered s P F = ((s.filter P).map F).sum；过滤常数 1 转计数可用 <code style="white-space:pre-wrap">simp [Prosa.Util.Sum.sumFiltered, List.countP_eq_length_filter]</code>。</span>

3. <span style="color:gray">Introduce local bridge lemmas for boolean-as-nat constants</span>.

<span style="color:red"><strong>为什么要改：</strong>big_distrr 是 MathComp 的分配引理，不能原名调用；先稳定内层的原则不变。<br><strong>怎么改：</strong>Finset 求和的右乘分配用 Finset.sum_mul，左乘用 Finset.mul_sum，按实际乘法方向选择。</span>

4. Use <span style="color:gray">`big_distrr`</span> or similar outer distribution only after inner normalization is stable.

<span style="color:red"><strong>为什么要改：</strong>mulnC 是 MathComp 引理名，需要替换为 Lean 声明。<br><strong>怎么改：</strong>使用 Nat.mul_comm。</span>

5. Use algebraic rewrites such as <span style="color:gray">`mulnC`</span> only when multiplication is literally present.

<a id="lean-review-7"></a>



## When To Switch To Count Bridging <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【说明什么时候问题已经从求和恒等式变成对象个数的上界，需要转到计数 skill。｜中改】</span>

<span style="color:red"><strong>为什么要改：</strong>这里用 iter 指代旧 MathComp 规范化阶段，不能假定 Lean 也会经历它。<br><strong>怎么改：</strong>按真实求和表示和改写结果界定本 skill 的范围。</span>

This skill handles generic big-operator, <span style="color:gray">`iter`</span>, and multiplication mismatches.

<span style="color:red"><strong>为什么要改：</strong>目的 skill 的 MathComp 计数接口及 Bool/Prop reflection 流程不能直接用于 Lean。<br><strong>怎么改：</strong>同步迁移计数 skill 的实际接口与反射步骤，业务声明仍须核实。</span>

If the branch has clearly become a counting proof, switch to [ssreflect-count-bridging](./skill_count.md) instead of staying here.

High-signal cues for switching:

<span style="color:red"><strong>为什么要改：</strong>这两条触发条件中的旧 MathComp 名称需更新；指标和计数是同一数量的判断可保留，Nat.min 本身也是 Lean 名称。<br><strong>怎么改：</strong>以 List.countP、过滤后的 length/card、Finset.sum_boole、Bool.toNat 与 Nat.min 识别，不按旧引理名搜索。</span>

- <span style="color:gray">the branch mixes `big_mkcond`, `sum1_count`, `big_filter`, `count`, and `Nat.min` or `minn`</span>
- the same quantity appears both as `if P x then 1 else 0` and as a <span style="color:gray">`count`</span>
- the endgame is no longer a pure big-operator identity, but a bound on how many elements satisfy a predicate

<span style="color:red"><strong>为什么要改：</strong>按下一条定理是否需要计数或数量界分流可保留；灰色层级名称来自旧库表示。<br><strong>怎么改：</strong>改按实际 List/Finset 求和、计数或基数定理分流，避免仅因旧名称出现就切换。</span>

- the next intended theorem lives in the <span style="color:gray">`count`</span> or `min` layer rather than in the generic <span style="color:gray">`bigop` or `iter`</span> layer

Use this generic skill only up to the point where the proof class is clear. Once the branch is really about indicator-sum to count normalization, the count-bridging skill has the stricter pipeline.

<a id="lean-review-8"></a>



## Side-Specific Normalization <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【展示怎样只改写等式的一侧，让它与另一侧或下一条定理的写法一致。】</span>
Sometimes the cleanest fix is to rewrite only one side into the other side’s syntax.

Example:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>只把等式右侧恢复成求和，保留左侧结构。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 不使用 [in RHS]- 语法。已有 hSum : 求和 = 乘法 时，改用 <code style="white-space:pre-wrap">conv =&gt;&#10;  rhs&#10;  rw [←hSum]</code>；是否恢复求和取决于后续定理，不为照搬 Coq iter 路线而恢复。</span>

```coq
rewrite [in RHS]-big_const_ord.
```

<span style="color:red"><strong>为什么要改：</strong>Lean 常数和未必出现 MathComp iter，不能把规避这个旧中间态当作恢复求和的固定理由。<br><strong>怎么改：</strong>只有后续定理需要求和表示时才反向改写，沿用上方已核实的局部等式。</span>

Use this when the goal is naturally a big operator and <span style="color:gray">forcing the other side into multiplication would create an unstable `iter` intermediate</span>.

<a id="lean-review-9"></a>



## Common Failure Signatures <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【把常见改写报错对应到当前表达式可能尚未完成的整理步骤。｜重改】</span>
See [failure-signatures](./references/failure-signatures.md) for a mapping from common error messages to the missing normalization step.

Short version:

<span style="color:red"><strong>为什么要改：</strong>这条“Coq 报错→iter 状态”映射描述的是旧调用，不能证明 Lean 的失败原因。<br><strong>怎么改：</strong>读取实际 Lean 目标；Finset.sum_const 后可能是 card • x，再用 simp [Nat.mul_comm] 化简。</span>

- <span style="color:gray">`Unable to unify "X * n" with "iter n (addn X) 0"` means the goal is still in `iter` form</span>.

<span style="color:red"><strong>为什么要改：</strong>这两条错误串使用 Coq/MathComp 的声明和诊断形式，不能直接匹配 Lean。<br><strong>怎么改：</strong>按实际 Lean diagnostic 和目标重建对应条目；乘法相关声明使用 Nat.one_mul/Nat.mul_comm。</span>

- <span style="color:gray">`The LHS of mul1n ... does not match any subterm`</span> means there is no literal `1 * _` yet.
- <span style="color:gray">`The LHS of mulnC ... does not match any subterm`</span> means there is no multiplication node yet, or not the one you think.

<span style="color:red"><strong>为什么要改：</strong>旧 ordinal bigop 形状及其报错不等于 Lean 的索引表示，不能据此决定如何拆项。<br><strong>怎么改：</strong>先区分索引；Fin 拆首项用 Fin.sum_univ_succ，range 拆末项用 Finset.sum_range_succ。</span>

- <span style="color:gray">`The LHS of big_ord_recr ... does not match any subterm` means the goal is no longer a standard ordinal big operator head</span>.

<span style="color:red"><strong>为什么要改：</strong>这里引用的是 Coq 执行时的错误消息，迁移后需取得 Lean 的实际 diagnostic。<br><strong>怎么改：</strong>重建相应 Lean 错误条目，不把旧字符串直接作为触发器。</span>

- <span style="color:gray">`No applicable tactic`</span> after several rewrites usually means the proof drifted across multiple normal forms without a stable bridge.

<span style="color:red"><strong>为什么要改：</strong>这一转交条件依赖 MathComp 关键词，不能直接识别 Lean 计数任务。<br><strong>怎么改：</strong>改看实际计数表示及下一条计数/上界定理；真正进入计数证明后再转交。</span>

<span style="color:gray">If the branch now mentions `big_mkcond`, `sum1_count`, filtered sums of ones, or `count` bounds</span>, stop here and switch to [ssreflect-count-bridging](./skill_count.md). That is no longer a generic bigop mismatch; it is a counting-normalization proof.

<a id="lean-review-10"></a>



## Anti-Patterns <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出会让表达式来回变形、却没有推进证明的常见改写习惯。｜中改】</span>


- Do not rewrite because two expressions are mathematically equal if the target lemma does not literally match the goal.

<span style="color:red"><strong>为什么要改：</strong>不盲串改写的原则可保留，灰色案例使用的是 MathComp 专属声明。<br><strong>怎么改：</strong>换成 Finset.sum_const、Finset.sum_mul、Nat.mul_comm 等实际案例；每步查看目标，目标明确时可用 simp [已知定义]。</span>

- Do not chain <span style="color:gray">`big_const_ord`, `iter_addn`, `mul1n`, and `mulnC`</span> blindly without checking the intermediate goal.
- Do not use a generic arithmetic lemma when a branch-local bridge lemma is simpler and more robust.
- Do not switch normal forms repeatedly inside one proof branch.

<a id="lean-review-11"></a>



## Minimal Debug Log <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【提供记录表，写清当前式子、打算用的等式以及改写后的实际结果。】</span>
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



## Success Condition <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【说明怎样确认每次改写都在朝选定的表达式前进。】</span>


The proof is on track when each rewrite is justified by a literal syntactic match, and every bridge lemma moves the branch toward a single stable normal form instead of introducing another oscillation.