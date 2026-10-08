<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>你找到了一个似乎能解决当前目标的定理，但系统拒绝使用它，甚至还没列出需要你补证哪些条件。这个 skill 帮你检查：是定理要讨论的对象还没确定，还是对象已确定、只剩一些事实需要证明。<br><strong>具体例子：</strong>你想用一个响应时间上界定理。使用它时，既要确定“是哪种任务、采用哪种调度策略”，也要证明“这个调度满足要求、干扰量没有超过给定限制”。如果调度策略本身还不明确，系统可能连“这个策略满足要求”具体指什么都无法确定；这时继续补后面的证明，未必能解决当前错误。<br><strong>它会怎么处理：</strong>它指导你查看定理的真实参数和系统期待的类型，只补充当前确实无法推断的对象或设置，再尝试应用定理。等系统列出需要证明的条件后，就逐项使用已有结论或继续证明。目的是避免盲目填写一长串参数，也避免把“没选定对象”误当成“又缺了一条数学结论”。具体如何判断和应用，需要使用对应证明语言的规则。</span>

<span style="color:red">【Lean迁移总评】区分实例/数据与证明前提、最小化显式信息的方法可保留；参数阻塞判据、应用策略及 Prosa 导出接口需重审。整体重写力度：中重。</span>

<span style="color:red">【Core Distinction｜首要结构性问题 1】<a href="#lean-review-1">点击跳转</a><br><strong>原来在做什么：</strong>应用大定理时，先区分“任务类型、调度策略等对象还没选定”和“对象已选定、但前提未证明”，让 Coq 的 apply/eapply 暴露能稍后证明的条件。<br><strong>改哪里：</strong>判断何者必须先给值的分类标准、apply/eapply 的选择规则，以及按 Coq 导出位置补参数的指导。<br><strong>为什么：</strong>Lean 从目标、实参和实例搜索推断缺失信息，apply/refine 如何留下目标也要按 Lean 实际行为判断。Coq 中“尚未产生子目标，所以先填此参数”的结论，不能直接用于 Lean。仅翻译长调用仍会留下错误分类器。<br><strong>替换（Rocq → Lean）：</strong>按 #check 实际定理 → 必要时 #synth 所需实例 → (参数名 := 已有值)/letI → apply 或 refine ... ?_ → 逐个证明目标的顺序处理。本地已核实主定理和 rs_jlfp_* 实例函数，按正文全名与真实 binder 使用。<br><strong>删除（仅未来 Lean 版）：</strong>旧 Coq 导出参数位置及报错时机不再直接作为 Lean 的分类依据；Hard Rule 中针对该失败模式一律拒绝完整显式项的策略，需按真实 Lean 调用重新评估。<br><strong>保留：</strong>只补确实无法推断的信息，不制造前提；普通证明义务可以留待后续完成。<br><a href="https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference">Lean 官方说明</a>。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-1">Core Distinction</a>；<a href="#lean-review-2">What Must Be Fixed First</a>；<a href="#lean-review-3">Failure Signals</a>；<a href="#lean-review-4">Procedure</a>；<a href="#lean-review-5">Hard Rule</a>；<a href="#lean-review-8">Early-Bound Example</a>；<a href="#lean-review-9">Final-Theorem Example</a>；<a href="#lean-review-10">Anti-Patterns</a>。</span>

<span style="color:red">【Rocq 示例需转为 Lean 代码｜点击跳转】<a href="#lean-review-code-1">示例 1</a>；<a href="#lean-review-code-2">示例 2</a>；<a href="#lean-review-code-3">示例 3</a>；<a href="#lean-review-code-4">示例 4</a>；<a href="#lean-review-code-5">示例 5</a>；<a href="#lean-review-code-6">示例 6</a>；<a href="#lean-review-code-7">示例 7</a>；<a href="#lean-review-code-8">示例 8</a>；<a href="#lean-review-code-9">示例 9</a>；<a href="#lean-review-code-10">示例 10</a>。共 10 个原代码块，全部保留。</span>

---
name: coq-goal-driven-apply
description: Distinguish postponable proof obligations from non-postponable early-bound implicit parameters, section arguments, policies, and typeclass instances in Coq and Rocq theorem application. In this failure mode, do not use exact of a fully explicit theorem term as a workaround. Use when apply or eapply fails before ordinary subgoals appear and Coq reports uninstantiated existentials or instance-construction errors, or when you are tempted to write a long exact (@lemma ...) call.
argument-hint: '[theorem name] [goal shape or early-binding error]'
user-invocable: true
---

<span style="color:red">【Frontmatter｜中改】<br><strong>改哪里：</strong>frontmatter 的 name、description、Coq 报错触发，以及针对本失败模式拒绝完整显式定理项的策略。<br><strong>为什么：</strong>Lean 的实际参数与实例接口需重新核对；应按应用结果判断是缺信息还是缺证明，不能把原场景中的长显式项禁令扩大成 Lean 语法禁令。<br><strong>替换（Rocq → Lean）：</strong>name 建议改为 lean-goal-driven-apply；description 改为“应用失败时检查 Lean 的显式/隐式/实例参数，使用命名参数、局部实例或 refine 暴露剩余义务”。以下通用片段已按本地 Lean 4.33.1 / 项目锁定的 Mathlib 核对；完整业务证明仍需目标上下文。h、xs、P 等是局部变量，不是新库接口。<br><strong>删除（仅未来 Lean 版）：</strong>移除 Coq 报错签名作为 Lean 固定触发条件的用法。<br><strong>保留：</strong>不靠猜测长位置列表绕过失败；原文限制的是这个修复场景，并非禁止所有 exact/@。</span>

# Coq Goal-Driven Apply for Early-Bound Arguments

<span style="color:red">【Coq Goal-Driven Apply for Early-Bound Arguments｜重改】<br><strong>本节在做什么：</strong>帮助查明定理为什么用不上，并区分需要先选定的参数与可以稍后证明的条件。<br><strong>改哪里：</strong>标题下的入口条件：以“尚未产生普通子目标”判定 early-bound 失败。<br><strong>为什么：</strong>在 Lean 中该现象不能单独说明缺少哪个参数；需区分类型不匹配、元变量未确定和实例合成失败。<br><strong>替换（Rocq → Lean）：</strong>入口先用 <code style="white-space:pre-wrap">#check Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq</code> 读取真实声明；Interference 实例失败时用 <code style="white-space:pre-wrap">#synth Prosa.Analysis.Abstract.Definitions.Interference Job</code>；已经生成普通目标时按目标分别证明。<br><strong>删除（仅未来 Lean 版）：</strong>不再把“尚未产生普通子目标”单独作为分类依据；应由实际类型/实例诊断支持。<br><strong>保留：</strong>应用失败时先查缺少什么信息，再决定补参数还是补证明。</span>

Use this skill for one failure mode only: an exported lemma looks applicable, but Coq cannot even produce the ordinary proof obligations because some implicit parameter, section argument, policy, or typeclass instance has not been fixed yet.

<a id="lean-review-1"></a>

<span style="color:red">【Core Distinction｜重改｜需重设分类标准】<br><strong>本节在做什么：</strong>区分“定理要讨论哪个对象还没确定”和“对象已确定但还有条件没证明”。<br><strong>改哪里：</strong>Core Distinction 的两类缺失信息，以及判断哪些参数确实无法推迟的依据。<br><strong>为什么：</strong>Lean 可以用目标、后续实参或期望类型推断依赖参数；参数是否依赖其他参数不足以判断它能否留待推断。<br><strong>替换（Rocq → Lean）：</strong>分类改为：普通证明前提 → apply/refine 后逐个证明；目标能推断的参数 → 留隐式；仍不确定的数据/实例 → (参数名 := 值) 或 letI。例如 <code style="white-space:pre-wrap">refine Nat.le_trans (m := b) ?_ ?_</code> 明确中间数，同时留下两项证明。<br><strong>删除（仅未来 Lean 版）：</strong>旧 Coq 调用中“尚不能生成前提”的结论不直接用于同名 Lean 声明；必须重新确认是哪个参数或实例无法推断。<br><strong>保留：</strong>对象/实例的选择与命题前提的证明需要区分；两种语言都有这类区别。</span>

## Core Distinction

There are two very different kinds of missing information.

- Postponable proof obligations: ordinary premises that appear as subgoals after `apply:` or `eapply`. These should stay postponed.
- Early-bound arguments or instances: values Coq must know before the theorem term is well-typed. These cannot be postponed.

If Coq has not produced ordinary subgoals yet, do not treat the problem as just another premise to prove later.

<a id="lean-review-2"></a>

<span style="color:red">【What Must Be Fixed First｜重改】<br><strong>本节在做什么：</strong>列出可能影响后续条件含义的参数，帮助判断哪些信息需要先补齐。<br><strong>改哪里：</strong>What Must Be Fixed First 的四条提前绑定判据及 Coq Section/local Instance 的参数对应。<br><strong>为什么：</strong>Lean 声明的显式、隐式和实例隐式参数不承诺沿用 Coq 导出位置；能从目标推断的项无需手填。<br><strong>替换（Rocq → Lean）：</strong>按 #check/#print 的实际 binder 查参；在同一上下文用 #synth 查实例。已核实 Prosa.Analysis.Abstract.Definitions.Interference 与 InterferingWorkload 均是 class；已有实例值用 letI 注册。policy、readiness 等余项需要根据 Lean Prosa 当前实际 declaration/API 确认。<br><strong>删除（仅未来 Lean 版）：</strong>不再将 Coq Section 的参数顺序和依赖关系直接作为 Lean 提前补参的判据。<br><strong>保留：</strong>缺失数学前提继续证明，不新增 variable/axiom 制造条件。</span>

## What Must Be Fixed First

An implicit argument or instance must be fixed first if it does one of the following:

- determines a local `Instance` used in the theorem statement
- fixes the policy that later hypotheses are typed over
- appears in the type of later hypotheses, so Coq cannot state those hypotheses until the binder is chosen
- selects the `Interference`, `InterferingWorkload`, readiness, or policy layer in which the conclusion lives

<a id="lean-review-3"></a>

<span style="color:red">【Failure Signals｜重改】<br><strong>本节在做什么：</strong>列出应用定理时的典型错误，帮助发现参数或实例没有选对的情况。<br><strong>改哪里：</strong>Failure Signals 的两条 Coq 英文报错及“这些都是 early-binding”的结论。<br><strong>为什么：</strong>Lean 使用自己的 diagnostics；同样的应用失败也可能由类型或参数位置错误造成，不能复用旧字符串分类。<br><strong>替换（Rocq → Lean）：</strong>未知名称 → #check 全限定名 并核对 import；类型不匹配 → 比较 expected/actual type；实例合成失败 → #synth 实例类型；未解决目标 → 查看剩余目标。若连带发生改写匹配失败，trace_state 后检查改写式与位置。英文串按实际 Lean 版本采集。定理若期望 JLFP_policy Job 却收到证明，按 #check 显示的 binder 改成命名传参。<br><strong>删除（仅未来 Lean 版）：</strong>去掉用旧 Coq 字符串识别 Lean，以及“没有子目标就能断定缺数据”的结论。<br><strong>保留：</strong>不要把证明假设硬塞到数据/策略参数的位置。</span>

## Failure Signals

Use this skill when goal-driven apply fails with signals like these:

- `Not enough uninstantiated existential variables.`
- `Constant does not build instances of a declared type class.`
- Coq expects a policy, instance, or data argument, but your next term is a proof hypothesis.
- A proof term such as `REFLEXIVE_JLFP` or `WORK_BEARING` is being read as if it should fill a non-`Prop` binder.

These are early-binding failures. They are not ordinary missing premises.

<a id="lean-review-4"></a>

<span style="color:red">【Procedure｜重改】<br><strong>本节在做什么：</strong>给出先尝试应用、查看缺失信息、最少补参、再处理剩余条件的顺序。<br><strong>改哪里：</strong>Procedure 的步骤 2/6（应用语法）、4（定位阻塞信息）、5（补参方式）。<br><strong>为什么：</strong>Lean 应按真实 binder 与实例合成结果选择参数；eapply/apply: 的语法及“最早位置”规则不能直接移植。<br><strong>替换（Rocq → Lean）：</strong>apply:/eapply → apply 定理 或 refine (定理 ... ?_)；步骤 4 用 #check/#synth；步骤 5 只补确认必要的 (Task := Task)、(PState := PState) 等命名参数，或 letI 注册已有实例。正常前提用 ·/case 分支证明。<br><strong>删除（仅未来 Lean 版）：</strong>原步骤 4—6 中按 Coq 导出位置选择最早不可推断参数、固定返回 apply:/eapply 的操作序列，改用上述 Lean 声明检查与 apply/refine 流程。<br><strong>保留：</strong>先看目标、最少补参、重新检查义务；不靠新假设制造输入。</span>

## Procedure

1. Shape the local goal first.
2. Try `apply:` or `eapply` exactly once.
3. If Coq exposes ordinary subgoals, stop. Those goals are postponable. Keep them postponed.
4. If Coq fails before ordinary subgoals appear, inspect the theorem source and identify the earliest non-inferable binder or instance.
5. Add only that earliest binder or instance explicitly, while keeping the theorem application in `apply:` or `eapply` form.
6. Re-run `apply:` or `eapply`.
7. Once Coq starts exposing ordinary subgoals, switch back to postponed-proof mode and do not keep filling parameters.

<a id="lean-review-5"></a>

<span style="color:red">【Hard Rule｜重改｜需重审而非改 tactic 名】<br><strong>本节在做什么：</strong>说明原 skill 为什么反对靠猜测一长串参数来绕过定理应用失败。<br><strong>改哪里：</strong>Hard Rule 在“这一失败模式”下禁止完整 exact (@lemma ...) 修复的策略及其理由。<br><strong>为什么：</strong>Lean exact 使用目标的期望类型，refine 可以同时给命名参数并留下 ?_；显式传参本身不会必然绕过义务发现。<br><strong>替换（Rocq → Lean）：</strong>规则改成“禁止未经核对地猜长位置参数；允许与 #check 声明一致的命名参数、exact/refine”。允许的例子：<code style="white-space:pre-wrap">refine Nat.le_trans (m := b) ?_ ?_&#10;· exact hAB&#10;· exact hBC</code>；@ 只在确需暴露隐式参数且已核对全部 binder 时使用。<br><strong>删除（仅未来 Lean 版）：</strong>不直接移植“在这一失败模式下一律拒绝完整显式项”的策略；根据实际 Lean 声明和剩余义务判断。原文没有禁止所有场景的 exact/@，也不能把它解释成这种语法禁令。<br><strong>保留：</strong>拒绝靠猜测一长串位置参数掩盖真正缺失的信息。</span>

## Hard Rule

For this failure mode, `exact (@lemma ...)` is prohibited as a repair strategy.

- Do not replace a failed or nearly working `apply:` or `eapply` with a fully explicit theorem term.
- Do not use `exact (@lemma ...)` just to force Coq past unresolved policies, instances, or generalized binders.
- If `apply:` or `eapply` already exposes ordinary subgoals, then the explicit `exact (@lemma ...)` form is strictly worse and should be rejected.

The reason is procedural, not stylistic: a long explicit term bypasses obligation discovery. It turns a goal-driven proof into manual reconstruction of the theorem's exported binder order, instance placement, and policy choices.

<a id="lean-review-6"></a>

<span style="color:red">【Preferred Application Style｜中改】<br><strong>本节在做什么：</strong>展示如何让当前目标帮助确定定理参数，并把未证明的条件留出来逐项处理。<br><strong>改哪里：</strong>Preferred Application Style 中 eapply/apply:、all: try done、=> // 及主定理的引用。<br><strong>为什么：</strong>Lean 的 tactic 语法和实例参数不同；try 没报错不代表所有义务已完成。<br><strong>替换（Rocq → Lean）：</strong>导入 Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta；先 <code style="white-space:pre-wrap">#check Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq</code>，再 apply 完整定理名。缺 Task 等时补真实命名参数；all: try done → all_goals try assumption。对于 => //，已有前提用 exact/assumption，定义化简用 simp only [实际定义]。<br><strong>保留：</strong>让目标约束参数，应用后检查具体实例和剩余 goals。</span>

## Preferred Application Style

When the theorem head is already the right one, keep the application implicit and let Coq expose the remaining obligations.

Prefer:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>先应用主定理，让系统列出还需要证明的前提，再尝试用已有假设解决其中能直接完成的部分。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>eapply 主定理与 all: try done 两行。<br><strong>为什么：</strong>Lean 使用 apply 生成前提目标，并以 all_goals 遍历；assumption 只处理已有假设能够关闭的目标。<br><strong>替换（Rocq → Lean）：</strong>导入对应模块后换成 <code style="white-space:pre-wrap">apply Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq&#10;all_goals try assumption</code>；参数不明时只补 #check 已确认的命名参数或已有实例，再查看剩余 goals。<br><strong>保留：</strong>先暴露前提，再使用现有事实；try 返回不等于证明完成。</span>

```coq
eapply uniprocessor_response_time_bound_restricted_supply_seq.
all: try done.
```

or:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>用另一种短写法应用同一个主定理，并尝试立即完成容易的前提，留下其余目标逐个处理。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>apply: ... => // 这一条 SSReflect 简写。<br><strong>为什么：</strong>Lean 不使用这组 SSReflect 语法；应用定理、用假设收尾和定义化简需要按实际目标选择。<br><strong>替换（Rocq → Lean）：</strong>先 apply Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq；剩余目标若已有局部前提则 exact/assumption，若只差定义则 simp only [实际定义]。<br><strong>保留：</strong>先检查剩余目标，再决定如何关闭；不要把 // 无条件替成大范围自动化。</span>

```coq
apply: uniprocessor_response_time_bound_restricted_supply_seq => //.
```

Then solve the exposed goals one by one.

Avoid replacing a nearly working application with a full explicit term such as:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>这是一个反例：一次按位置填写主定理的所有参数和前提，容易把参数顺序或实例放错。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>作为反例的 exact (@主定理 Task H ...) 长位置参数项，以及它后面关于参数错位的解释。<br><strong>为什么：</strong>Lean 的 exact/@ 合法；真正的问题是未经核对地猜参数位置，而不是存在显式参数。<br><strong>替换（Rocq → Lean）：</strong>在真实声明支持这些 binder 时，正确对照写成 <code style="white-space:pre-wrap">apply (Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq (Task := Task) (Job := Job) (PState := PState))</code>，其余前提作为 goals 处理。<br><strong>删除（仅未来 Lean 版）：</strong>不把 Task H ... 的旧 Coq 位置顺序复制为 Lean 调用模板。<br><strong>保留：</strong>保留“盲填位置参数易错配”的反例用途。</span>

```coq
exact (@uniprocessor_response_time_bound_restricted_supply_seq
   Task H ...
   INTRA_BOUNDED R SOL_SEQ_RS
   j ARR TSK).
```

That style is brittle because it forces you to guess generalized binder order, policy choices, and instance placement all at once. One small drift in a threshold instance, interference instance, or policy coercion can make the entire term ill-typed.

If one early-bound item really must be fixed first, add only that item and then return immediately to `apply:` or `eapply`. Do not keep expanding the theorem term.

<a id="lean-review-7"></a>

<span style="color:red">【Postponable Example｜中改】<br><strong>本节在做什么：</strong>用一个上界证明展示，哪些前提可以等应用定理后再单独证明。<br><strong>改哪里：</strong>Postponable Example 的两个 have 证明及所引用的业务定理。<br><strong>为什么：</strong>Lean 局部证明语法、forall/fun 和导出参数需按真实声明重写；名称存在不代表前提与原模板逐项相同。<br><strong>替换（Rocq → Lean）：</strong>导入 Prosa.Analysis.Facts.BlockingBound.Fp 与 Prosa.Analysis.Facts.BusyInterval.ServiceInversion，分别 #check nonpreemptive_segments_bounded_by_blocking 与 service_inversion_is_bounded 的完整声明，再用 have H_pi_bounded : ... := by 和 have SI_BOUNDED : ... := by 证明所需局部界。<br><strong>保留：</strong>先建立局部上界，再把它作为主引理的前提。</span>

## Postponable Example

<a id="lean-review-code-4"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>先证明非抢占执行片段的上界，再用这个局部结论证明 service-inversion 的上界；这两项都是可以稍后补齐的证明前提。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>两段 have ... Proof. ... Qed.、move=>、exact:、apply: ... => //。<br><strong>为什么：</strong>这些是 Rocq/SSReflect 的证明块和引入语法；Lean 要在 := by 块中按实际前提引入变量、应用定理。<br><strong>替换（Rocq → Lean）：</strong>两段分别改为 have H_pi_bounded : ... := by 与 have SI_BOUNDED : ... := by。第一段用 intro 引入变量后应用 <code style="white-space:pre-wrap">Prosa.Analysis.Facts.BlockingBound.Fp.nonpreemptive_segments_bounded_by_blocking</code>；第二段 apply <code style="white-space:pre-wrap">Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_is_bounded</code>，在匹配的界前提上 exact H_pi_bounded。其他策略、合法调度等条件从原上下文逐个证明。<br><strong>保留：</strong>策略和合法调度等条件从原上下文证明，不通过新增假设制造输入。</span>

```coq
have H_pi_bounded :
   forall j0 t1 t2,
      arrives_in arr_seq j0 ->
      job_of_task tsk j0 ->
      busy_interval_prefix arr_seq sched j0 t1 t2 ->
      max_lp_nonpreemptive_segment arr_seq j0 t1 <=
         (fun _ => blocking_bound ts tsk) (job_arrival j0 - t1).
Proof.
   move=> j0 t1 t2 ARR0 TSK0 PREFIX.
   exact: nonpreemptive_segments_bounded_by_blocking.
Qed.

have SI_BOUNDED :
   service_inversion_is_bounded_by arr_seq sched tsk (fun _ => blocking_bound ts tsk).
Proof.
   apply: service_inversion_is_bounded => //.
   exact: H_pi_bounded.
Qed.
```

Here `H_pi_bounded` is a normal proof premise. It appears after the theorem application and can be discharged later. Do not make more parameters explicit.

<a id="lean-review-8"></a>

<span style="color:red">【Early-Bound Example｜重改】<br><strong>本节在做什么：</strong>用调度策略和干扰模型展示，某些对象未确定时为什么后面的条件也无法明确。<br><strong>改哪里：</strong>Early-Bound Example 中 JLFP 与派生 Interference/InterferingWorkload 的上下文接入方式，以及“必须提前确定”的判据。<br><strong>为什么：</strong>Lean 依实例隐式 binder 搜索这些对象；是否确实阻塞须看实际合成结果，不能依据 Coq 顺序判断。<br><strong>替换（Rocq → Lean）：</strong>导入 Prosa.Analysis.Abstract.Definitions、Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation，并 open 对应 namespace。已有 JLFP 策略值时用 <code style="white-space:pre-wrap">letI : JLFP_policy Job := JLFP</code> 注册；JLFP_policy 来自 Prosa.Model.Priority.Definitions，再按下面清单建立派生实例。<br><strong>保留：</strong>仅使用已有策略和输入，不添加新前提制造实例。</span>

## Early-Bound Example

This is an existing-context pattern, not code to add to the benchmark file.
If the surrounding file or imported library already provides:

<span style="color:red">【Early-Bound Example｜中改】<br><strong>改哪里：</strong>上下文清单中 rs_jlfp_interference、rs_jlfp_interfering_workload 的实例注册，以及策略命题和数据实例的区别。<br><strong>为什么：</strong>Lean 必须能在当前上下文找到已选的 class 实例；普通 Prop 证明不能代替数据实例，原 Coq 清单也不是 Lean binder 顺序。<br><strong>替换（Rocq → Lean）：</strong>已有 arr_seq/sched 时，派生实例改为 <code style="white-space:pre-wrap">letI : Interference Job := rs_jlfp_interference arr_seq sched&#10;letI : InterferingWorkload Job := rs_jlfp_interfering_workload arr_seq sched</code>。这两个函数已用 #check 核实；后者仍需要原有 [JobCost Job]。<br><strong>保留：</strong>其他策略命题保留为 Prop 假设；缺失成本条件需从原上下文取得，不能凭空新建。</span>

```text
JLFP : JLFP_policy Job
H_priority_is_reflexive : reflexive_job_priorities JLFP
rs_jlfp_interference : Interference Job
rs_jlfp_interfering_workload : InterferingWorkload Job
H_policy_respects_sequential_tasks : policy_respects_sequential_tasks JLFP
```

then a target such as:

<a id="lean-review-code-5"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展示一个待证明的条件：所选干扰和工作量模型要与任务的顺序执行方式一致。形成这个目标时，就必须知道使用哪套策略和实例。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>裸写的一致性目标名称及其依赖的局部实例。<br><strong>为什么：</strong>Lean 需要解析到真实声明并找到选定的 Interference/InterferingWorkload；不能沿用 Coq 位置填入 SI_BOUNDED 等证明。<br><strong>替换（Rocq → Lean）：</strong>在上面注册的实例下检查 <code style="white-space:pre-wrap">Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk</code>；需要消歧时按实际声明加 (Task := Task)。<br><strong>保留：</strong>把数据参数与普通证明前提分开；SI_BOUNDED 不能填到需要策略或实例的位置。</span>

```coq
interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk
```

may require fixing the policy or instance arguments before ordinary proof
premises appear. Do not introduce new `Context`, `Hypothesis`, `Parameter`, or
`Variable` declarations to manufacture these arguments.

In this shape, `JLFP` and the induced `Interference` and `InterferingWorkload` instances are not later proof obligations. Coq must know them before it can form the instantiated theorem term. If they are still ambiguous, do not start filling later premises such as `SI_BOUNDED` or workload bounds. First fix the missing policy or instance, then re-run the theorem application.

<a id="lean-review-9"></a>

<span style="color:red">【Final-Theorem Example｜重改】<br><strong>本节在做什么：</strong>以最终响应时间定理为例，比较手填全部参数与让系统列出剩余条件的写法。<br><strong>改哪里：</strong>Final-Theorem Example 对主定理导出参数、实例和 SBF 实参的解释。<br><strong>为什么：</strong>Lean 不保证保留 Coq 的位置顺序；SBF 是结构值，其数值函数字段不是同一类型。<br><strong>替换（Rocq → Lean）：</strong>导入 Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta 后 <code style="white-space:pre-wrap">#check Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq</code>；核对 TaskRunToCompletionThreshold、JobPreemptable、MaxArrivals 等实例，选定 Interference/InterferingWorkload 再 apply/refine。SBF 传 SupplyBoundFunction 的值，需要数值函数时才取 supply_bound_function 字段。<br><strong>保留：</strong>已有调度、干扰、供应界和递推解等事实仍须分别匹配真实前提。</span>

## Final-Theorem Example

Suppose the final goal already matches a theorem head like
`uniprocessor_response_time_bound_restricted_supply_seq` and the remaining work is to supply facts such as schedule validity, bounded interference, a valid SBF, and a recurrence solution.

Preferred script:

<a id="lean-review-code-6"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>应用最终定理，把调度、供应界和递推关系等要求变成可见的子目标，再尝试使用已有事实。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>eapply 主定理与 all: try done 这两行最终应用。<br><strong>为什么：</strong>Lean 的应用/遍历语法不同，try 不会保证消掉全部前提。<br><strong>替换（Rocq → Lean）：</strong>换为 <code style="white-space:pre-wrap">apply Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq&#10;all_goals try assumption</code>。剩余 schedule、SBF、recurrence 前提在 · 分支中用对应已有事实证明。<br><strong>保留：</strong>用实际剩余 goals 判断进度，而不是看 try 是否返回成功。</span>

```coq
eapply uniprocessor_response_time_bound_restricted_supply_seq.
all: try done.
```

Then inspect the remaining goals and solve them using the local facts you already named.

If the proof can be driven by a line such as:

<a id="lean-review-code-7"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>把主定理应用和简单前提的自动尝试压在同一行，目的是让系统从目标推断能推断的参数。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>apply: 主定理; try done 的单行调用。<br><strong>为什么：</strong>Lean 可用命名参数确定无法推断的数据，再独立处理产生的前提，无需靠位置填写所有事实。<br><strong>替换（Rocq → Lean）：</strong>核实 binder 后使用 <code style="white-space:pre-wrap">apply (Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq (Task := Task) (Job := Job) (PState := PState))&#10;all_goals try assumption</code>。如果仍缺参数，根据当前错误只补对应 binder。<br><strong>保留：</strong>短调用已经完成时，不再盲目展开成长位置列表；这条建议有具体场景，不扩大成禁止 Lean exact/@ 的通用规则。</span>

```coq
apply: uniprocessor_response_time_bound_restricted_supply_seq; try done.
```

then a fully explicit `exact (@uniprocessor_response_time_bound_restricted_supply_seq ...)` term is not merely verbose. In this skill, it is the wrong move and should be removed.

Do not jump directly to:

<a id="lean-review-code-8"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>这是另一个反例：把调度条件、供应界和任务条件都塞进很长的位置参数列表，手工承担了本可交给系统的参数匹配。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>含 arm_sbf、调度条件与供应界证明的长 exact 反例及其参数顺序。<br><strong>为什么：</strong>Coq 导出顺序不能说明 Lean 的参数位置；ARM 专用构造也未核实为 Lean 同名接口。<br><strong>替换（Rocq → Lean）：</strong>按实际 Lean 声明重建“盲填位置列表”的反例；正确对照用 (arr_seq := arr_seq)、(sched := sched)、(tsk := tsk)、(R := R) 等真实 binder，仅显式提供诊断确认缺失的项。<br><strong>删除（仅未来 Lean 版）：</strong>旧 Coq 参数位置表只留在评审原文中，不作为未来 Lean 版的调用说明。<br><strong>保留：</strong>参数类型/位置未经核对时，继续塞证明不能修复应用。</span>

```coq
exact (@uniprocessor_response_time_bound_restricted_supply_seq
   Task H ...
   ABSTRACT_WORK_CONSERVING H_sequential_tasks I_AND_W_SEQUENTIAL
   L BUSY_INTERVALS_BOUNDED (arm_sbf Π Θ ν)
   RS_VALID_BUSY_SBF_ARM ARM_SBF_UNIT
   ...
   j ARR TSK).
```

In this situation, a long explicit term is not helping Coq discover obligations. It is bypassing obligation discovery and making you manually reconstruct the theorem's full exported binder order.

Concrete replacement example:

<a id="lean-review-code-9"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展示上面长参数列表的具体样子：任务类型、处理器模型、实例、供应界和证明前提混在一起，需要分清哪些是参数、哪些是待证明条件。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>二十余项参数混在一起的完整 exact 调用，特别是 class 实例、数据参数和 Prop 前提三部分。<br><strong>为什么：</strong>Lean 的参数次序和实例搜索与 Coq 导出接口不同；阈值/ARM 等构造不能仅凭旧名称接入。<br><strong>替换（Rocq → Lean）：</strong>① 已有 class 实例通过 letI 注册、#synth 核实；② Task/Job/PState 及 arr_seq/sched/ts/tsk/L/SBF/task_intra_IBF/R 按实际 binder 名传参；③ 其余命题由 apply/refine 生成 goals 后逐一证明。rs_jlfp_* 两实例按 Early-Bound Example 接入；ARM/阈值构造先 #check 真实声明再使用。<br><strong>删除（仅未来 Lean 版）：</strong>去掉将原长位置列表直接用作 Lean 接口说明的做法。<br><strong>保留：</strong>实例和证明均从原上下文取得，不制造输入。</span>

```coq
exact (@uniprocessor_response_time_bound_restricted_supply_seq
   Task H (@limited_preemptions_rtc_threshold Task H H1)
   Job H2 H4 H3 (@limited_preemptive_job_model Job H5)
   PState H_uniprocessor_proc_model H_unit_supply_proc_model
   H_consumed_supply_proc_model arr_seq VALID_ARRIVALS
   sched JOBS_FROM_ARRIVAL_SEQUENCE JOBS_MUST_ARRIVE
   COMPLETED_JOBS_DONT_EXECUTE VALID_COSTS ts tsk H_tsk_in_ts
   VALID_PREEMPTION_MODEL VALID_RTCT H0 VALID_ARRIVAL_CURVE
   RESPECTS_MAX_ARRIVALS
   (rs_jlfp_interference arr_seq sched)
   (rs_jlfp_interfering_workload arr_seq sched)
   ABSTRACT_WORK_CONSERVING H_sequential_tasks I_AND_W_SEQUENTIAL
   L BUSY_INTERVALS_BOUNDED (arm_sbf Π Θ ν)
   RS_VALID_BUSY_SBF_ARM ARM_SBF_UNIT
   (fun _ F => blocking_bound ts tsk + total_ohep_request_bound_function_FP ts tsk F)
   INTRA_BOUNDED R SOL_SEQ_RS
   j ARR TSK).
```

should be replaced by:

<a id="lean-review-code-10"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>用短的定理应用替换上一段长参数列表，让系统推断参数，并将尚未证明的条件留成明确的子目标。<br><strong>2）怎么换成 Lean 代码：</strong><br><strong>改哪里：</strong>作为替换答案的 apply: 主定理; try done 单行代码及成功判据。<br><strong>为什么：</strong>Lean 版本需检查残留目标、元变量和实例错误；短代码或 try 不报错本身不等于证明完成。<br><strong>替换（Rocq → Lean）：</strong>改为 <code style="white-space:pre-wrap">apply Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq&#10;all_goals try assumption</code>；剩余递推解等前提保留为显式 · 分支。只有无剩余 goals、无未解决元变量/实例错误且声明通过检查时才完成。<br><strong>保留：</strong>不增加未声明原理来关闭前提。</span>

```coq
apply: uniprocessor_response_time_bound_restricted_supply_seq; try done.
```

This shorter script is stronger because it lets Coq recover the instantiated theorem head from the goal and generate only the real remaining obligations.

<a id="lean-review-10"></a>

<span style="color:red">【Anti-Patterns｜重改】<br><strong>本节在做什么：</strong>列出容易把参数错误越修越复杂的做法，例如继续猜位置或盲目补后面的证明。<br><strong>改哪里：</strong>Anti-Patterns 中针对失败修复的长 exact (@...) 限制，以及补出阻塞参数后回到目标驱动证明的要求。<br><strong>为什么：</strong>Lean 的显式参数与义务发现可以并存；所需显式信息可能不止一个，应以真实声明和诊断为准。<br><strong>替换（Rocq → Lean）：</strong>将这组操作落实为 Lean 的命名参数、letI 和 refine ... ?_：只补 #check/diagnostics 证实无法推断的信息，每次重新应用后再判断是否还需补参；一旦生成普通证明目标，就逐个完成这些目标。<br><strong>保留：</strong>不猜顺序、不在数据含糊时盲补后续证明、不新增 axiom 或改变定理前提。</span>

## Anti-Patterns

- Do not respond to early-binding errors by writing a full `@lemma ...` term.
- Do not replace a good `apply:` or `eapply` candidate with `exact (@lemma ...)` just because some parameters are still unresolved.
- Do not keep an `exact (@uniprocessor_response_time_bound_restricted_supply_seq ...)` script once `apply: uniprocessor_response_time_bound_restricted_supply_seq; try done.` works.
- Do not fill later proof premises when the theorem term itself is still ambiguous.
- Do not treat a typeclass-construction failure as evidence that more `Prop` goals should be proved.
- Do not keep adding explicit arguments after the first missing policy or instance has been identified.

<a id="lean-review-11"></a>

<span style="color:red">【Output Expectations｜中改】<br><strong>本节在做什么：</strong>规定诊断结果应写清缺哪个参数、为什么缺它，以及下一步具体补什么。<br><strong>改哪里：</strong>Output Expectations 的五项报告，尤其“Coq 是否已暴露义务”这一首要分类依据。<br><strong>为什么：</strong>Lean 报告必须说明实际缺失的 binder、普通 goals 或实例问题；原 Coq 阶段分类不能替代这些证据。<br><strong>替换（Rocq → Lean）：</strong>依次填写：① Lean diagnostic 与 remaining goals；② #check 确认的缺失 binder 名；③ #synth/类型核对结果及为何阻塞；④ 最小 (name := value)/letI 修改；⑤ 重新应用后剩余 Prop goals。<br><strong>删除（仅未来 Lean 版）：</strong>不再仅凭是否产生 subgoals 判定一定是 early-bound。<br><strong>保留：</strong>先说明缺什么及原因，再展示下一步具体修改。</span>

## Output Expectations

When using this skill, explain proof choices in this order:

1. whether Coq already exposed ordinary proof obligations
2. which binder or instance must be fixed first
3. why that item is not a postponable proof premise
4. what minimum explicit information should be added now
5. when it is safe to return to postponed-proof mode
