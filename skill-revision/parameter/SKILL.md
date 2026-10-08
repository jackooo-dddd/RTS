<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>你找到了一个似乎能解决当前目标的定理，但系统拒绝使用它，甚至还没列出需要你补证哪些条件。这个 skill 帮你检查：是定理要讨论的对象还没确定，还是对象已确定、只剩一些事实需要证明。<br><strong>具体例子：</strong>你想用一个响应时间上界定理。使用它时，既要确定“是哪种任务、采用哪种调度策略”，也要证明“这个调度满足要求、干扰量没有超过给定限制”。如果调度策略本身还不明确，系统可能连“这个策略满足要求”具体指什么都无法确定；这时继续补后面的证明，未必能解决当前错误。<br><strong>它会怎么处理：</strong>它指导你查看定理的真实参数和系统期待的类型，只补充当前确实无法推断的对象或设置，再尝试应用定理。等系统列出需要证明的条件后，就逐项使用已有结论或继续证明。目的是避免盲目填写一长串参数，也避免把“没选定对象”误当成“又缺了一条数学结论”。具体如何判断和应用，需要使用对应证明语言的规则。</span>

<span style="color:red">【Core Distinction｜首要结构性问题 1】<a href="#lean-review-1">点击跳转</a><br><strong>为什么会有结构性问题：</strong>这一节区分“定理要用哪个对象还没确定”和“对象已确定，但条件还没证明”。旧判断依赖 Coq 定理导出的参数顺序，以及应用定理时在哪里报错；Lean 的声明接口和推断结果不保证相同。同一个参数在 Coq 中需要先补，不代表 Lean 中也要手填，因此不能沿用旧顺序决定缺什么。<br><strong>Lean 中大致怎么做：</strong>查看 Lean 定理的真实参数及当前应用结果，区分缺少对象、实例还是证明前提。只补确实推断不出的信息，其余条件作为待证目标逐项完成。两种语言都有参数推断，这里需要更新的是判断依据。 <a href="https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference">Lean 官方说明</a>。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-3">Failure Signals</a>；<a href="#lean-review-8">Early-Bound Example</a>；<a href="#lean-review-9">Final-Theorem Example</a>。</span>

<span style="color:red">【Rocq 示例需转为 Lean 代码｜点击跳转】<a href="#lean-review-code-1">示例 1</a>；<a href="#lean-review-code-2">示例 2</a>；<a href="#lean-review-code-3">示例 3</a>；<a href="#lean-review-code-4">示例 4</a>；<a href="#lean-review-code-5">示例 5</a>；<a href="#lean-review-code-6">示例 6</a>；<a href="#lean-review-code-7">示例 7</a>；<a href="#lean-review-code-8">示例 8</a>；<a href="#lean-review-code-9">示例 9</a>；<a href="#lean-review-code-10">示例 10</a>。共 10 个原代码块，全部保留。</span>

---
name: coq-goal-driven-apply
#<span style="color:red">【description】建议改为“处理 Lean 定理应用中的参数或实例推断失败，区分尚未确定的对象与待证明的前提；按真实声明补充必要的命名参数或局部实例，再用 apply/refine 暴露剩余目标”。理由：Lean 的参数接口和推断结果需重新检查，不能照搬 Coq 的参数顺序和报错分类。</span>
description: Distinguish postponable proof obligations from non-postponable early-bound implicit parameters, section arguments, policies, and typeclass instances in Coq and Rocq theorem application. In this failure mode, do not use exact of a fully explicit theorem term as a workaround. Use when apply or eapply fails before ordinary subgoals appear and Coq reports uninstantiated existentials or instance-construction errors, or when you are tempted to write a long exact (@lemma ...) call.
argument-hint: '[theorem name] [goal shape or early-binding error]'
user-invocable: true
---



# Coq Goal-Driven Apply for Early-Bound Arguments <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【帮助查明定理为什么用不上，并区分需要先选定的参数与可以稍后证明的条件。】</span>

<span style="color:red"><strong>为什么要改：</strong>参数未定而应用失败在 Lean 中也会发生；这里灰色只表示更换后端，不能把整种问题判为失效。<br><strong>怎么改：</strong>从实际 Lean 声明与诊断判断缺什么，不照抄旧 Coq 调用结论。</span>

Use this skill for one failure mode only: an exported lemma looks applicable, but <span style="color:gray">Coq</span> cannot even produce the ordinary proof obligations because some implicit parameter, section argument, policy, or typeclass instance has not been fixed yet.

<a id="lean-review-1"></a>



## Core Distinction <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【区分“定理要讨论哪个对象还没确定”和“对象已确定但还有条件没证明”。｜轻改】</span>

There are two very different kinds of missing information.

<span style="color:red"><strong>为什么要改：</strong>区分待证前提和确实阻塞的数据可保留；这两行的后端名称和 apply:/eapply 是旧执行入口。<br><strong>怎么改：</strong>使用 Lean apply/refine 留下普通目标；可推断参数留隐式，确实缺失时补命名参数或已有实例。refine Nat.le_trans (m := b) ?_ ?_ 可给中间数并保留两项证明。</span>

- Postponable proof obligations: ordinary premises that appear as subgoals after <span style="color:gray">`apply:` or `eapply`</span>. These should stay postponed.
- Early-bound arguments or instances: values <span style="color:gray">Coq</span> must know before the theorem term is well-typed. These cannot be postponed.

<span style="color:red"><strong>为什么要改：</strong>此处记录的是 Coq 的应用状态，Lean 版需更换状态来源。<br><strong>怎么改：</strong>读取当前 Lean 目标和 diagnostic；保留先检查应用失败原因的顺序。</span>

If <span style="color:gray">Coq</span> has not produced ordinary subgoals yet, do not treat the problem as just another premise to prove later.

<a id="lean-review-2"></a>



## What Must Be Fixed First <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出可能影响后续条件含义的参数，帮助判断哪些信息需要先补齐。｜中改】</span>



An implicit argument or instance must be fixed first if it does one of the following:

<span style="color:red"><strong>为什么要改：</strong>Instance 是原 Coq 声明语法；Lean 同样有实例和参数次序，但接口需按真实声明核对。<br><strong>怎么改：</strong>已核实 Prosa.Analysis.Abstract.Definitions 下的 Interference、InterferingWorkload 是 class；用 #synth 检查、letI 注册已有值。policy/readiness 余项仍按实际 API 确认，不新增假设。</span>

- determines a local <span style="color:gray">`Instance`</span> used in the theorem statement
- fixes the policy that later hypotheses are typed over

<span style="color:red"><strong>为什么要改：</strong>这里涉及 Coq 当前声明的参数依赖；Lean 定理的实际导出接口需重新核对。<br><strong>怎么改：</strong>按 Lean 的 #check/#print 检查参数及其依赖，不复制旧例的位置。</span>

- appears in the type of later hypotheses, so <span style="color:gray">Coq</span> cannot state those hypotheses until the binder is chosen
- selects the `Interference`, `InterferingWorkload`, readiness, or policy layer in which the conclusion lives

<a id="lean-review-3"></a>



## Failure Signals <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出应用定理时的典型错误，帮助发现参数或实例没有选对的情况。｜重改】</span>

Use this skill when goal-driven apply fails with signals like these:

<span style="color:red"><strong>为什么要改：</strong>这两条错误文本来自 Coq，不能直接作为 Lean 的固定故障签名。<br><strong>怎么改：</strong>按实际 Lean diagnostic 重建分类，并查看真实期望类型及 #check/#synth 结果。</span>

- <span style="color:gray">`Not enough uninstantiated existential variables.`</span>
- <span style="color:gray">`Constant does not build instances of a declared type class.`</span>

<span style="color:red"><strong>为什么要改：</strong>期望数据却收到证明仍是有效线索；此处只更换后端和实际类型证据。<br><strong>怎么改：</strong>读取 Lean 的 expected/actual type，核实是否传参错位，不把普通证明硬填到策略或实例的位置。</span>

- <span style="color:gray">Coq</span> expects a policy, instance, or data argument, but your next term is a proof hypothesis.
- A proof term such as `REFLEXIVE_JLFP` or `WORK_BEARING` is being read as if it should fill a non-`Prop` binder.



These are early-binding failures. They are not ordinary missing premises.

<a id="lean-review-4"></a>



## Procedure <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【给出先尝试应用、查看缺失信息、最少补参、再处理剩余条件的顺序。｜中改】</span>

1. Shape the local goal first.

<span style="color:red"><strong>为什么要改：</strong>先应用、检查首个无法推断项、最少补参的流程可保留；这三步须换成 Lean 调用和当前状态。<br><strong>怎么改：</strong>用 apply/refine 尝试，并以 #check/#synth 检查真实缺项；Lean 同样有声明参数次序，不能沿用旧例的位置。</span>

2. Try <span style="color:gray">`apply:` or `eapply`</span> exactly once.
3. If <span style="color:gray">Coq</span> exposes ordinary subgoals, stop. Those goals are postponable. Keep them postponed.
4. If <span style="color:gray">Coq</span> fails before ordinary subgoals appear, inspect the theorem source and identify the earliest non-inferable binder or instance.

<span style="color:red"><strong>为什么要改：</strong>补必要信息再重试可保留，但固定回到 Coq apply:/eapply 的执行形式不能直接搬到 Lean。<br><strong>怎么改：</strong>必要时用命名参数或 letI，再 apply/refine；后续步骤读取 Lean 实际目标，普通前提出现后逐项证明。</span>

5. Add only that earliest binder or instance explicitly, <span style="color:gray">while keeping the theorem application in `apply:` or `eapply` form</span>.
6. Re-run <span style="color:gray">`apply:` or `eapply`</span>.
7. Once <span style="color:gray">Coq</span> starts exposing ordinary subgoals, switch back to postponed-proof mode and do not keep filling parameters.

<a id="lean-review-5"></a>



## Hard Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【说明原 skill 为什么反对靠猜测一长串参数来绕过定理应用失败。】</span>



For this failure mode, `exact (@lemma ...)` is prohibited as a repair strategy.

<span style="color:red"><strong>为什么要改：</strong>下列规则里的 apply:/eapply 属于旧 Coq 执行写法。<br><strong>怎么改：</strong>未来 Lean 版换成相应的 apply/refine 调用，并核对实际定理参数。</span>

- Do not replace a failed or nearly working <span style="color:gray">`apply:` or `eapply`</span> with a fully explicit theorem term.
- Do not use `exact (@lemma ...)` just to force <span style="color:gray">Coq</span> past unresolved policies, instances, or generalized binders.
- If <span style="color:gray">`apply:` or `eapply`</span> already exposes ordinary subgoals, then the explicit `exact (@lemma ...)` form is strictly worse and should be rejected.



The reason is procedural, not stylistic: a long explicit term bypasses obligation discovery. It turns a goal-driven proof into manual reconstruction of the theorem's exported binder order, instance placement, and policy choices.

<a id="lean-review-6"></a>



## Preferred Application Style <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【展示如何让当前目标帮助确定定理参数，并把未证明的条件留出来逐项处理。】</span>

<span style="color:red"><strong>为什么要改：</strong>让目标帮助推断参数、暴露剩余前提的方法可保留；此处更换的是后端。<br><strong>怎么改：</strong>读取 Lean 实际生成的目标，具体调用使用下方已核实的声明。</span>

When the theorem head is already the right one, keep the application implicit and let <span style="color:gray">Coq</span> expose the remaining obligations.

Prefer:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>应用主定理，列出前提，再用已有假设处理能直接完成的部分。<br><strong>2）怎么换成 Lean 代码：</strong>由目标推断参数并暴露前提的方法可保留；eapply/all: try done 是待替换的 Coq 调用写法。导入并打开 Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta，先 #check 下述定理，再用 <code style="white-space:pre-wrap">apply uniprocessor_response_time_bound_restricted_supply_seq&#10;all_goals try assumption</code>；参数不明时补经核实的缺项。通用片段按 Lean 4.33.1/锁定 Mathlib 核过，业务证明仍需上下文，版本变化后复核；示意变量不是库接口。</span>

```coq
eapply uniprocessor_response_time_bound_restricted_supply_seq.
all: try done.
```

or:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>用简短写法应用主定理，尝试关闭容易的前提。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 没有 apply: ... => // 这组简写。沿用上一段主定理调用，已有事实用 assumption/exact，仅差定义时用 simp only [实际定义]。</span>

```coq
apply: uniprocessor_response_time_bound_restricted_supply_seq => //.
```

Then solve the exposed goals one by one.

Avoid replacing a nearly working application with a full explicit term such as:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>以长位置参数调用展示参数或实例错位的风险。<br><strong>2）怎么换成 Lean 代码：</strong>Coq 的 Task H ... 顺序不能直接当作 Lean 接口。正确对照使用前述定理及经 #check 核实的 (Task := Task)、(Job := Job)、(PState := PState) 等必要参数，剩余前提交给 goals；后文固定返回 apply:/eapply 改为合适的 Lean apply/refine。</span>

```coq
exact (@uniprocessor_response_time_bound_restricted_supply_seq
   Task H ...
   INTRA_BOUNDED R SOL_SEQ_RS
   j ARR TSK).
```



That style is brittle because it forces you to guess generalized binder order, policy choices, and instance placement all at once. One small drift in a threshold instance, interference instance, or policy coercion can make the entire term ill-typed.

<span style="color:red"><strong>为什么要改：</strong>修复首个阻塞项后重试可保留，固定返回 apply:/eapply 是旧执行形式。<br><strong>怎么改：</strong>改为合适的 Lean apply/refine，并从新结果决定是否还缺其他信息。</span>

If one early-bound item really must be fixed first, add only that item and then <span style="color:gray">return immediately to `apply:` or `eapply`</span>. Do not keep expanding the theorem term.

<a id="lean-review-7"></a>



## Postponable Example <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【用一个上界证明展示，哪些前提可以等应用定理后再单独证明。】</span>

<a id="lean-review-code-4"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>先证明非抢占片段的界，再用它证明 service-inversion 的界。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 的证明块和两条定理接口需重新匹配。导入 Prosa.Analysis.Facts.BlockingBound.Fp 与 Prosa.Analysis.Facts.BusyInterval.ServiceInversion；分别 #check 其中 nonpreemptive_segments_bounded_by_blocking、service_inversion_is_bounded。两段改为 have ... := by，用 intro/apply，并在匹配前提上 exact H_pi_bounded；其他条件由原上下文证明。</span>

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



## Early-Bound Example <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【用调度策略和干扰模型展示，某些对象未确定时为什么后面的条件也无法明确。】</span>

This is an existing-context pattern, not code to add to the benchmark file.
If the surrounding file or imported library already provides:

<span style="color:red"><strong>为什么要改：</strong>旧上下文清单不等于 Lean 的实例环境；策略命题仍是证明，数据实例另行注册。<br><strong>怎么改：</strong>导入并打开 Prosa.Analysis.Abstract.Definitions 与 Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation；JLFP_policy 来自 Prosa.Model.Priority.Definitions。用已有值注册 <code style="white-space:pre-wrap">letI : JLFP_policy Job := JLFP&#10;letI : Interference Job := rs_jlfp_interference arr_seq sched&#10;letI : InterferingWorkload Job := rs_jlfp_interfering_workload arr_seq sched</code>；两个派生函数已核实，后者仍需原有 [JobCost Job]，不能新造成本假设。</span>

```text
JLFP : JLFP_policy Job
H_priority_is_reflexive : reflexive_job_priorities JLFP
rs_jlfp_interference : Interference Job
rs_jlfp_interfering_workload : InterferingWorkload Job
H_policy_respects_sequential_tasks : policy_respects_sequential_tasks JLFP
```

then a target such as:

<a id="lean-review-code-5"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>要求已选的干扰模型和工作量模型与任务顺序执行一致。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 目标依赖上面注册的实例；旧参数位置不能用于接入证明。核实的声明是 <code style="white-space:pre-wrap">Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk</code>；需要消歧时按实际声明补 (Task := Task)，而非往数据位置塞 SI_BOUNDED。</span>

```coq
interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk
```


may require fixing the policy or instance arguments before ordinary proof
premises appear.

<span style="color:red"><strong>为什么要改：</strong>Context/Hypothesis/Parameter/Variable 是原声明语法；“不制造新前提”的约束在 Lean 中仍成立。<br><strong>怎么改：</strong>迁移对应声明写法，但不通过新增 variable/axiom 凑出任务原本没有的假设。</span>

Do not introduce new <span style="color:gray">`Context`, `Hypothesis`, `Parameter`</span>, or
<span style="color:gray">`Variable`</span> declarations to manufacture these arguments.


In this shape, `JLFP` and the induced `Interference` and `InterferingWorkload` instances are not later proof obligations.

<span style="color:red"><strong>为什么要改：</strong>“Coq 必须先知道”描述旧调用要求，不能据此断定 Lean 在同一时点也无法继续。<br><strong>怎么改：</strong>核对当前声明和实例搜索；确需现有实例时用上方 letI 注册，不把普通证明当作数据。</span>

<span style="color:gray">Coq must know them before it can form the instantiated theorem term.</span> If they are still ambiguous, do not start filling later premises such as `SI_BOUNDED` or workload bounds. First fix the missing policy or instance, then re-run the theorem application.

<a id="lean-review-9"></a>



## Final-Theorem Example <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【以最终响应时间定理为例，比较手填全部参数与让系统列出剩余条件的写法。】</span>

Suppose the final goal already matches a theorem head like
`uniprocessor_response_time_bound_restricted_supply_seq` and the remaining work is to supply facts such as schedule validity, bounded interference, a valid SBF, and a recurrence solution.

Preferred script:

<a id="lean-review-code-6"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>应用最终定理，把调度、供应界和递推条件留成待证目标。<br><strong>2）怎么换成 Lean 代码：</strong>将 Coq 两行换成前面 Preferred Application Style 的 Lean 调用；all_goals try assumption 只处理已有假设能关闭的部分，其余条件用 · 分支继续证明。</span>

```coq
eapply uniprocessor_response_time_bound_restricted_supply_seq.
all: try done.
```

Then inspect the remaining goals and solve them using the local facts you already named.

If the proof can be driven by a line such as:

<a id="lean-review-code-7"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>用短调用让目标帮助推断主定理参数。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 的参数接口需先核实，不能沿用 Coq 的位置顺序。采用前述 apply 调用，仅补确实缺失的命名参数。</span>

```coq
apply: uniprocessor_response_time_bound_restricted_supply_seq; try done.
```

then a fully explicit `exact (@uniprocessor_response_time_bound_restricted_supply_seq ...)` term is not merely verbose. In this skill, it is the wrong move and should be removed.

Do not jump directly to:

<a id="lean-review-code-8"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展示把调度、供应界与任务条件混填到长参数列表的反例。<br><strong>2）怎么换成 Lean 代码：</strong>这份 Coq 顺序不能直接当作 Lean 接口；arm_sbf 也未核实为同名 Lean API。反例按真实接口重建，修复时仅具名补缺失的 arr_seq、sched、tsk、R 等参数；完整检查见后面的具体调用。</span>

```coq
exact (@uniprocessor_response_time_bound_restricted_supply_seq
   Task H ...
   ABSTRACT_WORK_CONSERVING H_sequential_tasks I_AND_W_SEQUENTIAL
   L BUSY_INTERVALS_BOUNDED (arm_sbf Π Θ ν)
   RS_VALID_BUSY_SBF_ARM ARM_SBF_UNIT
   ...
   j ARR TSK).
```

<span style="color:red"><strong>为什么要改：</strong>此处引用 Coq 的义务与导出参数信息；Lean 版需要自己的声明及状态。<br><strong>怎么改：</strong>换用实际 Lean 定理的参数接口和当前 proof state。</span>

In this situation, a long explicit term is not helping <span style="color:gray">Coq</span> discover obligations. It is bypassing obligation discovery and making you manually reconstruct the theorem's full exported binder order.

Concrete replacement example:

<a id="lean-review-code-9"></a>

<span style="color:red"><strong>1）这段代码在干嘛：</strong>展示最终定理所需的实例、数据和证明前提，区分三者的供给方式。<br><strong>2）怎么换成 Lean 代码：</strong>不能假定 Lean 接口逐项沿用这份长位置表；尤其 SBF 是 SupplyBoundFunction 结构值，supply_bound_function 才是数值函数字段。实例先按上文 letI/#synth 核实，包括 TaskRunToCompletionThreshold、JobPreemptable、MaxArrivals；数据按真实参数名给出，证明留成 apply/refine 的 goals。rs_jlfp_* 沿用前例，ARM/阈值构造须另查实际声明，所有输入来自原上下文。</span>

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

<span style="color:red"><strong>1）这段代码在干嘛：</strong>用短调用代替长位置列表，将剩余条件明确留出来证明。<br><strong>2）怎么换成 Lean 代码：</strong>Lean 改用前述 apply 与 all_goals try assumption；剩余目标按实际 Lean 定理前提继续证明。</span>

```coq
apply: uniprocessor_response_time_bound_restricted_supply_seq; try done.
```

<span style="color:red"><strong>为什么要改：</strong>这里以 Coq 从目标实例化定理；Lean 版需使用其实际调用和生成的目标。<br><strong>怎么改：</strong>替换后端名称，核对 Lean 定理应用的结果。</span>

This shorter script is stronger because it lets <span style="color:gray">Coq</span> recover the instantiated theorem head from the goal and generate only the real remaining obligations.

<a id="lean-review-10"></a>



## Anti-Patterns <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【列出容易把参数错误越修越复杂的做法，例如继续猜位置或盲目补后面的证明。｜轻改】</span>

- Do not respond to early-binding errors by writing a full `@lemma ...` term.

<span style="color:red"><strong>为什么要改：</strong>灰色调用使用 Coq 的 apply:/eapply、分号串联和 try done。<br><strong>怎么改：</strong>换为相应 Lean apply/refine 与 all_goals try assumption；使用实际声明中的参数名。</span>

- Do not replace a good <span style="color:gray">`apply:` or `eapply`</span> candidate with `exact (@lemma ...)` just because some parameters are still unresolved.
- Do not keep an `exact (@uniprocessor_response_time_bound_restricted_supply_seq ...)` script once <span style="color:gray">`apply: uniprocessor_response_time_bound_restricted_supply_seq; try done.`</span> works.
- Do not fill later proof premises when the theorem term itself is still ambiguous.
- Do not treat a typeclass-construction failure as evidence that more `Prop` goals should be proved.
- Do not keep adding explicit arguments after the first missing policy or instance has been identified.

<a id="lean-review-11"></a>



## Output Expectations <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【规定诊断结果应写清缺哪个参数、为什么缺它，以及下一步具体补什么。｜中改】</span>

When using this skill, explain proof choices in this order:

<span style="color:red"><strong>为什么要改：</strong>先说明是否出现普通目标的报告顺序可保留；旧 Coq 运行结果不能充当 Lean 当前状态的证据。<br><strong>怎么改：</strong>报告实际 Lean 错误与目标、缺项及原因、最小修复和重试结果。</span>

1. whether <span style="color:gray">Coq</span> already exposed ordinary proof obligations
2. which binder or instance must be fixed first
3. why that item is not a postponable proof premise
4. what minimum explicit information should be added now
5. when it is safe to return to postponed-proof mode
