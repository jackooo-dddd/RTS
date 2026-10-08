<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>一个证明卡住了，但还不知道它属于分支、参数、改写还是别的问题时，先用这份通用指导。它规定遇到失败后按什么顺序检查，以及怎样保留已经完成的工作。<br><strong>具体例子：</strong>你刚加入几行证明，系统随后报出多条错误。后面的错误可能是第一处错误导致的：例如一个局部结论没有成功建立，后续使用它的地方也就都失败了。如果同时修改很多位置，很难知道哪项修改真正有效。<br><strong>它会怎么处理：</strong>先查看当前目标和第一条可靠错误，只修改最小的一步，然后马上验证。成功的部分保存下来，失败时只撤回或修复相关部分。如果确认是特定问题，再使用处理分支、参数或计数的专门 skill。结束前还要检查负责的目标确实完成、没有用占位代替证明，而且通过检查的是最新版本。</span>

<span style="color:red">【Completion check｜首要结构性问题 1】<a href="#lean-review-6">点击跳转</a><br><strong>为什么会有结构性问题：</strong>这一节要确认“当前版本的证明真的完成，而且没有占位”。原规则使用 Coq 的结束命令和验证方式；Lean 没有 Qed.，占位写法及检查结果也不同，例如含 sorry 的声明可能带着警告通过编译。无占位并不是 Lean 才有的要求，问题是旧的识别与验收方式不能直接确认 Lean 是否满足这个要求。<br><strong>Lean 中大致怎么做：</strong>检查当前版本的 Lean 声明是否完成、是否仍依赖占位证明，并使用对应版本的后端验证结果。保留原来的完整性要求，换成能识别 Lean 声明和证明状态的检查方式。 <a href="https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/">Lean 官方说明</a>。</span>

<span style="color:red">【Scope and proof integrity｜首要结构性问题 2】<a href="#lean-review-2">点击跳转</a><br><strong>为什么会有结构性问题：</strong>这项机制要识别“允许修改的证明从哪里开始、到哪里结束”。Lean 的证明写在声明内部，还能嵌套局部证明和分支，没有 Coq 的 Proof./Qed. 起止命令。如果旧工具依靠这些命令划定区域，就无法正确定位 Lean 的证明范围；仅改写区域里的代码解决不了这个问题。<br><strong>Lean 中大致怎么做：</strong>根据 Lean 的语法结构和源码位置识别声明、证明体及局部块，再沿用原来的编辑权限：只改获准的证明范围，保护定理前提和相邻声明。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-2">Scope and proof integrity</a>；<a href="#lean-review-3">Goal and branch discipline</a>；<a href="#lean-review-6">Completion check</a>。</span>

---
name: rocq-proof-methodology
#<span style="color:red">【description】建议改为“处理 Lean 4 证明中的目标、tactic、类型、分支、改写或未完成证明问题；在没有更具体的专门 skill 能直接处理时，使用通用的小步检查与恢复流程”。理由：将适用语言改为 Lean，同时保留通用入口和专门 skill 的分工。</span>
description: Use for general Rocq/Coq proof development and recovery when the blocker is a goal-state, tactic, typing, focus, rewrite, or incomplete-proof issue and no narrower domain skill already explains it.
---



# Rocq Proof Methodology <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【提供证明卡住时的通用处理顺序，并把具体问题交给合适的专门 skill。】</span>

Use this skill as a compact recovery loop, not as a second copy of the agent's proof policy. Prefer a narrower skill when the diagnostic already identifies a specific pattern such as goal focus, `by` expansion, failed lemma application, count/bigop bridging, or a known Prosa construction.

<a id="lean-review-1"></a>



## Core loop <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【规定每次只修一个可靠错误，小步验证并保留已经成功的部分。】</span>

<span style="color:red"><strong>实现层按需适配：</strong>若会话保存的是 Rocq 状态，应改由 Lean 后端读取同版本目标与诊断；例如 $/lean/plainGoal、textDocument/publishDiagnostics。不假定已有 lean_session 工具。</span>

1. Read the exact current goal and hypotheses from the live proof state.
2. Fix the first reliable error only: syntax/structure, then typing/unification, then tactic failure or unfinished goals.
3. Make one small proof-producing step or edit.


<span style="color:red"><strong>保留：</strong>小步验证、checkpoint 记录和只回退失败尾部的方法不变。<br><strong>实现层按需适配：</strong>用 lake env lean 验证对应版本的 Lean 源码。</span>

4. Re-run the smallest relevant goal/checkpoint validation.
5. Persist a validated step in the proof file or roll back only its failing tail.

Do not respond to a failed step with an unrelated broad search. A targeted lookup is justified when the current goal or compiler error names the missing definition, lemma shape, instance, or premise; use its result in the next proof attempt.

<a id="lean-review-2"></a>



## Scope and proof integrity <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【限定允许修改的证明范围，并要求保持定理前提和证明完整性。】</span>

- Keep edits inside the currently owned theorem or proof_region.
- Preserve compiler-certified prefixes and current transaction state.

<span style="color:red"><strong>为什么要改：</strong>灰色的 Axiom、Parameter、Hypothesis、Variable、Admitted. 是 Coq 的声明或结束写法，不能作为 Lean 的对应语法直接使用；admit 两边都有。<br><strong>怎么改：</strong>按 Lean 的 axiom/variable/sorry 等实际形式检查；禁止新增前提或占位充当证明的政策保留，合法既有前提也保留。</span>

- Do not introduce <span style="color:gray">`Axiom`</span>, <span style="color:gray">`Parameter`</span>, <span style="color:gray">`Hypothesis`</span>, <span style="color:gray">`Variable`</span>, `admit`, or <span style="color:gray">`Admitted.`</span> as a proof substitute. A runtime-authorized temporary skeleton is not final success.
- Do not change theorem assumptions or declarations to make the proof easier.

<span style="color:red"><strong>为什么要改：</strong>Lean 没有 Qed./Defined.，不能用这两个结束命令判断完成或透明性。<br><strong>怎么改：</strong>按用途选择 theorem/def，并检查实际声明范围。若旧区域解析器按 Proof./Qed. 定界，才替换其实现；原编辑权限和定理前提保护不变。</span>

- <span style="color:gray">Close a benchmark proof only with a real compiling `Qed.` (or `Defined.` when transparency is intentionally required).</span>

<a id="lean-review-3"></a>



## Goal and branch discipline <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【要求在改写、应用定理或切换分支后，确认当前目标仍然清楚。】</span>

- Inspect the goal after a tactic that rewrites, applies a lemma, introduces a local fact, or changes branches.

<span style="color:red"><strong>保留：</strong>先隔离分支、修复结构的纪律可以沿用。Lean 4.33.1 也支持花括号 tactic 块；应核对局部声明的连接语法，而不是把括号本身判为不兼容。</span>

- Use bullets or `{ ... }` to isolate multiple focused goals. Repair focus/brace structure before changing semantic tactics.

<span style="color:red"><strong>为什么要改：</strong>这里的 compressed by 原指 SSReflect 执行后要求收尾的写法；Lean by 是证明块入口，不能删除它来展开。<br><strong>怎么改：</strong>保留 by，拆开内部步骤查看目标；局部事实以 have ... := by 连接证明。</span>

- If a <span style="color:gray">compressed `by ...`</span> hides the failure, expand only that boundary and inspect the first revealed goal.
- For dependent rewrite errors, first consider `subst` for a variable equality, or revert/generalize dependent hypotheses before rewriting.

<a id="lean-review-4"></a>



## Choosing the next step <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【根据当前需要证明的内容，选择改写、逻辑推理、局部结论或算术等动作。】</span>

Choose tactics from the actual goal shape; this is guidance, not a mandatory route:

<span style="color:red"><strong>为什么要改：</strong>当前 Lean 4.33.1/Mathlib 未提供 reflexivity、cbn 这两个同名 tactic；前者用于自反，后者用于定义化简。<br><strong>怎么改：</strong>按实际目标选 rfl 或 dsimp 等对应机制，不把两种任务混成一个动作。</span>

- definitional equality: <span style="color:gray">`reflexivity`</span>, <span style="color:gray">`cbn`</span>, or a small unfold;

<span style="color:red"><strong>为什么要改：</strong>split 在 Lean 中存在，但用于 if/match 分析，不是这里的合取构造。<br><strong>怎么改：</strong>合取目标用 constructor；本行其余同名逻辑动作按实际目标使用。</span>

- available hypothesis or constructor: `exact`, `assumption`, `apply`, `constructor`, <span style="color:gray">`split`</span>, `left`, `right`;

<span style="color:red"><strong>为什么要改：</strong>f_equal 和 congruence 分别承担函数同余与等式闭包推理，本地 Lean 没有这些同名 tactic；不能把两者都当成一次改写。<br><strong>怎么改：</strong>函数同余可用 congrArg/congr，等式闭包按目标选择 grind 等机制。rewrite/subst 本身有 Lean 对应入口，不因同名强制改名。</span>

- equality transport: `rewrite`, `subst`, <span style="color:gray">`f_equal`</span>, <span style="color:gray">`congruence`</span>;

<span style="color:red"><strong>为什么要改：</strong>assert、suff、pose proof 是 Coq 的局部事实语法，不能按原写法交给 Lean。<br><strong>怎么改：</strong>按用途使用 have 或 suffices；本行 have、set 在 Lean/Mathlib 也有对应入口，具体参数和证明连接按 Lean 核实。</span>

- local bridge: `have`, <span style="color:gray">`assert`</span>, <span style="color:gray">`suff`</span>, <span style="color:gray">`pose proof`</span>, or `set`;

<span style="color:red"><strong>保留：</strong>本地 Lean 4.33.1 已核实 lia 可用，Mathlib 也有 ring；这里“按数值域选择已导入求解器”的规则可保留，不要求只因迁移就把 lia 改成 omega。</span>

- arithmetic: use the imported solver appropriate to the domain, such as `lia` or `ring`;

<span style="color:red"><strong>为什么要改：</strong>auto/eauto 的深度参数及 hint database 属于 Coq 的搜索配置，不能直接成为 Lean 的搜索设置。<br><strong>怎么改：</strong>保留有界、前提明确的搜索原则，按实际 Lean tactic 配置事实集与搜索范围。</span>

- bounded search: <span style="color:gray">`auto n`</span> or <span style="color:gray">`eauto n`</span> only when the relevant <span style="color:gray">hint database</span> and premises are understood.



<span style="color:red"><strong>为什么要改：</strong>灰色标记的是 SSReflect 重复改写语法；工作区的禁用政策不会因语言迁移而自动取消。<br><strong>怎么改：</strong>需要约束 Lean 具体操作时，按同一政策写清对应语法与允许范围。</span>

Do not use ssreflect repeat-rewrite syntax <span style="color:gray">`rewrite !...`</span> or <span style="color:gray">`rewrite -!...`</span> in this environment.

<span style="color:red"><strong>为什么要改：</strong>intuition 是原工作区明确禁用的旧工具名，不能据此扩大为禁止所有 Lean 自动化。<br><strong>怎么改：</strong>保留明确写出逻辑步骤的要求；若约束 Lean 的具体工具，按同一政策写清允许范围。</span>

Do not use <span style="color:gray">`intuition`</span>; construct the logical steps explicitly.

<a id="lean-review-5"></a>



## Candidate lemma audit <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【在使用一个引理前，检查它的结论、参数和全部前提是否适合当前目标。】</span>



Before committing to an imported lemma:

<span style="color:red"><strong>保留：</strong>检查类型和前提的规则不变。<br><strong>实现层按需适配：</strong>若探针使用 Coq 的参数实例化、统一结果，应在当前 Lean 上下文重新核实。</span>

1. inspect its exact type;
2. unify its conclusion with the live target;
3. list the remaining premises and implicit instances;
4. check whether each premise follows from current hypotheses or an already certified local bridge;
5. abandon or change the instantiation when a required premise is unavailable.

<span style="color:red"><strong>保留：</strong>只在证据改变后重试的规则不变。<br><strong>实现层按需适配：</strong>若失败记录使用 Coq 的参数实例化、统一结果，应在当前 Lean 上下文重新核实；fingerprint/certificate 概念与字段不必因此改名。</span>

A verified failed lemma/missing-premise route must not be repeated through cosmetic edits or an `admit_id` rename. It may be reconsidered after a new hypothesis is derived, the missing premise is compiled, the instantiation genuinely changes, or the audit is shown wrong.

<a id="lean-review-6"></a>



## Completion check <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【在报告成功前，确认最新版本中的负责目标已完成，而且没有留下占位证明。】</span>

Before reporting success, verify:

- the current owned goal is closed;

<span style="color:red"><strong>保留：</strong>两边都须满足原有无占位要求。<br><strong>实现层按需适配：</strong>可检查 Lean 声明依赖中的 sorryAx；普通非占位警告不自动判失败。</span>

- no proof placeholder remains in the owned theorem;


<span style="color:red"><strong>为什么要改：</strong>coqc 验证 Coq 源码，不能验证 Lean；checkpoint 作为项目验证记录的概念可保留。<br><strong>怎么改：</strong>改用当前版本的 Lean 编译与诊断。</span>

- the authoritative staged revision, not an older disk copy, passes checkpoint/<span style="color:gray">coqc</span>;
- all opened branches and local assertions are closed;

<span style="color:red"><strong>为什么要改：</strong>这里的 terminator 承接前文 Qed./Defined.，Lean 没有对应结束命令。<br><strong>怎么改：</strong>按实际声明和证明范围确认完成，保持原编辑权限及验收范围。</span>

- <span style="color:gray">the final theorem terminator</span> is correct for the assigned ownership layer.

If the proof still fails, return the exact stable goal/error, the smallest failed step, missing premises, and which certified prefix remains reusable.
