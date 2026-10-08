<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>一个证明卡住了，但还不知道它属于分支、参数、改写还是别的问题时，先用这份通用指导。它规定遇到失败后按什么顺序检查，以及怎样保留已经完成的工作。<br><strong>具体例子：</strong>你刚加入几行证明，系统随后报出多条错误。后面的错误可能是第一处错误导致的：例如一个局部结论没有成功建立，后续使用它的地方也就都失败了。如果同时修改很多位置，很难知道哪项修改真正有效。<br><strong>它会怎么处理：</strong>先查看当前目标和第一条可靠错误，只修改最小的一步，然后马上验证。成功的部分保存下来，失败时只撤回或修复相关部分。如果确认是特定问题，再使用处理分支、参数或计数的专门 skill。结束前还要检查负责的目标确实完成、没有用占位代替证明，而且通过检查的是最新版本。</span>

<span style="color:red">【Lean迁移总评】恢复循环、所有权和前提审计方法可保留；主要修改是 Lean 的 proof-state 工具、分支语义、区域边界及完成验收。整体重写力度：中。</span>

<span style="color:red">【Completion check｜首要结构性问题 1】<a href="#lean-review-6">点击跳转</a>：<br><strong>原来在做什么：</strong>最后检查当前证明是否真的完成、是否留有占位，以及验证的是不是最新版本。原文要求用 Coq 的检查点或编译器确认结果。<br><strong>改哪里：</strong>修改 Completion check 中的编译检查、占位识别和 checkpoint 验收。<br><strong>为什么：</strong>Lean 可以接受含 sorry 的声明并给出警告；旧 Coq 命令和占位检测无法证明迁移后的 Lean 声明完整。<br><strong>替换（Rocq → Lean）：</strong>coqc → 项目环境中的 lake env lean；Coq checkpoint → 绑定同一 staged revision 的 Lean 检查结果。<br><strong>删除（仅未来 Lean 版）：</strong>删除通过 Qed./Defined. 文本结束符判断 Lean 证明结束的规则；原有“无占位”检查必须保留。<br><strong>新增（Lean 适配）：</strong>接入 Lean diagnostics 和实际声明检查；对完整定理运行 #print axioms，核实无 sorryAx 占位依赖。普通非占位 warning 不自动判失败。<br><strong>保留：</strong>保留“最新版本、目标完成、没有占位”的要求；新增的是 Lean 证据采集实现，并非新的证明完整性原则。<br><a href="https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/">Lean 官方说明</a>。</span>

<span style="color:red">【Scope and proof integrity｜首要结构性问题 2】<a href="#lean-review-2">点击跳转</a>：<br><strong>原来在做什么：</strong>限定当前任务能修改哪一段证明，并确认它没有改到定理前提或相邻声明。原文还通过 Qed./Defined. 这样的 Coq 结束命令判断证明结束。<br><strong>改哪里：</strong>修改 Scope and proof integrity 中识别 proof_region 起止位置的实现。<br><strong>为什么：</strong>Lean 证明位于声明的 := by 块或证明项中，还可嵌套 have/case；不存在供旧解析器寻找的 Qed. 结束命令。<br><strong>替换（Rocq → Lean）：</strong>Proof./Qed. 文本分割 → Lean parser/elaborator 的 declaration/proof Syntax 源范围；锁定 theorem 的类型和 binders，仅授权证明项范围。<br><strong>删除（仅未来 Lean 版）：</strong>若旧解析器按 Proof./Qed. 结束关键字定界，移除该匹配逻辑；原文的权限政策本身保留。<br><strong>新增（Lean 适配）：</strong>为区域编辑工具接入 Lean 源位置及嵌套证明块归属；只翻译区域内 tactic 无法完成这项适配。<br><strong>保留：</strong>ownership 和“不改定理前提或相邻声明”的权限政策保留。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-2">Scope and proof integrity</a>；<a href="#lean-review-3">Goal and branch discipline</a>；<a href="#lean-review-6">Completion check</a>。</span>

---
name: rocq-proof-methodology
description: Use for general Rocq/Coq proof development and recovery when the blocker is a goal-state, tactic, typing, focus, rewrite, or incomplete-proof issue and no narrower domain skill already explains it.
---

<span style="color:red">【Frontmatter｜中改】<br><strong>改哪里：</strong>修改 frontmatter 的 name、description 语言范围和 by expansion 路由描述。<br><strong>为什么：</strong>Lean 的 by 是证明块入口，不能沿用 SSReflect 的“去掉 by”调试动作。<br><strong>替换（Rocq → Lean）：</strong>name 建议改为 lean-proof-methodology；description 的 Rocq/Coq → Lean 4；by expansion → “展开 by 块内部的 tactic”。<br><strong>保留：</strong>其余通用故障入口和 recovery loop 用途保留。</span>

# Rocq Proof Methodology

<span style="color:red">【Rocq Proof Methodology｜中改】<br><strong>本节在做什么：</strong>提供证明卡住时的通用处理顺序，并把具体问题交给合适的专门 skill。<br><strong>改哪里：</strong>修改通用入口向 goal、tactics、parameter 等专门 skill 的路由说明。<br><strong>为什么：</strong>技能名称可以相同，但 Lean 的分支、by 和参数推断语义不同；路由必须指向已迁移的规则。<br><strong>替换（Rocq → Lean）：</strong>路由写明 goal→分支归属，tactics→块内失败定位，parameter→参数/实例推断，math→表达式改写，count-bridging→计数转换，failure-signature→报错动作表；链接使用 ../对应目录/SKILL.md。<br><strong>新增（Lean 适配）：</strong>涉及业务引理的路由仍需根据 Lean Prosa 当前实际 declaration/API 确认。<br><strong>保留：</strong>保留“通用恢复优先，遇到专门问题再分流”的职责。</span>

Use this skill as a compact recovery loop, not as a second copy of the agent's proof policy. Prefer a narrower skill when the diagnostic already identifies a specific pattern such as goal focus, `by` expansion, failed lemma application, count/bigop bridging, or a known Prosa construction.

<a id="lean-review-1"></a>

<span style="color:red">【Core loop｜轻改】<br><strong>本节在做什么：</strong>规定每次只修一个可靠错误，小步验证并保留已经成功的部分。<br><strong>改哪里：</strong>修改 Core loop 的读取目标、获取诊断、小步验证和失败恢复的后端调用。<br><strong>为什么：</strong>Coq 会话状态不能供 Lean 继续执行；Lean LSP 的目标与诊断必须对应同一文档版本和位置。<br><strong>替换（Rocq → Lean）：</strong>Coq goal inspection → Lean LSP <code style="white-space:pre-wrap">$/lean/plainGoal</code>（URI/position）；Coq diagnostics → <code style="white-space:pre-wrap">textDocument/publishDiagnostics</code>；coqc → 项目根目录执行 <code style="white-space:pre-wrap">lake env lean path/to/File.lean</code>。<br><strong>删除（仅未来 Lean 版）：</strong>不再复用旧 Rocq 会话状态，也不把旧版本诊断当作新版本验证结果。<br><strong>新增（Lean 适配）：</strong>在会话封装中实现 didChange 同步新版本→等待同版本诊断→查询目标。保存 staged 文本；失败只恢复本次修改范围的先前文本并重检。这里需要实现适配器，不能假设已有 lean_session 工具。<br><strong>保留：</strong>先看真实目标、只修首个可靠错误、小步验证、保留进度的顺序保留；版本保存和回退本身是通用机制。</span>

## Core loop

1. Read the exact current goal and hypotheses from the live proof state.
2. Fix the first reliable error only: syntax/structure, then typing/unification, then tactic failure or unfinished goals.
3. Make one small proof-producing step or edit.
4. Re-run the smallest relevant goal/checkpoint validation.
5. Persist a validated step in the proof file or roll back only its failing tail.

Do not respond to a failed step with an unrelated broad search. A targeted lookup is justified when the current goal or compiler error names the missing definition, lemma shape, instance, or premise; use its result in the next proof attempt.

<a id="lean-review-2"></a>

<span style="color:red">【Scope and proof integrity｜重改｜需重设完成与边界契约】<br><strong>本节在做什么：</strong>限定允许修改的证明范围，并要求保持定理前提和证明完整性。<br><strong>改哪里：</strong>修改 proof_region 解析、占位检测和 Qed./Defined. 对应的声明选择规则。<br><strong>为什么：</strong>Lean 以声明及证明项范围组织证明；sorry 可生成带 sorryAx 依赖的声明；theorem/def 的透明性选择也不能由旧结束命令直接决定。<br><strong>替换（Rocq → Lean）：</strong>Coq 证明边界 → Lean declaration/proof Syntax 源范围；Axiom/Admitted/admit 检测 → Lean axiom、sorry、admit 及最终依赖里的 sorryAx 检查；按需要选择 theorem 或有意可展开的 def。<br><strong>删除（仅未来 Lean 版）：</strong>删除依靠 Qed./Defined. 判断 Lean 证明完成的规则；若现有区域解析器按 Proof./Qed. 定界，也要移除该匹配逻辑。<br><strong>新增（Lean 适配）：</strong>区域工具需识别 := by 与嵌套块；声明检查需返回占位依赖，而不能只报告编译进程成功。<br><strong>保留：</strong>proof_region/ownership、锁定类型和 binders、保留合法 variable 前提的政策不变。</span>

## Scope and proof integrity

- Keep edits inside the currently owned theorem or proof_region.
- Preserve compiler-certified prefixes and current transaction state.
- Do not introduce `Axiom`, `Parameter`, `Hypothesis`, `Variable`, `admit`, or `Admitted.` as a proof substitute. A runtime-authorized temporary skeleton is not final success.
- Do not change theorem assumptions or declarations to make the proof easier.
- Close a benchmark proof only with a real compiling `Qed.` (or `Defined.` when transparency is intentionally required).

<a id="lean-review-3"></a>

<span style="color:red">【Goal and branch discipline｜重改】<br><strong>本节在做什么：</strong>要求在改写、应用定理或切换分支后，确认当前目标仍然清楚。<br><strong>改哪里：</strong>修改 bullets/braces、删掉 by、split 和依赖假设处理的操作条目。<br><strong>为什么：</strong>Lean 用缩进和标签管理证明块；by 是必要的 tactic proof 入口，split 也不是合取构造的直接对应。<br><strong>替换（Rocq → Lean）：</strong>Coq bullets/braces → ·、case、局部 := by；删掉 by → 拆开块内 rw 或组合器；subst → Lean subst；依赖假设需退回时用 revert，改写后 intro；合取 split → constructor，分析 if/match 时才使用 Lean split。<br><strong>删除（仅未来 Lean 版）：</strong>旧 SSReflect by 边界的展开方式不再沿用；Lean 的 by 入口必须保留，调试只拆开内部步骤。<br><strong>保留：</strong>改写或应用定理后检查目标、必要时处理依赖假设的原则保留。</span>

## Goal and branch discipline

- Inspect the goal after a tactic that rewrites, applies a lemma, introduces a local fact, or changes branches.
- Use bullets or `{ ... }` to isolate multiple focused goals. Repair focus/brace structure before changing semantic tactics.
- If a compressed `by ...` hides the failure, expand only that boundary and inspect the first revealed goal.
- For dependent rewrite errors, first consider `subst` for a variable equality, or revert/generalize dependent hypotheses before rewriting.

<a id="lean-review-4"></a>

<span style="color:red">【Choosing the next step｜中改】<br><strong>本节在做什么：</strong>根据当前需要证明的内容，选择改写、逻辑推理、局部结论或算术等动作。<br><strong>改哪里：</strong>修改 Choosing the next step 中每类证明任务对应的 tactic 以及搜索配置。<br><strong>为什么：</strong>任务分类能保留，Coq tactic 语法和 auto/eauto 的 hint database 不能原样交给 Lean。<br><strong>替换（Rocq → Lean）：</strong>reflexivity→rfl；cbn→dsimp/simp only；rewrite h→rw [h]；rewrite -h→rw [←h]；f_equal→congrArg 或 congr；have/assert→have h : P := by；suff→suffices；pose proof→have h := proofTerm；Nat/Int 线性算术 lia→omega；ring→导入 Mathlib.Tactic 后使用 ring。逻辑构造仍可选择 exact/apply/constructor，定义等同可用 rfl/change/unfold，局部定义可用 let。<br><strong>删除（仅未来 Lean 版）：</strong>删除直接继承 Coq auto/eauto 深度和 hint database 配置的做法。<br><strong>新增（Lean 适配）：</strong>Lean 搜索规则可明确使用 solve_by_elim [h1,h2] 或逐个 apply，并按项目配置限制搜索；所选 tactic 的 imports 需核实。<br><strong>保留：</strong>按定义、逻辑、等式、局部事实和算术选择下一步的分类保留。</span>

## Choosing the next step

Choose tactics from the actual goal shape; this is guidance, not a mandatory route:

- definitional equality: `reflexivity`, `cbn`, or a small unfold;
- available hypothesis or constructor: `exact`, `assumption`, `apply`, `constructor`, `split`, `left`, `right`;
- equality transport: `rewrite`, `subst`, `f_equal`, `congruence`;
- local bridge: `have`, `assert`, `suff`, `pose proof`, or `set`;
- arithmetic: use the imported solver appropriate to the domain, such as `lia` or `ring`;
- bounded search: `auto n` or `eauto n` only when the relevant hint database and premises are understood.

<span style="color:red">【Choosing the next step｜中改】<br><strong>改哪里：</strong>修改禁止 rewrite !...、rewrite -!... 和 intuition 的两条规则。<br><strong>为什么：</strong>这些是 Rocq 语法名称；Lean 不支持同一写法，继续保留名字不能约束真实的 Lean 动作。<br><strong>替换（Rocq → Lean）：</strong>需要明确简化事实时写 simp only [h1,h2]；反向改写写 rw [←h]；逻辑拆解用 intro、constructor、rcases、exact。<br><strong>删除（仅未来 Lean 版）：</strong>删去对这三个旧语法名字的禁令；不要将禁止 intuition 扩展成禁止所有 Lean 自动化。<br><strong>保留：</strong>如果项目要求限制不透明自动化，保留这一目的，并只约束实际可用的 Lean tactic。</span>

Do not use ssreflect repeat-rewrite syntax `rewrite !...` or `rewrite -!...` in this environment. Do not use `intuition`; construct the logical steps explicitly.

<a id="lean-review-5"></a>

<span style="color:red">【Candidate lemma audit｜中改】<br><strong>本节在做什么：</strong>在使用一个引理前，检查它的结论、参数和全部前提是否适合当前目标。<br><strong>改哪里：</strong>修改候选引理审计的探针和 failed-route/premise fingerprint 的证据来源。<br><strong>为什么：</strong>同名 Lean 定理的参数、实例和前提可能不同；旧 Coq 审计记录不能认证 Lean 应用。<br><strong>替换（Rocq → Lean）：</strong>Coq 类型/应用探针 → #check 全限定名，再在当前 Lean 上下文试 apply/refine，记录未解决 goals 与实例问题；需要时 #synth 所需实例，并为每个前提指定已有 h 或依赖区域。<br><strong>删除（仅未来 Lean 版）：</strong>取消旧 Coq fingerprint/certificate 对 Lean 应用的认证效力；旧记录可留作历史。<br><strong>新增（Lean 适配）：</strong>适配器按 Lean 定理名、实际参数/实例、目标和缺失前提生成失败路线键。<br><strong>保留：</strong>检查真实类型与前提的方法、证据改变才重试的策略保留；admit_id 仍只是 runtime 身份字段，改名不算新证据。</span>

## Candidate lemma audit

Before committing to an imported lemma:

1. inspect its exact type;
2. unify its conclusion with the live target;
3. list the remaining premises and implicit instances;
4. check whether each premise follows from current hypotheses or an already certified local bridge;
5. abandon or change the instantiation when a required premise is unavailable.

A verified failed lemma/missing-premise route must not be repeated through cosmetic edits or an `admit_id` rename. It may be reconsidered after a new hypothesis is derived, the missing premise is compiled, the instantiation genuinely changes, or the audit is shown wrong.

<a id="lean-review-6"></a>

<span style="color:red">【Completion check｜重改｜需重建验收条件】<br><strong>本节在做什么：</strong>在报告成功前，确认最新版本中的负责目标已完成，而且没有留下占位证明。<br><strong>改哪里：</strong>修改 Completion check 的验证命令、证明结束判据和占位验收。<br><strong>为什么：</strong>Lean 没有 Qed./Defined. 结束命令，且编译成功可能包含 sorry；目标、声明和证书还必须对应当前版本。<br><strong>替换（Rocq → Lean）：</strong>checkpoint/coqc → 对当前 staged 内容运行 <code style="white-space:pre-wrap">lake env lean path/to/File.lean</code>；需要库级依赖检查时运行 lake build 对应 target；结束判定 → 当前声明及其源范围检查。<br><strong>删除（仅未来 Lean 版）：</strong>删除通过 Qed./Defined. 判断 Lean 声明结束的旧判据；原有无占位要求继续单独检查，不能被编译成功替代。<br><strong>新增（Lean 适配）：</strong>查询 <code style="white-space:pre-wrap">#print axioms 完整定理名</code>，核实无 sorryAx 等占位依赖，结合 diagnostics 检查未解决目标。工具结果和 certificate 绑定同一版本；普通非占位 warning 不自动判失败。<br><strong>保留：</strong>最新版本、负责目标完成、无占位的验收原则不变。</span>

## Completion check

Before reporting success, verify:

- the current owned goal is closed;
- no proof placeholder remains in the owned theorem;
- the authoritative staged revision, not an older disk copy, passes checkpoint/coqc;
- all opened branches and local assertions are closed;
- the final theorem terminator is correct for the assigned ownership layer.

If the proof still fails, return the exact stable goal/error, the smallest failed step, missing premises, and which certified prefix remains reusable.
