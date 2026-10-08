<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>ProsaBuddy 会检查证明任务的编辑范围、文件版本、依赖条件和验证结果。这份 skill 用来解释这些检查反馈，并决定接下来该采取什么行动，例如重新读取文件、补一个前提、换一条证明路线，或恢复到已验证的位置。<br><strong>具体例子：</strong>你基于旧版本写好了一个修改，但当前文件已经变了，系统会拒绝直接应用这份修改；你需要先读取新版本。又例如，你想使用某个引理，系统发现它需要的条件还没有证明，就会要求补出这个条件，而不是通过给引理改个名字来重复尝试。<br><strong>它会怎么处理：</strong>先读取完整反馈，确认被拒绝的具体原因，然后只修复相关部分。已经验证通过的证明要保留，新写但尚未通过的草稿也要保存，避免恢复时丢失。它还要求依赖某个结果的后续任务，等这个结果真正通过验证后再开始。这份 skill 主要安排系统反馈后的恢复与继续工作，不负责推导某个具体数学定理。</span>

<span style="color:red">【Lean迁移总评】guard 治理、transaction、ownership、草稿保存与恢复政策大体可保留；会话状态、区域解析、前提审计和证书生成需由 Lean backend 承担。策略层轻改，执行/验证层重改；整体重写力度：中重。</span>

<span style="color:red">【Workflow｜首要结构性问题 1】<a href="#lean-review-5">点击跳转</a>：<br><strong>原来在做什么：</strong>当编辑版本过期、会话里的目标与文件不一致，或一次尝试失败时，这一节让 ProsaBuddy 回到可继续证明的位置，同时保留已验证的内容和新草稿。它依赖后端知道“当前证明进行到哪里、能从哪里恢复”。<br><strong>改哪里：</strong>修改 Workflow 的会话恢复、目标读取、checkpoint 与 proof_region 定位实现。<br><strong>为什么：</strong>Coq 保存的状态不能交给 Lean 执行；Lean 的目标来自具体文档位置，证明区域也依赖其声明与嵌套块语法。<br><strong>替换（Rocq → Lean）：</strong>Coq 会话读取 → 项目中 lake env lean --server 启动的 Lean LSP；didOpen/didChange 同步文本，publishDiagnostics 取错误，$/lean/plainGoal 按位置取目标；Coq 区域定位 → Lean Syntax 源范围。<br><strong>删除（仅未来 Lean 版）：</strong>删除把旧 Coq snapshot/state ID 当成 Lean 恢复点的做法。<br><strong>新增（Lean 适配）：</strong>为现有恢复协议实现 Lean 适配器：保存每个 staged revision 的源文本，恢复时重载并重新检查，重新取得目标及局部假设。仅替换工具名字不能提供这些能力。<br><strong>保留：</strong>先读最新状态、保存草稿、保住已验证进度的政策保留；版本管理本身并非 Lean 独有。</span>

<span style="color:red">【Candidate Roles And Scheduling｜首要结构性问题 2】<a href="#lean-review-4">点击跳转</a>：<br><strong>原来在做什么：</strong>系统会记下某个引理还缺哪些前提、某条路线为何失败，以及哪些证明已经验证。后续据此决定能否重试、能否使用一个结果，以及是否可以开始依赖它的下一块证明。这里的“证书”就是后端保存的验证记录。<br><strong>改哪里：</strong>修改 direct_apply 审计、certificate/premise fingerprint 生成以及任务 ready 的证据来源。<br><strong>为什么：</strong>旧记录只证明某个 Coq 声明在旧环境中的情况；Lean 的参数、实例和前提改变后，旧成功或失败都不能直接沿用。<br><strong>替换（Rocq → Lean）：</strong>Coq 应用探针 → 当前 Lean 上下文中的 apply/refine，收集真实残留 goals 和实例信息；已完成区域 → lake env lean 检查并核实完整声明无占位。<br><strong>删除（仅未来 Lean 版）：</strong>取消旧 Coq certificate 和 failed-route 记录对 Lean 任务状态的直接判定效力；历史记录仍可保存。<br><strong>新增（Lean 适配）：</strong>由适配器根据当前 Lean 验证结果和版本生成新 certificate/premise fingerprint，再让调度读取新记录。<br><strong>保留：</strong>候选角色、依赖就绪调度和 failed-route 策略保留；需要迁移的是证据的生成与验证实现。</span>

<span style="color:red">【需重写的 section｜点击跳转】<a href="#lean-review-1">Recovery Map</a>；<a href="#lean-review-4">Candidate Roles And Scheduling</a>；<a href="#lean-review-5">Workflow</a>。</span>

---
name: prosabuddy-guard-recovery
description: Interpret Prosabuddy proof guard, premise-audit, Coq-session desynchronization, proof-transaction recovery, and theorem-region planning feedback and select the next safe proof action. Use when a proof worker receives verified_failed_route_reuse, verified_failed_route_requires_audit, candidate_unresolved_premise, repair_plan_route, proof_transaction_stale_view, proof_transaction_scope_rejection, session_state_desync, debug-only progress, a recoverable transaction, or region-granularity guidance.
---

<span style="color:red">【Frontmatter｜中改】<br><strong>改哪里：</strong>修改 frontmatter description 中的 Coq-session desynchronization。<br><strong>为什么：</strong>技能名和 guard 字段是 ProsaBuddy 协议；发生变化的是会话证据的后端来源。<br><strong>替换（Rocq → Lean）：</strong>Coq-session desynchronization → Lean document/session desynchronization。<br><strong>新增（Lean 适配）：</strong>描述中写明恢复必须使用当前 Lean 文档版本、目标位置和验证结果；实际会话、审计、证书能力需核实后端实现，不能假定已就绪。<br><strong>保留：</strong>skill name、guard 字段和事务契约不变。</span>

# Prosabuddy Guard Recovery

<span style="color:red">【Prosabuddy Guard Recovery｜轻改】<br><strong>本节在做什么：</strong>解释 ProsaBuddy 拒绝某次操作或要求恢复时，应怎样修复并保住已有进度。<br><strong>改哪里：</strong>修改开头 compiler-validated 一词所指的验证记录来源。<br><strong>为什么：</strong>旧 Coq 证书不能证明迁移后的 Lean 声明通过验证。<br><strong>替换（Rocq → Lean）：</strong>Coq compiler-validated 记录 → 同一 staged revision 对应的 Lean 文件检查与无占位证明记录。<br><strong>删除（仅未来 Lean 版）：</strong>移除将旧 Coq 验证记录复制为 accepted Lean certificate 的做法；旧记录只留作历史诊断。<br><strong>保留：</strong>依据完整 guard payload、保留 staged 和已验证进度的两条原则直接保留。</span>

Use the full runtime guard payload as the source of truth. Preserve staged and compiler-validated proof text, then repair only the rejected dimension.

<a id="lean-review-1"></a>

<span style="color:red">【Recovery Map｜重改｜协议保留，证据与状态实现需迁移】<br><strong>本节在做什么：</strong>把每种系统反馈对应到下一项允许的修复动作。<br><strong>改哪里：</strong>修改 Recovery Map 中依赖 premise、goal、region、session 和 certificate 的具体恢复动作。<br><strong>为什么：</strong>guard 协议可以复用，但 Coq assumption/conversion probe、目标指纹和会话状态不能代表当前 Lean 上下文。<br><strong>替换（Rocq → Lean）：</strong>failed_route/premise 类 → 同一 Lean 上下文试 apply/refine 并记录残留 goals；scope_rejection → 用 Lean 语法范围裁剪；session_state_desync → 重开或同步 Lean 文档并重取目标；best_certified → 读取已验证版本源文本，重新检查后恢复。<br><strong>删除（仅未来 Lean 版）：</strong>取消旧 Coq probe 成功/失败和旧证书对 Lean 的直接效力，不能只改工具名再重放状态。<br><strong>新增（Lean 适配）：</strong>Lean 后端需提供 region parser、goal fingerprint、前提审计和证书生成；具体能力需核实实现。<br><strong>保留：</strong>字段名不变；stale_view 仍先重读 staged revision 再生成差异；debug 仍保存草稿但不签发证书。</span>

## Recovery Map

<span style="color:red">【Recovery Map｜轻改】<br><strong>改哪里：</strong>只修改 DAG、metadata-only 修复及重试限制读取的验证数据来源。<br><strong>为什么：</strong>DAG 节点/边、5/5 重试上限和四次结构修订是 ProsaBuddy 治理规则，与证明语言无关。<br><strong>替换（Rocq → Lean）：</strong>Coq target/premise/certificate 数据 → 当前 Lean 验证结果。<br><strong>保留：</strong>DAG 字段、metadata-only 修复、5/5 和最多四次结构修订原样保留；不把这些数值绑定到 LSP goal 数量。runtime 版本另有变化时再核对。</span>

| Guard or state | Next safe action |
|---|---|
| `verified_failed_route_reuse` | Change the lemma, affected target route, or mechanically audited instantiation; alternatively prove the exact missing premise with a current compiler certificate. |
| `verified_failed_route_requires_audit` | Replace the legacy name-only candidate with a structured library candidate and let the live premise audit check its exact interface and application. Do not treat a renamed fact or free-form override as evidence. |
| `candidate_unresolved_premise` | A residual premise already survived the live assumption/conversion probe. Produce it through an explicit dependency node or reference a current compiler certificate from the handoff; otherwise remove the candidate. |
| `candidate_premise_*_invalid` | Use the exact residual-premise fingerprint returned by the guard. Correct the dependency target or reference a current matching certificate; do not invent certificate IDs or relabel a residual premise as local evidence. |
| `recommended_action: repair_plan_route` | Preserve the current semantic DAG: keep node targets, edges, dependencies, and the leaf set fixed. Change only the candidate lemma, its mechanically distinct instantiation, or the audited source of a residual premise. |
| `recommended_action: repair_plan_metadata` | Correct only the fields named by `repair_hint` and `details`—for example node IDs, edge endpoints, dependency anchors, declared root targets, or the final composition output. Copy the reported normalized target instead of paraphrasing it. This does not consume a semantic DAG revision. |
| `recommended_action: do_not_retry_metadata_only_plan` | The submitted payload has not changed the review-relevant state. If `metadata_repair_repeat_count` is `5/5`, the identical metadata failure has reached its limit. Do not resubmit the same payload or make another wording-only change; re-read `compared_target_field`, normalized values, and hashes, then rebuild the exact rejected fields from authoritative root/producer data. |
| `recommended_action: revise_semantic_dag` | Submit a materially different dependency/target structure only when the current plan has a structural hard error. The initial plan plus at most four materially distinct revisions is the bounded semantic search space. |
| `recommended_action: stop_and_report_best_plan` | Do not explore another speculative or still-failing semantic DAG. Report the best rejected plan and its exact hard errors. A stale exhausted verdict may be invalidated only by a candidate that now passes the deterministic review; do not keep submitting rejected candidates to test this exception. |
| `proof_transaction_stale_view` | Re-read the staged region and build a new patch against the current revision. |
| `proof_transaction_scope_rejection` | Shrink the patch to the authorized theorem body or proof region and preserve its markers and surrounding source. |
| `session_state_desync` | Stop submitting tactics, reopen the assigned region-scoped session, and verify the goal fingerprint before continuing. |
| `progress_level: debug` | Keep the draft for diagnosis, but do not treat it as route validation or accepted proof progress. |
| recoverable transaction | Use the active recovery baseline. If `recovery_base` is `best_certified`, continue there while preserving the newer unaccepted draft in the journal; otherwise continue from the current staged draft. |

<a id="lean-review-2"></a>

<span style="color:red">【Generic Route Recipe｜轻改】<br><strong>本节在做什么：</strong>提供从准备定义到完成证明的一般路线，供实际目标决定如何取舍。<br><strong>改哪里：</strong>修改五层通用路线里举例使用的具体证明动作。<br><strong>为什么：</strong>定义准备、桥接、规范化、组合和收尾的规划不依赖语言；真正执行时要调用 Lean tactic。<br><strong>替换（Rocq → Lean）：</strong>定义展开→unfold/simp only；局部桥接→have；表达式统一→rw/simp；组合→apply/refine/calc；自然数算术→omega。每层记录实际输出目标。<br><strong>保留：</strong>五层规划和根据真实目标合并/放弃步骤的原则保留；这些动作可选，不能强制每个任务走五步或硬编码固定定理清单。</span>

## Generic Route Recipe

Use this only as a soft planning prior:

1. Prepare definitions and local context needed by later facts.
2. Establish a semantic or pointwise bridge.
3. Normalize the data, collection, or library-facing proof shape.
4. Aggregate or compose established facts.
5. Close the final logical or arithmetic step.

Reorder, merge, replace, or abandon these layers when the live goal, hypotheses, premise audit, or compiler evidence supports a better route. Never turn a successful trace into a theorem-specific lemma list, variable naming scheme, or tactic script.

<a id="lean-review-3"></a>

<span style="color:red">【Region Granularity｜中改】<br><strong>本节在做什么：</strong>说明一段证明应拆成多大的任务块，避免分得过碎或把独立任务混在一起。<br><strong>改哪里：</strong>修改 Region Granularity 的区域分割器和局部区域验证上下文。<br><strong>为什么：</strong>Lean 用声明和缩进证明块组织范围，局部证明还依赖 imports、namespace、前置声明和局部假设；旧命令终止符无法确定这些边界。<br><strong>替换（Rocq → Lean）：</strong>.v 命令/Proof./Qed. 分割 → Lean declaration 和 := by/嵌套 have/case 的 Syntax 源范围。<br><strong>删除（仅未来 Lean 版）：</strong>若现有区域解析器依赖 Rocq 命令结束符，移除这部分分割逻辑；原文未规定具体解析器，需先核实现有实现。<br><strong>新增（Lean 适配）：</strong>在 Lean 区域适配器中记录所属声明、可见局部假设和依赖区域；构造验证上下文时带上相同 imports/namespace/前置声明。局部片段不能脱离共享上下文单独编译后就签发证书；具体 parser 和验证封装仍需查看后端实现。<br><strong>保留：</strong>按依赖和归属拆成 3–6 个语义区域的建议，以及只编辑获授权证明体的政策不变。</span>

## Region Granularity

Prefer roughly 3-6 meaningful first-level regions, commonly 4-5, without treating the count as a guard condition. Keep several local rewrites, arithmetic steps, or helper facts together when they establish one exported fact under one dependency boundary. Split only for independent semantic layers, missing dependencies, cross-branch ownership, or repeated semantic/compiler failure. Merge adjacent tactic-sized leaves that share hypotheses and have no useful independent certificate.

<a id="lean-review-4"></a>

<span style="color:red">【Candidate Roles And Scheduling｜重改】<br><strong>本节在做什么：</strong>区分候选引理的用途，并规定后续任务何时可以使用已经验证的前置结果。<br><strong>改哪里：</strong>修改五种 candidate role 的可用性探针，以及区域 ready 的判定输入。<br><strong>为什么：</strong>Lean 要在当前上下文重新完成 elaboration、结论统一和实例合成；旧 binder 位置、Coq probe 或证书不能证明候选有效。<br><strong>替换（Rocq → Lean）：</strong>direct_apply→apply/refine 后收集未解决 goals；rewrite→指定位置试 rw [h] 或 rw [←h]；transport→显式等式配合 subst/rw；local_fact→have h := 已实例化证明项；automation_hint→在实际 tactic 中使用指定事实集。<br><strong>删除（仅未来 Lean 版）：</strong>取消旧 Coq certificate 对 Lean ready 状态的直接认证；仅 #check 可见不算 valid。<br><strong>新增（Lean 适配）：</strong>调度读取同一 Lean 环境/版本重新生成的生产者证书，探针同时返回实例合成问题和真实残留义务。<br><strong>保留：</strong>五类用途和依赖就绪调度政策保留。</span>

## Candidate Roles And Scheduling

Set each structured library candidate to `direct_apply`, `rewrite`, `transport`, `local_fact`, or `automation_hint`. Only `direct_apply` is expected to unify with the complete node target and expose residual premises during planning; other roles are checked for availability and validated at their concrete proof use. Follow the runtime's dependency-ready region selection: declared producer regions must be compiler-certified, while file order is only a tie-breaker among ready regions.

<a id="lean-review-5"></a>

<span style="color:red">【Workflow｜重改】<br><strong>本节在做什么：</strong>给出收到反馈后读取状态、保留草稿、修复指定问题并重新验证的完整顺序。<br><strong>改哪里：</strong>修改 Workflow 第 5 步的会话验证、证书生成和恢复实现。<br><strong>为什么：</strong>这一步需要 Lean 实际 proof state、diagnostics 和声明检查；旧 Coq state ID 无法恢复 Lean，位置目标或编译成功也不足以证明无占位。<br><strong>替换（Rocq → Lean）：</strong>旧验证链 → 同步 staged 文档→等待同版本 diagnostics→取区域目标→编译相同内容→核实完整声明无占位→生成结果记录。<br><strong>删除（仅未来 Lean 版）：</strong>不再把 Rocq state ID 用作 Lean 的恢复点。<br><strong>新增（Lean 适配）：</strong>实现或核实 Lean 后端的会话与恢复参数；保底采用保存源文本版本并重新检查。若实现内存 snapshot，须同时保存相应 Lean 环境和上下文。<br><strong>保留：</strong>步骤 1–4 的完整 payload、草稿保存、精确修复和 stale 后重读政策不变。</span>

## Workflow

1. Read the complete guard payload, including fingerprints, missing premises, transaction revision, recommended action, `repair_hint`, and structured `details`.
2. Preserve the active transaction baseline, every compiler-certified fragment, and any newer unaccepted draft recorded by revision/hash.
3. Change only the route, premise mapping, proof state, or edit scope identified by the guard.
4. Re-read after stale-view or desynchronization errors instead of replaying an old edit or tactic.
<span style="color:red">【Workflow｜重改｜工具与验证实现需替换】<br><strong>改哪里：</strong>修改 coq_session、coqc、checkpoint 和 best_certified 的实际工具调用。<br><strong>为什么：</strong>Lean LSP 提供位置目标与诊断，ProsaBuddy 的 checkpoint/certificate 则仍需自己的适配器；LSP 位置目标或内存快照不等于独立编译证书。<br><strong>替换（Rocq → Lean）：</strong>Coq goal inspection → <code style="white-space:pre-wrap">$/lean/plainGoal</code>（URI/position）；Coq diagnostics → <code style="white-space:pre-wrap">textDocument/publishDiagnostics</code>；coqc → 项目根目录的 <code style="white-space:pre-wrap">lake env lean path/to/File.lean</code>，需要项目目标时用 lake build。<br><strong>新增（Lean 适配）：</strong>用 lake env lean --server 启动服务；didOpen/didChange 发送当前文本；textDocument/waitForDiagnostics 等待检查。适配器核对源版本、上下文和占位依赖后生成证书，并实现 best_certified 恢复。不能假设现成 lean_session 工具或 Lean LSP 自带同名 checkpoint/certificate 方法。</span>

5. Validate the new staged revision with the narrowest suitable `coq_session`, checkpoint, or `coqc` certificate.
6. If the guard omits the evidence needed to choose a legal recovery, report the missing field instead of inventing a free-form override.

<span style="color:red">【Workflow｜轻改】<br><strong>改哪里：</strong>修改 runtime payload 中验证证据的环境、目标和来源版本字段。<br><strong>为什么：</strong>同一身份字段下保存的证据必须来自当前 Lean 环境；skill 不能自行编造后端返回值。<br><strong>替换（Rocq → Lean）：</strong>Coq 环境/目标表示 → Lean 项目和版本、document URI/version、region 源范围、实际 goal/premise 表示；certificate 记录对应编译结果及来源版本。<br><strong>保留：</strong>复用现有 transaction/revision 字段及“策略由 skill、身份/版本/指纹由 runtime 提供”的分工。字段缺失时按原策略报告，不杜撰 certificate ID、fingerprint 或恢复接口。</span>

The skill supplies stable recovery policy only. Runtime prompts must provide concrete transaction IDs, revisions, hashes, goal fingerprints, failure IDs, and premise fingerprints.
