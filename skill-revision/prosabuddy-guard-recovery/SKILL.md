<span style="color:red">【这个 skill 在做什么】<br><strong>什么时候用：</strong>ProsaBuddy 会检查证明任务的编辑范围、文件版本、依赖条件和验证结果。这份 skill 用来解释这些检查反馈，并决定接下来该采取什么行动，例如重新读取文件、补一个前提、换一条证明路线，或恢复到已验证的位置。<br><strong>具体例子：</strong>你基于旧版本写好了一个修改，但当前文件已经变了，系统会拒绝直接应用这份修改；你需要先读取新版本。又例如，你想使用某个引理，系统发现它需要的条件还没有证明，就会要求补出这个条件，而不是通过给引理改个名字来重复尝试。<br><strong>它会怎么处理：</strong>先读取完整反馈，确认被拒绝的具体原因，然后只修复相关部分。已经验证通过的证明要保留，新写但尚未通过的草稿也要保存，避免恢复时丢失。它还要求依赖某个结果的后续任务，等这个结果真正通过验证后再开始。这份 skill 主要安排系统反馈后的恢复与继续工作，不负责推导某个具体数学定理。</span>

<span style="color:red">【Workflow｜Lean 后端适配 1】<a href="#lean-review-5">点击跳转</a><br><strong>可以保留：</strong>现有 recovery policy（恢复规则）和 revision management（版本管理），包括保存草稿、保住已验证进度、按当前修订恢复。<br><strong>为什么要适配：</strong>这些规则需要后端提供“当前目标是什么、有哪些可用条件、证明进行到哪里”。原 Coq 会话提供的 proof state 不能交给 Lean 继续执行，因此要调整状态的读取、恢复和校验实现。<br><strong>怎么适配：</strong>让现有流程调用 Lean 后端，从对应源码版本取得目标、上下文及位置，并核对恢复后的状态与该版本一致；恢复规则和版本管理方式继续沿用。</span>

<span style="color:red">【Candidate Roles And Scheduling｜Lean 后端适配 2】<a href="#lean-review-4">点击跳转</a><br><strong>可以保留：</strong>现有 candidate roles（候选引理角色）和 dependency scheduling（依赖调度），包括只对 direct_apply 审查完整目标与剩余前提、生产者验证通过后才调度依赖任务。<br><strong>为什么要适配：</strong>这些决策依赖 premise audit（前提审查）和 compiler certificate（编译验证证据）。原 Coq 审查和编译结果不能证明 Lean 声明满足同样的条件，需要更换证据的生产与核验实现。<br><strong>怎么适配：</strong>由 Lean 后端检查实际声明、参数、实例和剩余前提，并为对应版本生成编译验证证据；接收证据时核对其 Lean 环境和源码修订，再交给现有角色规则与调度流程使用。证书契约和调度政策可保留。</span>

<span style="color:red">【需适配后端的 section｜点击跳转】<a href="#lean-review-1">Recovery Map</a>；<a href="#lean-review-4">Candidate Roles And Scheduling</a>；<a href="#lean-review-5">Workflow</a>。保留现有工作流规则，调整对 Lean 后端的调用及验证证据的来源与核验。</span>

---
name: prosabuddy-guard-recovery
#<span style="color:red">【description】将 <code style="white-space:pre-wrap">Coq-session desynchronization</code> 改为 <code style="white-space:pre-wrap">Lean document/session desynchronization</code>，并补充“恢复依据当前 Lean 文档版本、目标位置和验证结果”；其余 guard 触发词保留。理由：会话验证的后端改为 Lean，原有 guard 名称和事务协议仍可保留。</span>
description: Interpret Prosabuddy proof guard, premise-audit, Coq-session desynchronization, proof-transaction recovery, and theorem-region planning feedback and select the next safe proof action. Use when a proof worker receives verified_failed_route_reuse, verified_failed_route_requires_audit, candidate_unresolved_premise, repair_plan_route, proof_transaction_stale_view, proof_transaction_scope_rejection, session_state_desync, debug-only progress, a recoverable transaction, or region-granularity guidance.
---



# Prosabuddy Guard Recovery <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【解释 ProsaBuddy 拒绝某次操作或要求恢复时，应怎样修复并保住已有进度。】</span>

Use the full runtime guard payload as the source of truth. Preserve staged and compiler-validated proof text, then repair only the rejected dimension.

<a id="lean-review-1"></a>



## Recovery Map <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【把每种系统反馈对应到下一项允许的修复动作。】</span>

<span style="color:red"><strong>保留：</strong>表中的 guard、指纹、证书、best_certified、DAG 与重试额度都是通用契约，字段和政策不因迁移而失效。<br><strong>实现层按需适配：</strong>① 若前提探针调用 Coq 的假设匹配或转换检查，改为 Lean 上下文中的检查；原文没有给出实现，需先核实。<br>② 若恢复点或证书保存 Coq 状态及编译结果，不能直接认证或恢复 Lean，应重取同版本 Lean 结果。旧记录可留作历史；具体元数据修复与草稿保存规则继续保留。</span>

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



## Generic Route Recipe <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【提供从准备定义到完成证明的一般路线，供实际目标决定如何取舍。】</span>



Use this only as a soft planning prior:

1. Prepare definitions and local context needed by later facts.
2. Establish a semantic or pointwise bridge.
3. Normalize the data, collection, or library-facing proof shape.
4. Aggregate or compose established facts.
5. Close the final logical or arithmetic step.

<span style="color:red"><strong>保留：</strong>这五层是语言无关的规划建议，Lean 中仍可重排、合并或放弃；不要把示例变成固定的 tactic 或定理清单。</span>

Reorder, merge, replace, or abandon these layers when the live goal, hypotheses, premise audit, or compiler evidence supports a better route. Never turn a successful trace into a theorem-specific lemma list, variable naming scheme, or tactic script.

<a id="lean-review-3"></a>



## Region Granularity <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【说明一段证明应拆成多大的任务块，避免分得过碎或把独立任务混在一起。】</span>

<span style="color:red"><strong>保留：</strong>按语义和依赖切分的原则，以及 3–6 个区域的建议不变。<br><strong>实现层按需适配：</strong>原文未规定解析器；若它依赖 Rocq 命令结束符，应改按 Lean 声明和嵌套证明范围定位。验证局部片段时仍需所属声明、imports 和局部上下文，不能脱离上下文单独签证。</span>

Prefer roughly 3-6 meaningful first-level regions, commonly 4-5, without treating the count as a guard condition. Keep several local rewrites, arithmetic steps, or helper facts together when they establish one exported fact under one dependency boundary. Split only for independent semantic layers, missing dependencies, cross-branch ownership, or repeated semantic/compiler failure. Merge adjacent tactic-sized leaves that share hypotheses and have no useful independent certificate.

<a id="lean-review-4"></a>



## Candidate Roles And Scheduling <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【区分候选引理的用途，并规定后续任务何时可以使用已经验证的前置结果。】</span>



Set each structured library candidate to `direct_apply`, `rewrite`, `transport`, `local_fact`, or `automation_hint`.

<span style="color:red"><strong>保留：</strong>候选角色分工、只为 direct_apply 在规划时暴露完整前提的契约不变。<br><strong>实现层按需适配：</strong>若探针读取 Coq binder 或统一结果，就在 Lean 真实上下文中重查；其他角色仍在实际使用处验证。查得到名称不等于适用。</span>

Only `direct_apply` is expected to unify with the complete node target and expose residual premises during planning; other roles are checked for availability and validated at their concrete proof use.

<span style="color:red"><strong>保留：</strong>生产者先验证再调度的契约不变，compiler-certified 概念本身不失效。<br><strong>实现层按需适配：</strong>若记录保存 Coq 编译证据，应在 Lean 真实上下文中重新取得验证结果。</span>

Follow the runtime's dependency-ready region selection: declared producer regions must be compiler-certified, while file order is only a tie-breaker among ready regions.

<a id="lean-review-5"></a>



## Workflow <span style="color:red; font-size:14px; font-weight:normal; display:inline;">【给出收到反馈后读取状态、保留草稿、修复指定问题并重新验证的完整顺序。】</span>

1. Read the complete guard payload, including fingerprints, missing premises, transaction revision, recommended action, `repair_hint`, and structured `details`.
2. Preserve the active transaction baseline, every compiler-certified fragment, and any newer unaccepted draft recorded by revision/hash.
3. Change only the route, premise mapping, proof state, or edit scope identified by the guard.
4. Re-read after stale-view or desynchronization errors instead of replaying an old edit or tactic.

<span style="color:red"><strong>为什么要改：</strong>① coq_session 是这里指定的 Coq 执行工具，不能直接运行 Lean。<br>② coqc 不能编译 Lean 源码；checkpoint/certificate 则是通用记录，是否改实现取决于它是否绑定 Coq 状态或输出。<br><strong>怎么改：</strong>接入实际 Lean 目标与诊断接口，例如 $/lean/plainGoal、textDocument/publishDiagnostics，以 lake env lean 等验证同版本源码。不臆造现成会话工具；恢复实现若保存 Coq 状态，再适配为有效的 Lean 文本重检或快照。</span>

5. Validate the new staged revision with the narrowest suitable <span style="color:gray">`coq_session`</span>, checkpoint, or <span style="color:gray">`coqc`</span> certificate.
6. If the guard omits the evidence needed to choose a legal recovery, report the missing field instead of inventing a free-form override.



The skill supplies stable recovery policy only.

<span style="color:red"><strong>保留：</strong>身份、版本及指纹字段继续由 runtime 提供；skill 缺少字段时仍按原规则报告。<br><strong>实现层按需适配：</strong>只有指纹或状态编码包含 Coq 表达式时，才需替换其生成或序列化实现。核实当前 Lean 环境和版本的证据来源，不复制旧 Coq 结果。</span>

Runtime prompts must provide concrete transaction IDs, revisions, hashes, goal fingerprints, failure IDs, and premise fingerprints.
