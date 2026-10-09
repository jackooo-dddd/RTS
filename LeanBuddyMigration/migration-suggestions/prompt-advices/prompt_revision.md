# ProsaBuddy Prompts: Rocq → Lean Migration Requirements

## 0. Conventions Shared by All Proof-Related Prompts

### 0.1 Use an Outer Parenthesized Wrapper for Delegated Proof Regions

Lean ProsaBuddy adopts `have h : P := (by ... )` as a project convention: the matching outer parentheses delimit the delegated target’s proof term. This is a project-level requirement, not a syntax form that Lean requires for every proof. Inside `by`, Lean tactic syntax, indentation, and branch rules still apply; adding outer parentheses does not make internal indentation irrelevant. [See the Lean tactic syntax documentation][lean-running].

The following five requirements must appear in both `prover.txt` and `lemma.txt` and must be enforced by a consistent region parser and edit-scope checker:

1. Include the entire target. A `proof_region` must enclose the complete `have h : P := (by ... )`, including its name, proposition, and entire proof term—not only the tactics inside `by`.
2. End after the matching closing parenthesis. The `proof_region end` marker must appear after the `)` matching the outermost `(` in the target’s `:= (by ... )`; it must not be placed inside the proof term.
3. Perform genuine delimiter matching. The parser must anchor its search to the target’s assignment, not confuse parentheses in declaration parameters with the proof wrapper. It must handle nested expressions, string and character literals, escapes, line comments, and nested block comments correctly, rather than stopping at the first `)`.
4. Apply one delegated-target format consistently. Every target governed by this delegation protocol must use the wrapper above. Do not mix parenthesis-based extraction with indentation-based guesses for different regions in the same protocol. Missing wrappers, unbalanced parentheses, or ambiguous bounds must produce a structural error; do not guess or capture a neighboring region.
5. Keep parent composition outside the region. Uses of an exported result—such as `exact h`, `rw [h]`, `apply h`, or cross-branch combinations—must follow the end marker and remain owned by the main prover. The `lemma` agent may not move markers to enlarge its authority or edit these steps outside its region.

Boundary example:

```lean
example (P Q R : Prop)
    (hP : P) (hPQ : P → Q) (hQR : Q → R) : R := by
  -- proof_region begin
  have hQ : Q := (by
    exact hPQ hP
  )
  -- proof_region end

  -- Parent composition: managed by the main prover, outside the lemma edit scope.
  exact hQR hQ
```

Necessary helper facts may appear in the same region, but they must precede the exported target or occur inside its proof term. The begin marker must enclose those helpers and the complete target. Parent-composition steps after the target must not be pulled into the region under the guise of helpers.

Two replacements must not be made mechanically. An empty `{}` cannot simply become an empty `()`; `()` does not mean “an unproved proposition.” A draft placeholder such as `:= (by sorry)` may be allowed by project policy, but it must be marked unfinished. Moreover, matching parentheses establishes only a textual boundary. It does not, by itself, prove that the target statement was preserved, the surrounding environment was unchanged, or the proof is valid.

### 0.2 Tool Migration: Pantograph Session, LSP Diagnostics, `lake build` — Do Not Invent Command Names

**Decided 2026-10-09 ([BACKEND_DECISION.md](../BACKEND_DECISION.md)):** Pantograph is the interactive proof backend (step-by-step tactics, goal inspection, multiple subgoals, backtracking), Lean LSP provides file-level diagnostics, and `lake build` performs final verification. Retain small-step interactive proof development through the Pantograph-backed session tool. Until that tool is implemented, prompts must still not name concrete commands (e.g. `lean_session step`); use the exact operation names of the pinned Pantograph version once they exist.

| Current Rocq operation | Capability required on the Lean side |
| --- | --- |
| Tactic execution with `coq_session` or `petanque` | Run tactics on a Pantograph goal state opened from the target in the current staged source revision (real context, not a re-typed statement); write the successful proof text back to the source and check it there. |
| `coq_session goal`, `petanque goals`, Rocq `lsp proofGoals`, `Show.` | Goals and local context the agent acts on come from the Pantograph goal state; the `lsp` tool has no goal operation (DECISIONS D3). |
| `coqtop Check / About / Print / Search` | Query Lean types and declarations, hover information, definition lookup, and repository search; Lean commands such as `#check` and `#print` do not by themselves cover every lookup feature. |
| `coqc` | Per step: Lean LSP diagnostics or `lake env lean <file.lean>` on the staged file. Final: `lake build` of the module plus the integrity audit. A successful process exit alone does not certify a completed proof. |
| Session snapshot / rollback | Inside a session: keep Pantograph goal-state handles and continue from an earlier one. Across source changes: restore the transaction revision and re-open the goal state from source (old handles are invalid). |
| `checkpoint`, certificates, audits | ProsaBuddy protocol names may remain, but their evidence must be produced by the Lean backend and bound to the exact revision and verification scope. |

Scratch validation fragments must preserve the target’s real parameters, instances, local definitions, and valid dependencies. Do not make a fragment “succeed” by adding extra assumptions. Describe a particular query, incremental-checking feature, or validation command in the prompt only after that capability has actually been implemented; do not invent tool names in advance.

### 0.3 A Checkable Draft, a Completed Region, and a Completed Theorem Are Different States

Lean placeholders introduced by `sorry` and incomplete proofs in dependencies can surface as `sorryAx`. Neither an empty goal list nor a successful compilation result rules out placeholder-based proofs. For final declarations, `#print axioms` can help inspect dependencies. [See the official proof-validation documentation][lean-validation].

| State | Acceptance criterion | What it does not establish |
| --- | --- | --- |
| Draft or skeleton checks | The structure and outer composition match the plan; placeholders remain only in approved locations; all unfinished obligations are tracked. | The corresponding region is not yet certified as solved. |
| Local region completed | The exported target has been checked in the correct context, carries no unfinished proof dependencies, and satisfies region, contract, and dependency requirements. | This does not establish that other siblings or the entire theorem are complete. |
| Entire theorem completed | The merged target declaration passes Lean checking, integrity auditing, and dependency review, with no unfinished proof dependencies or unauthorized assumptions. | Local certificates or a successful draft compilation alone are insufficient. |

These are project acceptance requirements. The verification scope must distinguish the region itself, the producers it actually uses, and the entire theorem. Unfinished unrelated siblings must not automatically invalidate a sound certificate for an independent region; conversely, results depending on uncertified producers must not be presented as unconditionally complete.

The foundational-axiom policy must be configured separately. “No `sorryAx` or unauthorized new assumptions” does not mean “Lean must contain zero axioms of any kind.” The final proof’s dependencies and the preservation of the original declaration and environment are two separate audit questions.

---

## 1. `prover.txt`

### Responsibility

The main prover reads the theorem, consults `proof.tex` when applicable, submits `proof_plan`, builds the theorem skeleton and `proof_region` boundaries, reviews local results, and owns final acceptance. Normal delegation is driven by the proof-workflow scheduler using the accepted DAG and dependency certificates—not by the main prover freely redispatching lemmas each turn. References: [lines 23–31](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L23-L31), [lines 44–52](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L44-L52), [lines 90–112](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L90-L112).

### 1.1 Coq tools → Lean tools；`.v` → `.lean`

Location: [lines 1–18](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L1-L18).

```text
12: - `coq_session`: preferred tool for incremental proof construction and validation
13: - `coqtop`: quick `Check`, `About`, `Print`, and `Search` queries
14: - `coqc`: narrow compilation check when it is the simplest validation
```

Replace tool definitions and all later usage instructions with the Lean capabilities in §0.2. Change the output-file extension on source line 11 to `.lean`; also revise the opening role description and the fallback-tool guidance on line 18. Generic tools or protocols such as `read`, `edit`, `proof_plan`, and `checkpoint` do not need renaming solely because the proof language changes.

### 1.2 Region Boundaries → Project-Mandated `:= (by ... )`

Location: [lines 26–30](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L26-L30), [lines 69–70](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L69-L70), [lines 84–85](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L84-L85).

```text
26: ... wraps the exported local target statement and its complete `{ ... }` proof block ...
29: ... discharge that subgoal inside `{ ... }` immediately ...
85: ... place `proof_region end` immediately after that target's `{ ... }` proof block ...
```

Replace the brace-based rules with all five requirements in §0.1. The heading on source line 28 can become “Local Proof Wrappers and Connector-Fact Rules.” The main prover must generate compliant wrappers when materializing the skeleton; do not defer formatting repairs to a lemma agent with restricted edit permissions.

`region end` must be located after the `)` matching the target’s outer proof wrapper. Lean indentation and branch syntax remain mandatory inside that wrapper.

### 1.3 Prosa/MathComp Lemmas and Evidence → Lean Prosa/Mathlib

Location: [lines 35–39](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L35-L39), [lines 48](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L48), [lines 56–59](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L56-L59), [lines 70](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L70), [lines 85](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L85), [lines 118–128](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L118-L128).

```text
59: ... existing Prosa, MathComp, or local lemma.
70: Use `prosa:`, `mathcomp:`, `local:`, `context:`, `coq:`, or `compiler:` evidence ...
128: ... MathComp bigop/cardinality/count lemmas ... bool/proposition reflection ...
```

Replace library interfaces, shape-node examples, and evidence sources. **Decided (DECISIONS D13):** the evidence prefixes become `prosa:`, `mathlib:`, `local:`, `context:`, `lean:`, `compiler:`; the contract parser, the premise audit and the prompts change together, not only the prompt.

Review the `bigop`, `count`, `has`, `pick`, and `uniq` references on source lines 56–58. Choose representations actually used in the Lean translation; do not indiscriminately replace every sequence with `Finset`, because list duplicates may matter for counting. Treat project-specific APIs such as `sumFiltered` as unverified until their real definitions have been checked. Arithmetic over ordinary Lean propositions should not be forced through an SSReflect-style Bool↔Prop round trip; introduce such bridges only for genuinely Boolean interfaces.

### 1.4 Coq AST/Audit → Lean Validation and Declaration-Integrity Audit

Location: [lines 92–96](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L92-L96).

```text
94: Final `coqc`/`checkpoint` success is not committable until the Rocq AST audit also accepts it.
```

Retain the requirement that compilation alone is not sufficient; the Lean backend must confirm that the target declaration and its parameters have not been changed without authorization, commands and environment outside the region comply with scope rules, and no incomplete or unapproved dependencies remain. Merely renaming “Rocq AST audit” does not implement the audit.

Statuses such as `ast_audit_rejected` may be retained as language-independent protocol values or renamed. Either way, tool output, runtime logic, and prompts must change together. Replace the source line 94 import exception with an explicit Lean import policy; do not allow the agent to import arbitrary modules or instances merely to pass validation.

### 1.5 Writing the Theorem Skeleton in Lean

Location: [lines 23–30](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L23-L30), [lines 39–40](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L39-L40), [lines 68–75](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L68-L75), [lines 122–128](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L122-L128), [lines 165–169](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L165-L169), [lines 185–187](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L185-L187).

These passages define more than parenthesis boundaries: they specify how `pose`, `set`, `have`, `assert`, `suff`, `enough`, and `have ->` are used to construct the skeleton. Migrate by proof function—to Lean local objects, named facts, goal transformations, and composition steps such as `let`, `have`, `suffices`, and `show`—rather than translating keywords one-to-one. [Lean tactic reference][lean-tactics].

Delegated exported facts still use `have h : P := (by ... )`. Preserve the distinctions between objects and propositions, proving intermediate facts before parent composition, and retaining useful existing user-written skeletons. Contract comments and region markers must also use valid Lean comment syntax, not Rocq comment syntax.

The SSReflect repeat-rewrite restrictions and `intuition` ban on source lines 185–186 also occur in the main prover; revise them consistently with `lemma.txt`. Do not treat an old Coq-specific audit rationale for a tactic as an intrinsic property of a similarly named Lean tactic.

### 1.6 `proof_plan` Matching, Parameters, and `normal_form`

Location: [lines 47–52](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L47-L52), [lines 70](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L70), [lines 85](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L85), [lines 109–111](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L109-L111), [lines 126–128](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L126-L128).

Preserve the structured candidate roles: `direct_apply`, `rewrite`, `transport`, `local_fact`, and `automation_hint`. But recheck each candidate route against real Lean declarations, parameter instantiation, and actual goals. The existence of a declaration name alone does not show that it can prove the node.

Change `normal_form: <coq_goal_shape>` to a Lean proposition or target contract elaborable in the current context. It must match the exported target rather than a vague label such as “sum equality” or “arithmetic fact.” Any remaining premises after candidate application must be justified by available hypotheses, explicit dependency nodes, or valid current certificates—not relabeled as though they were already in context.

**Contract fields (DECISIONS D10):** the file's contract comment carries `plan_node`, `depends_on`, `source`, `input`, `output`, `expected`, `normal_form`, `evidence`; the region marker carries `owner`, `admit_id`, `theorem`, `target`, `plan_node`. `kind` and `layer` are written only in the `proof_plan` node, never in the file (lines 70, 85, 86 and 126–128 of `prover.txt`; see `known-problem-fixes/prover.txt-fixes.md`).

Parameter handling also needs rewriting: distinguish inferable parameters, unresolved objects, instance-search failures, and genuine proof premises. Do not assume a whole class of binders must always be fixed before `apply`. Base decisions about the subgoals produced or solved by Lean `apply` and `refine` on the actual result of the current invocation. [Lean tactic reference][lean-tactics].

Retain plan freezing, constrained revision, metadata repair, and the distinction from semantic re-decomposition. The production and verification of supporting evidence must use Lean.

### 1.7 Proof Holes, Checkable Drafts, and Final Closure

Location: [lines 72–80](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L72-L80), [lines 92–94](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L92-L94), [lines 146–150](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L146-L150), [lines 184–188](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/prover.txt#L184-L188).

Replace draft `admit` / admitted leaves with an explicitly tracked Lean placeholder mechanism. `admit_id` may remain a stable task identifier: it is a ProsaBuddy protocol field, not a requirement to use Rocq’s `admit` tactic.

Replace the source line 80 message `No more goals, but there are some goals you gave up` with a project state such as “outer composition has been checked; only authorized leaf obligations remain unfinished.” An empty goal list after `sorry` consumes a goal is not evidence of completion.

Source line 92 must no longer describe an `Admitted.` → `Qed.` replacement. After all regions are merged, the main prover must validate the complete Lean theorem and review dependencies and original-declaration integrity under §0.3. Final acceptance still belongs to the main prover, not the lemma agent.

---

## 2. `lemma.txt`

### Responsibility

A long-running subagent owns exactly one frozen `proof_region` and continually builds, checks, and repairs its local proof. It may introduce helpers inside that region, but must not take over the enclosing theorem, sibling regions, or parent composition. Structural blockers must be escalated to the main prover with evidence. References: [lines 3–43](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L3-L43), [lines 47–74](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L47-L74).

### 2.1 Coq tools → Lean tools

Location: [lines 11–18](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L11-L18), [lines 52–64](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L52-L64), [lines 80–88](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L80-L88), [lines 215–218](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L215-L218).

Change the `.v`, `coq_session`, `petanque`, rocq-lsp/coq-lsp, `coqtop`, and `coqc` references in Available Tools and all later usage guidance as specified in §0.2. Also change the source of truth described on line 67 to the current controlled `.lean` source revision. Editing the Available Tools section alone is not enough.

### 2.2 Region Parsing and Edit Permissions

Location: [lines 35–43](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L35-L43), [lines 73](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L73), [lines 94–96](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L94-L96), [lines 193–194](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L193-L194).

```text
37: Empty `{}` proof blocks are partition boundaries.
39: ... exported target statement ... plus the complete `{ ... }` proof block.
73: ... markers are wrongly placed inside the target's braces ...
```

Replace these rules in parallel with `prover.txt` using the five conventions in §0.1: a complete `have h : P := (by ... )`, an end marker after the matching outer `)`, robust delimiter matching, one delegated-target format, and noneditable parent composition outside the region.

Source line 37 must no longer forbid `by` proofs. The Lean rule should prohibit removal of the project-required outer wrapper, not prohibit `by`. An empty `{}` must not be mechanically replaced with an empty `()`. If a wrapper is missing or markers are misplaced, and repair would exceed this region’s authority, escalate rather than silently widening its scope.

A target appearing inside the editable region is not permission to change the proposition. Its name, statement, and intended use remain the main prover’s contract; if the target itself is incorrect, use `needs_subgoal_remodel`.

### 2.3 SSReflect/Coq Tactics, Libraries, and Local Helpers

Location: [lines 63](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L63), [lines 78](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L78), [lines 97–103](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L97-L103), [lines 112–116](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L112-L116), [lines 213–214](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L213-L214).

The `rewrite !...` / `rewrite -!...` rules on source line 213 and the `intuition` restriction on line 214 must be rewritten against Lean tactics and the project’s audit policy. Tactics such as `exact` and `apply` also exist in Lean, but Coq syntax and debugging practices must not be copied unchanged.

Replace source line 63’s `bigop/minn rewrite mismatch` and line 78’s `bigop algebra` with corresponding summation, counting, filtering, and `Nat.min` problems from the actual translated interfaces. Use verified Lean Prosa/Mathlib APIs rather than assumed equivalents.

Update source lines 97–103 concerning `pose` / `have` and proof comments. Keep the strategy “form a concrete proof idea before introducing necessary helpers,” but illustrate objects, local facts, and branch goals using actual Lean proof syntax.

### 2.4 Rocq Local Proof Loop → Lean Local Proof Loop

Location: [lines 61–66](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L61-L66), [lines 76–89](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L76-L89).

```text
80: Open `coq_session` or `petanque` ...
81: Snapshot ...
83: ... `coq_session step` / `petanque run` ...
84: ... `coq_session goal`, `petanque goals`, or `lsp proofGoals` ...
85: ... write the validated proof fragment ... and snapshot ...
86: ... Expand `by`, fix bullet/focus structure ...
87: ... `coqtop Check`/`Print`/`Search` ...
88: Run `coqc` ...
```

This section defines an iterative workflow: choose the next small step → prove incrementally → inspect the goal → preserve valid progress → diagnose failures → look up lemmas → edit and validate. Retain the loop, but reimplement execution using the Lean backend: make a small edit in the current owned region and revision, inspect the corresponding Lean goals and diagnostics, query actual declarations as needed, record stable validated revisions, and certify the appropriate local scope.

Do not assume that the only workflow is “execute tactics in a session, then mirror the proof into a file.” In a source-driven design, the controlled source revision and its checking results are authoritative. Source line 86 must not be read as “remove Lean `by`”: instead, unpack overly compressed tactics, check `·` / `case` / `next`, nested `have` blocks, and indentation, then inspect the actual current goal. [Lean proof-state documentation][lean-goals].

### 2.5 Prefix Validation and Proof-Hole Completion

Location: [lines 35–38](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L35-L38), [lines 52–53](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L52-L53), [lines 94–96](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L94-L96), [lines 218–223](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L218-L223).

The current rule resolves the first unfinished hole in a region before advancing to the next block. That prefix ordering can remain, but its completion criterion must be implemented for Lean.

`lemma_prefix_validation: ok` must mean that the specified local block and its required prefix passed the appropriate checks in the correct context, and that the current blocker was genuinely discharged. It cannot merely mean that the first error moved down the file, that current tactics raised no error, or that the full file compiles with placeholders still present.

If a later sibling still contains `sorry`, do not automatically reject this region based solely on dependencies printed for the entire theorem. Check the region’s actual proof term or an audited context-faithful validation slice, and verify certificates for the producer nodes it actually uses. Conversely, do not publish a completion certificate by treating uncertified upstream facts as unrecorded extra assumptions.

Backend implementation note: `have` introduces a local fact. Do not assume that it has a global declaration name that can be passed directly to `#print axioms`. Local certification requires suitable proof-term checking or an audited extraction/validation mechanism; the theorem as a whole is checked separately at the end.

### 2.6 Context Audit and Parameter/Instance Diagnostics

Location: [lines 69–74](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L69-L74), [lines 186](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L186).

The original `coq_session inspect` examines hidden parameters, Section/Module instantiation, implicit arguments, and alias normalization. The Lean replacement must produce verifiable diagnostics concerning the actual declaration’s parameters, local context, instance resolution, metavariables, and unfolding.

Protocol fields such as `context_audit`, `context_mismatch_basis`, and `failed_local_bridge`, together with statuses such as `convertible`, `not_convertible`, and `inconclusive`, may remain. The model must not invent verified results, and Rocq audit IDs cannot be reused as evidence for Lean.

A failed or inconclusive definitional-convertibility check does not automatically establish that the proposition is false or that the two statements cannot be proved equivalent. It means only that the requested conversion was not established by the current check; a local bridge, further diagnosis, or evidence-backed escalation may be needed.

### 2.7 Progress, Transactions, and Certificate Revisions

Location: [lines 128–135](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L128-L135).

Retain the `hard`, `structural`, and `debug` progress levels, but replace source line 130’s `final Qed. success` with the Lean final-acceptance state. A successful tactic step, shifted error location, modified marker, or file that remains checkable only because of placeholders does not automatically create a new completion certificate.

On recovery, use the transaction’s authoritative staged source, revision, and hash rather than reverting to an older workspace file. Lean certificates must bind the exact checked source, region/target, relevant dependencies, and environment. When source or upstream context changes, revalidate certificate applicability instead of blindly reusing an old snapshot.

### 2.8 AST Audit, Output Protocol, and Theorem-Closure Authority

Location: [lines 30–43](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L30-L43), [lines 169–194](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L169-L194).

Migrate the Rocq AST audit on source line 43 to a Lean declaration-, scope-, and dependency-integrity audit. The `proof_result` schema may be preserved, but `status = solved` must require the local certification defined in §0.3—not just a nonempty `proof_text` or complete region markers.

Source lines 42 and 194 must no longer describe authority as “do not replace `Admitted.` with `Qed.`.” Instead, prohibit edits to theorem declarations, outer proof composition, and other protected content outside the owned region. Final merging and acceptance remain the main prover’s responsibility.

Retain `solved` / `split` / `escalate`, the single immediate-child convention, and in-session local decomposition. Do not introduce new result fields or enum values merely because the language changed to Lean.

---

## 3. `fixer.txt`

### Responsibility

After another agent encounters a specific error, it sends the error, affected source, current goal, local context, and previously attempted approaches to fixer. Fixer makes and verifies the smallest local repair. If fixing the error requires changing an import, the target signature, or the outer proof structure, it must escalate rather than widening its scope. Fixer is a wide fallback repair agent, so its actions do not demonstrate lemma-local isolation. References: [lines 1–35](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/fixer.txt#L1-L35).

### 3.1 Convert Error Inputs and Goal/Context Information to Lean

Location: [lines 6–9](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/fixer.txt#L6-L9).

```text
6: Error: The exact Coq error message ... coqc error-only output
8: Goal: ... focused goal + local hypotheses from `Show.`
```

Use Lean diagnostics, error locations, the goal list, the focused goal, and its local context from the current controlled `.lean` source revision. Replace `Show.` with the goal-query mechanism actually supported by the Lean backend. Do not repair an error from one revision or position using goals retrieved from another.

The environment description on source line 9 must also include the actual local parameters, instances, and scopes that affect Lean elaboration. Simply changing the word Coq `Section` to Lean `section` is not sufficient to align contexts.

### 3.2 Rewrite the Entire `Common Coq Error Patterns` Section

Location: [lines 55–62](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/fixer.txt#L55-L62).

Keep the “error → likely cause → minimal diagnostic/repair” structure, but do not impose a mechanical one-to-one mapping from Coq error strings to Lean errors. The table lists issues the Lean version should cover, not fixed strings guaranteed to appear verbatim across Lean versions.

| Original pattern | Issue to cover in Lean | Minimal response |
| --- | --- | --- |
| `Unable to unify` | Type mismatches such as `type mismatch` / `application type mismatch` | Compare actual versus expected types, arguments, rewrite direction, and goal representation. |
| `Not found` / `Cannot find` | `unknown identifier` or a declaration out of scope | Check names, namespaces, visibility, and actual imports; escalate if importing requires unauthorized changes. |
| `Syntax error` from a missing Coq period | Invalid indentation inside `by`, tokens, parentheses, or branch structure | Identify the actual syntax boundary; do not mechanically add Coq sentence-ending periods. |
| `No matching clauses` | `match` / `cases` branch or pattern problems | Inspect the actual type, constructors, and Lean branch rules. |
| `Cannot infer` | Implicit-argument inference, holes, metavariables, or typeclass synthesis | Distinguish an unresolved data parameter, missing instance, and unproved premise before supplying what is needed. |
| Section-generalized foralls | Parameterized declarations and goals generated by `apply` / `refine` | Inspect actual types; do not treat every `∀` as an instance argument or mistake ordinary premises for obligations that need no proof. |

Build specific diagnostic examples and tests against the project’s pinned Lean toolchain. In particular, `failed to synthesize` does not by itself mean a theorem lacks a mathematical hypothesis; it may reflect elaboration or instance resolution.

### 3.3 Repair Validation and Lookup Tools

Location: [lines 16–17](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/fixer.txt#L16-L17), [lines 35](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/fixer.txt#L35), [lines 66–73](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/fixer.txt#L66-L73).

Replace `coq_session step`, `coqc`, and `coqtop Check/Search` with real Lean editing, lookup, and validation interfaces. Bind the repair result to the staged revision actually modified. A tactic succeeding in a scratch fragment does not establish that the whole theorem or current region has been completed.

### 3.4 Skeletons, Transactions, and Controlled Repair Scope

Location: [lines 25–35](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/fixer.txt#L25-L35).

Adapt source line 26’s protection of the `pose` / `have` skeleton to Lean local objects, named facts, wrappers, and outer composition. Preserve the running-region takeover protocol on line 25 and the staged-source/stale-view recovery rules on lines 32–34, but verify that Lean editing and checking use the same transaction.

A “successful repair” under source line 35 requires validation evidence matching the current revision: the reported error is fixed, no out-of-scope code was changed, and no new placeholder or assumption has been used to conceal the problem. Fixing one error need not discharge all other obligations; report the actual validation scope.

Retain the `<fix>` / `<escalate>` output format on source lines 37–52 and the permissions forbidding new files or delegated tasks. Language migration does not implicitly relax those restrictions.

---

## 4. `diagnoser.txt`

### Responsibility and Retained Behavior

Diagnoser only diagnoses and classifies errors. It must not edit proofs, create files, or delegate subagents. Its current top-level error categories are largely language-independent and can be retained. References: [lines 13–23](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/diagnoser.txt#L13-L23), [lines 44–57](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/diagnoser.txt#L44-L57).

```text
local_tactic_failure
definition_unfolding_needed
library_shape_mismatch
missing_preceding_bridge
missing_uniqueness_bridge
missing_context_strengthening
theorem_spine_mismatch
subgoal_modeling_error
sibling_syntax_error
not_local_obligation
```

`sibling_syntax_error` remains possible in Lean—for example, a neighboring syntax error or malformed wrapper may prevent a later local task from elaborating correctly.

### 4.1 Update Coq Inputs and Lookup Tools, Not Just the Role Name

Location: [lines 1–16](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/diagnoser.txt#L1-L16).

Replace Coq compiler/LSP errors with Lean diagnostics, and `coqtop` lookup with Lean type and declaration queries. The goal/context on source lines 8–9 must refer to the same source revision and include the actual local parameters and instances. The change is modest, but it is more than a find-and-replace of “Coq.”

### 4.2 Add Lean Diagnostics While Preserving Protocol Compatibility

Location: [lines 27–42](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/diagnoser.txt#L27-L42), [lines 46–57](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/diagnoser.txt#L46-L57).

Keep `<diagnosis>` and fields including `error_category`, `error_subcategory`, `recommended_escalation_type`, `is_local`, `suggested_owner`, and `minimal_next_action`.

Represent Lean implicit-argument issues, instance-synthesis errors, elaboration mismatches, and branch/indentation failures within `by` initially via `error_subcategory` and explanatory fields. Do not invent new top-level categories unsupported by the runtime merely by editing the prompt; synchronize schemas, callers, and tests if the enum truly must grow.

`missing_context_strengthening` must still propose deriving and threading bridge facts from existing assumptions. Missing an instance is not a blanket justification for adding a new hypothesis to the original theorem.

---

## 5. `explore.txt`

### Responsibility

This is a read-only search helper: it finds definitions, lemmas, or existing proof patterns relevant to the current proof step and explains where they are and how they support the task. It neither proves goals nor edits source. References: [lines 1–21](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/explore.txt#L1-L21).

### 5.1 Small Terminology Updates for Search Targets

Location: [lines 7](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/explore.txt#L7), [lines 15–16](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/explore.txt#L15-L16).

```text
7: ... a caller's paper step, equation, or local `pose` / `have` obligation
16: ... supports a `pose`, a `have`, or only Coq technical support
```

Refer to Lean declarations, local definitions, local facts, the current subgoal, and Lean-specific technical support. Retain Glob/Grep/Read search methods, the requirement to find evidence for the caller’s concrete question, and return of locatable file paths.

### 5.2 Search Roots and Read-Only Constraints

Location: [lines 10–19](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/explore.txt#L10-L19).

The current prompt does not hard-code a Rocq Prosa search root. Switching the search scope to Lean Prosa/Mathlib must be handled in the caller, workspace, or search-tool configuration; this entire change should not be attributed to `explore.txt`.


---

## 6. `compaction.txt`

### Responsibility

When context grows too long or work must be handed off, compaction summarizes the current owned task: goals, hypotheses, validated fragments, failures, protected boundaries, remaining obligations, and next actions. The next agent should continue rather than repeat earlier exploration. Retain the core summary structure. References: [lines 1–20](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/compaction.txt#L1-L20), [lines 22–89](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/compaction.txt#L22-L89).

### 6.1 Replace `.v` References and Validation Sources

Location: [lines 12–18](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/compaction.txt#L12-L18), [lines 38–43](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/compaction.txt#L38-L43), [lines 49–53](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/compaction.txt#L49-L53).

Change `.v` to `.lean` on source lines 12 and 38. Replace `coq_session` / `petanque` / `coqc` state and validation sources on lines 18, 43, and 51 with Lean goals, local context, diagnostics, source positions, and the actual backend checking results.

Convert source line 43’s Coq bullet/focus metadata to Lean’s current goals, branch/local-proof position, and required scope information; do not mechanically preserve old session-state fields.

### 6.2 Recovery Must Use the Current Authoritative Source Revision

Location: [lines 12–19](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/compaction.txt#L12-L19), [lines 36–43](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/compaction.txt#L36-L43), [lines 75–85](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/compaction.txt#L75-L85).

The continuation summary should preserve the current file path, staged source revision/hash, owned region/target, last validation position and revision, certificates and their dependencies, and the next verification action. If a transaction is active, resume from its authoritative staged source rather than a stale on-disk file or a proof reconstructed from the summary.

The summary is a handoff artifact, not a restorable Lean runtime object. Old goal IDs or snapshots may be invalid after an LSP session or process restart. Reload the corresponding source revision and query the state again; do not treat old proof-state text as current checking output.

### 6.3 Preserve Progress Classes but Record Certification Scope

Location: [lines 16–18](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/compaction.txt#L16-L18), [lines 49–53](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/compaction.txt#L49-L53).

Keep `validated`, `in_file_but_unvalidated`, and `speculative_or_reverted`. For `validated`, record whether the evidence concerns a tactic prefix, a complete region, or the final theorem, together with remaining placeholders and valid certificates. Avoid describing a checkable draft as a completed proof when compacting context.

Unchanged: summarize only the current agent-owned task, preserve ownership, avoid expanding into siblings, retain failed proof routes, and record user constraints.

---

## 7. `whole-lemma.txt`

### Responsibility and Difference from `lemma`

It uses a small-step interactive proving discipline similar to the lemma agent, but owns the entire target theorem. It does not build the main prover’s paper-derived DAG, create first-level `proof_region` / `admit_id` delegation, or call `lemma` for first-level splits. The source explicitly calls it a wide fallback direct prover. References: [lines 1–3](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L1-L3), [lines 19–27](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L19-L27), [lines 58–60](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L58-L60).

“Direct proof” does not mean a single tactic, and it does not forbid local `have` facts. The key difference is that this path does not use theorem-level DAG delegation. Describing it as available for a direct probe is a reasonable intended use, but its actual invocation conditions are determined by the caller/runtime, not by this prompt alone.

### 7.1 Tools and File Extensions

Location: [lines 3–15](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L3-L15), [lines 20](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L20), [lines 31–41](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L31-L41), [lines 45–54](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L45-L54), [lines 64](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L64).

Migrate the tools on source lines 7–15 and every later Rocq tool invocation according to §0.2. Change `.v` to `.lean` on source lines 3, 8, 20, 31, 36, and 64. Keep the current controlled source as the output location; proof code must not exist only in the agent’s answer.

### 7.2 Whole-Theorem Interactive Proof Loop

Location: [lines 31–41](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L31-L41).

```text
31: Read the target `.v` theorem
32–33: Search relevant definitions/lemmas/proof patterns, then start proving directly
34–35: `coq_session` / `petanque`; small tactics, goal inspection, snapshots, rollback
36–37: Write back to `.v` and repair based on LSP/session/compiler feedback
38–39: Diagnose compressed Coq `by` and bullet/focus issues; query `coqtop`
40–41: Preserve validated fragments and run `coqc` checking
```

Migrate this loop similarly to `lemma.txt`: keep “plan the next step → edit a small proof fragment → inspect real goals/diagnostics → repair → milestone validation,” but execute through Lean source and actual backend capabilities. The certification scope is the whole theorem rather than a single owned region.

### 7.3 Local Constructs, Libraries, and Tactic Policy

Location: [lines 7](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L7), [lines 23–26](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L23-L26), [lines 32–33](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L32-L33), [lines 45–53](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L45-L53).

Replace the preference for Rocq Prosa facts with reuse of actual Lean Prosa/Mathlib declarations. Change the `pose`, `set`, `have`, and `assert` guidance on source line 48 to appropriate Lean local objects, facts, and goal-transformation constructs.

Synchronize the compressed Coq `by`/bullet repair rules on source line 38 and the SSReflect/`intuition` guidance on lines 51–52 with the other proving prompts. Do not import Coq-specific rationales for banning a tactic merely because Lean has a tactic with the same name.

### 7.4 Completion Criteria and Retained Rules

Location: [lines 21–27](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L21-L27), [lines 54–64](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/whole-lemma.txt#L54-L64).

Expand “continue until the file compiles” into the final theorem acceptance criteria in §0.3: preserve the original declaration, check that the proof and its dependencies contain no unfinished obligations, and enforce the environment and assumption policies. Ownership of the whole theorem does not authorize changing the theorem statement, adding assumptions, or arbitrarily modifying global context.

Retain source lines 3 and 22 (“do not read `proof.tex` or create paper-skeleton regions”) and line 60 (“do not call `lemma` to create first-level regions”). These are strategic differences of the direct-proof path, not Rocq-specific features to remove during migration.

---

## 8. `title.txt`

Location: [lines 1–44](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/title.txt#L1-L44).

This prompt only generates conversation titles, so it requires no migration. Its tool-use restrictions do not apply to proof agents.

---

## 9. Prompt and Backend Changes That Must Be Coordinated

The following table is a coordination checklist. It does not claim that the Lean implementations already exist, nor that every TypeScript implementation has been audited line by line.

| New prompt requirement | Backend capability to verify or implement | Risk if omitted |
| --- | --- | --- |
| Delegated targets use `:= (by ... )` | Region extraction, wrapper validation, source-range mapping, edit-scope guards | Agents generate the new syntax while the old parser still determines boundaries using Coq braces. |
| Parent composition is outside `lemma` ownership | Owned-region boundaries, declaration contracts, detection of exterior source changes | A local agent may gain unauthorized edit scope by moving markers or mismatching parentheses. |
| Placeholders exist only in permitted locations | Hole detection, prefix validation, distinction between drafts and solved states | A compilation result containing placeholders is incorrectly labeled `solved`. |
| Lean target matching in `proof_plan` | Parameter instantiation, candidate application, residual-premise audits, `normal_form` validation | A plan appears sound but its actual application has unresolved arguments or premises. |
| Lean context audit | Same-revision local context, instance/metavariable/convertibility diagnostics, evidence-ID verification | Old Coq audit output or unsupported model assertions are mistaken for verified Lean evidence. |
| Lean certificates | Verification records bound to source, target, dependencies, and environment, with invalidation rules | Success from a stale revision is reused for new code. |
| Lean declaration-integrity audit | Verification of original targets, surrounding context, and proof dependencies | Proving a different proposition is accepted as completing the original task. |
| Source-driven interactive proving | LSP synchronization with staged source, controlled fragment validation, and state refresh after recovery | The agent edits new source based on stale goals or outdated diagnostics. |
| Lean tool list and protocol | Agent permissions, tool registration, schemas, state enums, and runtime-injected instructions | A prompt requests nonexistent tools or returns output the runtime cannot parse. |

Begin coordinated review with agent registration, tool calls, proof workflow, proof projection/region extraction, edit transactions, checkpoints, and audits. Protocol names such as `proof_region`, `admit_id`, `checkpoint`, and `ast_audit_rejected` do not all need renaming. Prefer backward-compatible names while migrating language-specific interpretation and evidence.

### 9.1 Terminology Must Be Consistent Across Files

Libraries and syntax. Review role descriptions, `.v` references, Coq snippets, SSReflect rules, and MathComp examples throughout. Updating only headings and Available Tools is insufficient. Do not assume that tactics such as Lean `have`, `apply`, and `exact` do not exist.

Tools. Use only names actually registered by the backend; do not invent `lean_session`. Distinguish source checkpoints from in-process proof-state snapshots. Do not assume an old session state can resume automatically in the next agent turn.

Acceptance. Distinguish “a diagnostic disappeared,” “a tactic or prefix is valid,” “a region is complete,” and “the theorem is complete.” Temporary `sorry` placeholders, unfinished dependencies, stale certificates, and unchecked audits must not be described as final success.

Ownership. Preserve permission differences among the main prover, lemma, fixer, diagnoser, explorer, and whole-lemma agents. Concurrent/running region takeovers, accepted-plan revision windows, and records of failed routes must continue to follow runtime authorization.

---

## 10. Migration Completion Checklist

- [ ] Both `prover.txt` and `lemma.txt` explicitly contain all five parenthesized-region requirements from §0.1.
- [ ] Every delegated target uses `:= (by ... )`; internal indentation and branching still obey Lean syntax.
- [ ] Parser tests cover nested parentheses, `)` inside strings, comments, missing closing parentheses, and neighboring regions. Ambiguous boundaries never expand edit permissions.
- [ ] Parent composition follows the end marker; unauthorized changes to the target proposition or exterior code are blocked or escalated.
- [ ] Migration covers downstream workflows, examples, and validation rules, rather than changing only `.v`, `coqc`, and tool names.
- [ ] Every tool referenced in the prompts matches real permissions, schemas, and runtime-injected instructions; no Lean APIs have been invented.
- [ ] Draft placeholders, valid prefixes, completed regions, and completed theorems have distinct, testable acceptance criteria.
- [ ] Tests show that a tactic consuming the goal while leaving a placeholder cannot return `solved`.
- [ ] Tests cover a region with no local placeholder that nonetheless depends on an unfinished helper/producer, ensuring those dependencies are not missed.
- [ ] Independent regions are not rejected because unrelated siblings remain unfinished, while real dependencies are still audited.
- [ ] Certificates, goals, and diagnostics correspond to the same source/environment revision; stale-view and recovery paths are tested.
- [ ] The meaning and fields of `proof_plan`, context audits, and result JSON agree between agents and runtime.
- [ ] The final theorem passes Lean validation, dependency review, and integrity auditing against the original target and controlled environment.
- [ ] Every new Lean example, error pattern, and validation command has been tested against the pinned project toolchain; unverified items are labeled explicitly.

In summary, this migration requires more than renaming Rocq tools. It must also migrate how the skeleton is constructed, how regions are delimited, how proof state is queried and recovered, and how local versus final proof completion is certified. Core principles—small-step validation, preserving verified progress, reasoning from actual goals, and never changing the assigned proposition outside one’s authority—remain intact.

---

## Appendix: Lean Technical References

Check syntax and proof mechanisms in the Lean documentation below against the project’s pinned `lean-toolchain`, dependency versions, and actual diagnostics.

- [Lean: Running Tactics and `by` Syntax][lean-running]
- [Lean: Proof States and Multiple Goals][lean-goals]
- [Lean: Tactic Reference, Including Local Facts, Application, and Goal Construction][lean-tactics]
- [Lean: Validating Proofs, Dependencies, and `#print axioms`][lean-validation]

[lean-running]: https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Running-Tactics/
[lean-goals]: https://lean-lang.org/doc/reference/latest/Tactic-Proofs/
[lean-tactics]: https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/
[lean-validation]: https://lean-lang.org/doc/reference/latest/ValidatingProofs/
