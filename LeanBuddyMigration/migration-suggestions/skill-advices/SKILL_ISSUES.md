# Issues in the original skills

These concerns also apply in Rocq/Coq. They are separate from differences introduced by a Lean migration. The suggestions below have not been applied to the original rules or examples.

## count-bridging

### 1. Symptoms are sometimes presented as confirmed causes

[Problem Shape](count-bridging/SKILL.md#lean-review-problem-shape) and [Failure Signatures](count-bridging/SKILL.md#lean-review-failure-signatures) attribute failures to representation drift or an unfinished Bool/Prop bridge. Those are possible explanations, but an error alone does not establish them.

**Recommendation:** Present candidate causes and the goal, types or execution evidence needed to confirm them. Check the actual expression, definitions and rewrite direction before requiring a bridge.

## failure-signature

### 1. Missing literal text does not necessarily require a new lemma

[Practical Rule](failure-signature/SKILL.md#lean-review-4) says:

> If the answer is no, add a bridge lemma instead of trying another algebraic rewrite.

The expression may match after unfolding, or the problem may be the type, location or rewrite direction.

**Recommendation:** Keep the observation checklist, but require a new equality only after confirming that a mathematical bridge is actually missing.

### 2. An error message does not establish one normalization cause

[Common Messages](failure-signature/SKILL.md#lean-review-2) maps general errors to specific expression states. The same message can arise for other reasons.

**Recommendation:** Distinguish possible causes from verified causes. Record the goal, theorem type and failed step before choosing a repair.

## math

### 1. Literal matching is too strong as a universal rewrite criterion

[Procedure](math/SKILL.md#lean-review-3) says:

> Ask whether that left-hand side occurs syntactically in the current goal.

> If the answer is no, stop and choose a bridge step instead.

Printed syntax alone does not account for definitional equality or parameter inference. This limitation already exists in Coq.

**Recommendation:** Use the visual check as an initial observation, then inspect types, arguments, unfolding and direction. Judge progress by the actual rewrite result rather than literal similarity alone.

### 2. Diagnostic messages are treated as root causes

[Common Failure Signatures](math/SKILL.md#lean-review-9) associates errors with missing multiplication nodes or representation drift. These may be useful hypotheses, but need supporting context.

**Recommendation:** Write each entry as a possible cause, a confirming check, and an action after confirmation. Support frequency claims such as “usually” with observed cases.

### 3. Some original resource links do not resolve

The original references to `./assets/bridge-lemma-templates.v`, `./skill_count.md` and `./references/failure-signatures.md` do not match files in this package.

**Recommendation:** Locate missing resources or correct the paths to real files. The current count skill is at `../count-bridging/SKILL.md`. Do not assume a resource exists merely by changing its extension. Original links remain unchanged in this review.

## parameter

### 1. A dependency does not prove that an argument must be supplied manually

[What Must Be Fixed First](parameter/SKILL.md#lean-review-2) lists parameters appearing in later types as early-bound inputs. That does not establish whether the current goal or other arguments can already determine them.

**Recommendation:** Treat the dependency list as inspection guidance. Demonstrate the unresolved input that actually blocks this application before requiring explicit binding.

### 2. The restriction on explicit applications needs a clear scope

[Hard Rule](parameter/SKILL.md#lean-review-5) prohibits a fully explicit theorem term for this failure mode. The restriction is already scoped; the ambiguity is whether it rejects guessing argument positions or also rejects a fully checked explicit term.

**Recommendation:** Explain the intended workflow restriction. Do not describe explicit terms as inherently invalid or claim that a different application style makes the mathematical theorem stronger.

### 3. Different application failures need separate diagnoses

[Failure Signals](parameter/SKILL.md#lean-review-3) groups several errors under early binding. Supplying a proof where data is expected may indicate an argument-position error rather than an unresolved instance.

**Recommendation:** Show the expected type and supplied term before classifying the failure. Accept raw errors in the input hint instead of requiring the user to diagnose early binding first.

## goal

### 1. A goal count other than one is not automatically an error

[Hard Recovery Protocol](goal/SKILL.md#lean-review-6) says:

> If the goal count is still not exactly one, repeat this protocol.

Splitting a goal can legitimately create several obligations; completing one can leave none. Requiring recovery until the count is one can reject valid progress in Coq too.

**Recommendation:** Record the count, but recover only when the active goal or branch differs from the intended state. Enforce a single-goal precondition only for an operation that actually requires it.

### 2. Later errors are not necessarily secondary noise

[Core Rule](goal/SKILL.md#lean-review-2) postpones later application errors until the goal count returns to one. Independent name, type or argument errors can still be genuine causes.

**Recommendation:** Defer an error only when evidence shows that it follows from an earlier state error. Otherwise inspect its location and context normally.

### 3. Splitting need not always wait for unfolding the goal

[Hidden Goal Head Before Case Split](goal/SKILL.md#lean-review-4) treats visible goal-head syntax as a general prerequisite. Establishing cases and rewriting the goal using those cases are different operations.

**Recommendation:** Decide what the split should establish, then unfold only where the next operation actually needs the definition exposed.

### 4. Linear handling of multiple goals is not inherently invalid

[Anti-Patterns](goal/SKILL.md#lean-review-9) rejects linear tactics after branching. The actual risk is losing track of the active goal, not linear notation itself.

**Recommendation:** If bullets are a project convention, state that as an organization rule. Distinguish violating that convention from applying a tactic to the wrong goal or leaving a branch unfinished.

## tactics

### 1. New branches do not by themselves imply a structural fault

[Required Procedure](tactics/SKILL.md#lean-review-4) and [What To Do After Expansion](tactics/SKILL.md#lean-review-6) require structural repair when branches appear. Those branches may be the intended result.

**Recommendation:** Check whether the branches and active context match expectations before classifying the state as broken.

### 2. Rewrite failure is not only a printed-shape mismatch

[First Revealed Error](tactics/SKILL.md#lean-review-5) treats literal mismatch as the explanation. Types, implicit arguments, definitions and direction can also matter in Coq.

**Recommendation:** Treat printed shape as one clue and verify the attempted equality against the actual context.

### 3. Routing paths refer to an older package layout

[What To Do After Expansion](tactics/SKILL.md#lean-review-6) refers to `skill_goal.md` and `.github/skills/coq-proof-state-discipline/skill_math.md`.

**Recommendation:** In a future packaging repair, use the actual paths, currently `../goal/SKILL.md` and `../math/SKILL.md`. This is a packaging issue, not a language-migration difference; the original references remain unchanged here.
