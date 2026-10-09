# Lean 4 Migration Notes for `task.ts`

**Purpose**: Create and resume subagent tasks, delegate proof regions, and audit, validate, and accept submitted results.

**1. Proof Delegation Entry Point | Modify, Medium**

- **Location**: [Line 276: beginProofEditTransaction](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L276).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Proof-transaction file check, [From line 284](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L284):

```ts
  if (!binding?.file.endsWith(".v")) return undefined
  const requestedFile = input.lemmaAssignment?.file ?? input.repairAssignment?.file ?? binding.file
  const file = path.isAbsolute(requestedFile) ? requestedFile : path.resolve(Instance.directory, requestedFile)
```

- **Current behavior**: The transaction entry point requires a `.v` binding; related branches use Coq prover names and compilation-recovery guidance.
- **Recommendation**: Support `.lean` and the new proof-tool identifiers; retain theorem/region binding and parent-child task inheritance so Lean tasks do not fall into the ordinary task path without proof transactions.

**2. Gap Recognition and Task Instructions | Modify, Large**

- **Location**: [Line 444: countExplicitGapPlaceholders](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L444).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq gap counting, [From line 444](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L444):

```ts
function countExplicitGapPlaceholders(source: string) {
  return Array.from(source.matchAll(/\bAdmitted\.|\badmit\b/g)).length
}
```

- **Current behavior**: Counts `Admitted`/`admit`; `withLemmaAssignment` generates Coq have/assert, brace, and terminator constraints.
- **Recommendation**: Identify `sorry` gaps using Lean local-proof ranges; require complete Lean regions as deliverables, preserving indentation and exported targets, and remove Coq terminator-editing instructions.

**3. Goal Context Audit | Modify, Large**

- **Location**: [Line 674: contextAuditReview](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L674).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Context audit lookup, [From line 683](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L683):

```ts
  const recorded = submitted?.audit_id
    ? findContextNormalizationAudit(sessionID, submitted.audit_id)
    : undefined
```

Reading the current Coq proof state, [From line 1038](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L1038):

```ts
          const liveProofState = currentCoqProofState(ctx.sessionID)
          const liveProofStateMatchesBaseline = Boolean(
            liveProofState &&
```

- **Current behavior**: Reviews context-normalization audits from `coq-session`; execution reads `currentCoqProofState`.
- **Recommendation**: Use Lean goals, binders, instance context, and audit results from the same source version; retain source hash checks and structured failure reports without relying on Coq goal-text shapes.

**4. Subtask Acceptance | Modify, Large**

- **Location**: [Line 402: astAuditRepairPrompt](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L402).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Language constraints to replace in AST audit repair guidance, [Line 409](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L409):

```ts
    "Continue in this same subagent session and repair the current staged source. Preserve the original target declaration and every command outside your authorized proof scope; do not replace Qed with Admitted/Defined/Abort or introduce axioms, options, proof modes, meta commands, controls, attributes, or untrusted imports/plugins.",
```

- **Current behavior**: Calls `CoqAstAudit` when accepting changes; repair guidance prohibits replacing Qed with Admitted/Defined/Abort, among other changes.
- **Recommendation**: Use Lean declaration and proof-dependency audits with Lean completion criteria; retain the sequence of repair after audit failure, revalidation, and then merge.

**5. Corresponding Description File | Modify, Small**

- **Location**: [task.txt](../../../prosabuddy-rocq/packages/opencode/src/tool/task.txt#L33).

**Description text to update** (excerpt):

Coq terminator restrictions, [Line 29](../../../prosabuddy-rocq/packages/opencode/src/tool/task.txt#L29):

```text
10. A lemma task must not close the outer theorem or edit theorem-level terminators such as `Admitted.` or `Qed.`. After the last region is solved, final merge and final validation return to the prover.
```

- **Current behavior**: Includes Coq proof terminators, tool names, and SSReflect/intuition restrictions.
- **Recommendation**: Update Lean regions, tools, and proof-completion constraints together; retain general task instructions.

Task creation, delegation ownership, retries, region acceptance, and result merging can be retained.
