# Lean 4 Migration Notes for `coqc.ts`

**Purpose**: Invoke the Coq compiler to check proof files and feed compilation results into proof progress, transaction commits, and final validation.

**Verification (decided 2026-10-09):** per-step checks use Lean LSP diagnostics or `lake env lean` on the staged file; final verification is `lake build` of the module plus the integrity audit — see [`BACKEND_DECISION.md`](../../BACKEND_DECISION.md).

**Decided 2026-10-09 (DECISIONS D2):** the Lean tool is named `lean_check` (`lake env lean <file>` on the staged file).


**1. Source Files and Compilation Entry Points | Modify, Medium**

- **Location**: [Line 45](../../../prosabuddy-rocq/packages/opencode/src/tool/coqc.ts#L45).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

File type restriction, [From line 45](../../../prosabuddy-rocq/packages/opencode/src/tool/coqc.ts#L45):

```ts
    if (!filepath.endsWith(".v")) {
      throw new Error("File must be a .v (Coq source) file")
    }
```

Coq compilation command, [Line 84](../../../prosabuddy-rocq/packages/opencode/src/tool/coqc.ts#L84):

```ts
      const args = [...CoqProject.coqcCmd(), ...resolved.flags, ...extraFlags, filepath]
```

- **Current behavior**: Requires `.v` and compiles through `CoqProject.resolve/coqcCmd`; uses `Validation.prefix` when a transaction exists.
- **Recommendation**: Accept `.lean` and use the same Lean project environment for ordinary and staged source; distinguish single-file checking from `lake build`, and ensure validation does not compile only the older on-disk version.

**2. Coq Style Checks and Error Feedback | Modify, Medium**

- **Location**: [Line 54](../../../prosabuddy-rocq/packages/opencode/src/tool/coqc.ts#L54).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq tactic guard, [From line 54](../../../prosabuddy-rocq/packages/opencode/src/tool/coqc.ts#L54): 

```ts
    assertNoRewriteBangInCoqFile(filepath, coqcSource)
    assertNoIntuitionInCoqFile(filepath, coqcSource)
```

Compiler diagnostic parsing, [From line 282](../../../prosabuddy-rocq/packages/opencode/src/tool/coqc.ts#L282):

```ts
    const diagnostics = parseCoqCompilerOutput(stdout, stderr)
    if (stagedValidation) {
```

- **Current behavior**: Runs SSReflect style checks before compilation; uses `parseCoqCompilerOutput` and Coq skill hints after failure.
- **Recommendation**: Remove Coq tactic restriction calls and use Lean diagnostics and hints, while retaining the flow that passes error locations to the workflow.

**3. Completion Criteria and Certificates | Modify, Large**

- **Location**: [Line 118: finalPreview](../../../prosabuddy-rocq/packages/opencode/src/tool/coqc.ts#L118).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Final validation and AST audit entry point, [From line 118](../../../prosabuddy-rocq/packages/opencode/src/tool/coqc.ts#L118):

```ts
      const finalPreview = SessionProofWorkflow.previewFinalTheoremGate(ctx.sessionID, filepath, coqcSource)
      const finalAstAudit = finalPreview.final_theorem_gate.ok
        ? await CoqAstAudit.runForSession({
            sessionID: ctx.sessionID,
```

Validator identifier, [Line 172](../../../prosabuddy-rocq/packages/opencode/src/tool/coqc.ts#L172):

```ts
        validator: "coqc",
```

- **Current behavior**: The success branch calls the final theorem gate, `CoqAstAudit.runForSession`, `recordCompilerResult`, and `classifyCoqcSuccess`; the validator is labeled `coqc`.
- **Recommendation**: Consume Lean declaration/proof-dependency validation results and update the validator identifier and `Qed` wording; issue a final certificate only when the target has no unfinished proof and the audit passes.

**4. Corresponding Description File | Modify, Small**

- **Location**: [coqc.txt](../../../prosabuddy-rocq/packages/opencode/src/tool/coqc.txt#L1).

**Description text to update** (excerpt):

Files, parameters, and completion conditions, [From line 1](../../../prosabuddy-rocq/packages/opencode/src/tool/coqc.txt#L1):

```text
Compile a Coq source file using coqc. Returns success/fail status.

On success: returns "success" status plus `status_detail`:
- `final_theorem_success` means compilation succeeded, there is no unfinished proof/admit marker, and the current target theorem proof ends with `Qed.`.
- `compile_success_nonfinal` means compilation succeeded but the file is not yet a final theorem success, usually because admits/unfinished proofs remain or the target theorem is not closed with `Qed.`.
```

- **Current behavior**: Describes `.v`, `-Q`, `Qed.`, SSReflect restrictions, and Rocq AST acceptance.
- **Recommendation**: Update Lean file, project parameter, completion, and audit instructions together; retain the distinction between successful compilation and final proof completion.

Path checks, timeout/cancellation handling, transaction commits, and result aggregation can be retained.
