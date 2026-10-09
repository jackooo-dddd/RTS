# Lean 4 Migration Notes for `checkpoint.ts`

**Purpose**: Run compilation checks at proof milestones and assess local progress, validation certificates, and completion of the target theorem.

**Verification (decided 2026-10-09):** per-step checks use Lean LSP diagnostics or `lake env lean` on the staged file; final verification is `lake build` of the module plus the integrity audit — see [`BACKEND_DECISION.md`](../../BACKEND_DECISION.md).

**1. Compilation and Staged Validation Entry Points | Modify, Medium**

- **Location**: [Line 48: CheckpointTool](../../../prosabuddy-rocq/packages/opencode/src/tool/checkpoint.ts#L48).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

File type restriction, [Line 60](../../../prosabuddy-rocq/packages/opencode/src/tool/checkpoint.ts#L60):

```ts
    if (!filepath.endsWith(".v")) throw new Error("File must be a .v (Coq source) file")
```

Coq compilation command, [Line 96](../../../prosabuddy-rocq/packages/opencode/src/tool/checkpoint.ts#L96):

```ts
      const args = [...CoqProject.coqcCmd(), ...resolved.flags, ...extraFlags, filepath]
```

- **Current behavior**: Parameters and checks require `.v`; ordinary source uses coqc, while transaction source uses `Validation.prefix`.
- **Recommendation**: Connect Lean files to the project compilation backend and validate the current staged revision; remove Coq flags and SSReflect style-check calls.

**2. Diagnostic and Warning Summaries | Rewrite, Medium**

- **Location**: [Line 308: diagnostics](../../../prosabuddy-rocq/packages/opencode/src/tool/checkpoint.ts#L308).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Diagnostic parsing, [From line 308](../../../prosabuddy-rocq/packages/opencode/src/tool/checkpoint.ts#L308):

```ts
    const diagnostics = parseCoqCompilerOutput(stdout, stderr)
    const lines = stderr.split("\n")
    const firstFile = stagedValidation ? filepath : (diagnostics.firstError?.file ?? null)
    const firstLine = stagedValidation?.first_error_line ?? diagnostics.firstError?.line ?? null
    const firstMsg = stagedValidation?.message ?? diagnostics.firstError?.message ?? null
```

Coq Warning text extraction, [From line 227](../../../prosabuddy-rocq/packages/opencode/src/tool/checkpoint.ts#L227):

```ts
      const warns = stderr.split("\n").filter((l: string) => l.includes("Warning")).map((l: string) => l.trim())
      const grouped: Record<string, number> = {}
      for (const w of warns) {
        const cat = w.match(/Warning:\s*(\S+)/)?.[1] ?? "other"
```

- **Current behavior**: The failure branch parses Coq file locations and counts warnings from `Warning:` text.
- **Recommendation**: Use positions, severity, and messages from Lean diagnostics; retain output fields such as first error and same-as-previous.

**3. Local Progress and Final Acceptance | Modify, Large**

- **Location**: [Line 130: finalPreview](../../../prosabuddy-rocq/packages/opencode/src/tool/checkpoint.ts#L130).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Final gate and AST audit, [From line 130](../../../prosabuddy-rocq/packages/opencode/src/tool/checkpoint.ts#L130):

```ts
      const finalPreview = SessionProofWorkflow.previewFinalTheoremGate(ctx.sessionID, filepath, compiledSource)
      const finalAstAudit = finalPreview.final_theorem_gate.ok
        ? await CoqAstAudit.runForSession({
            sessionID: ctx.sessionID,
```

- **Current behavior**: Calls the Coq final gate, AST audit, and local prefix certification; instructions refer to final `Qed` and preserving region braces.
- **Recommendation**: Connect Lean region and proof-dependency validation; retain the distinction between local progress and completion of the whole theorem, and remove Qed and Coq brace instructions.

**4. Corresponding Description File | Modify, Small**

- **Location**: [checkpoint.txt](../../../prosabuddy-rocq/packages/opencode/src/tool/checkpoint.txt#L1).

**Description text to update** (excerpt):

Checkpoint completion semantics, [Line 12](../../../prosabuddy-rocq/packages/opencode/src/tool/checkpoint.txt#L12):

```text
- `progress_level: hard` is genuine accepted proof progress: a proof-region compiler certificate, reduced unresolved semantic debt, a certified missing premise, or final `Qed.` success. It may update the committable transaction snapshot and reset repair/livelock counters.
```

- **Current behavior**: Specifies Coq checkpoints, `.v`, coqc flags, final Qed, and Rocq AST checks.
- **Recommendation**: Describe Lean checkpoint parameters and completion criteria while retaining the three progress categories and existing milestone invocation semantics.

The reason enum, error deduplication, hard/structural/debug progress categories, and transaction flow can be retained.
