# Lean 4 Migration Notes for `coq-ast-audit.ts`

**Purpose**: Compare Rocq ASTs of baseline and candidate source and invoke validators to audit theorem declarations and permitted proof changes.

**Decided 2026-10-09 (DECISIONS D4):** replaced by a semantic gate (`tool/lean-gate.ts`); the recommendations below about Lean syntax/elaboration audits are superseded — see [`gap-revisions/04-audit-backend/`](../../gap-revisions/04-audit-backend/README.md).

**1. Rocq AST Generation and External Validators | Rewrite, Large**

- **Location**: [Line 259: run](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L259).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Rocq AST dump command, [From line 318](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L318):

```ts
        "baseline astdump",
        [fcc, "--no_vo", "--plugin=coq-lsp.plugin.astdump", ...flags, originalFile],
        resolved.cwd,
```

- **Current behavior**: Generates `.v` inputs, produces AST dumps with fcc and `coq-lsp.plugin.astdump`, then invokes classification/validation scripts.
- **Recommendation**: Audit baseline and candidate source using Lean syntax and elaboration information; replace the external protocol and Coq vernac classification, retaining the result structure for stage, reasons, and source hashes.

**2. Imports and Trusted Dependencies | Rewrite, Large**

- **Location**: [Line 212: trustedRequireKeys](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L212).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Trusted library roots, [Line 54](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L54):

```ts
  const DEFAULT_TRUSTED_REQUIRE_ROOTS = ["mathcomp", "prosa"]
```

Coq import AST type check, [From line 215](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L215):

```ts
      if (record.phase !== "VernacSynterp" || record.vernac_kind !== "VernacRequire") continue
      const require = record.require
      if (!require || typeof require !== "object" || Array.isArray(require)) continue
```

- **Current behavior**: Extracts modules from `VernacRequire` and filters by trusted roots; configuration includes mathcomp/prosa and Coq plugins.
- **Recommendation**: Inspect Lean imports and actual declaration dependencies. Distinguish existing dependencies from newly introduced axioms under the project's allowed foundational axioms, and check whether the target proof depends on sorry; a Mathlib/Prosa name allowlist is not proof of completion.

**3. Preserving Theorem Declarations and Session Integration | Modify, Large**

- **Location**: [Line 398: runForSession](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L398).

**Related source code** (retain the call or general mechanism and adapt its dependencies):

Audit baseline and target binding, [From line 419](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L419):

```ts
    const transaction = ProofEditTransaction.auditContext(input.sessionID, input.file)
    const binding = SessionProof.get(input.sessionID)
    const bindingMatches = binding && path.normalize(binding.file) === path.normalize(input.file)
    const baselineSource = transaction?.baselineSource ?? (bindingMatches ? binding.canonicalSource : undefined)
    const theorem = input.theorem ?? transaction?.theorem
```

- **Current behavior**: Reads original source stored by the transaction/session as the audit baseline and passes it to run.
- **Recommendation**: Keep the baseline protected from replacement by changes under review; the Lean audit must check declaration types, binders, implicit/instance parameters, local-context changes, and proof dependencies. Retain existing mode configuration, but require the new backend to determine Lean audit success.

Baseline/candidate comparison, transaction binding, audit results, and staged acceptance must not be removed merely because the proof language changes.
