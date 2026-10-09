# Lean 4 Migration Notes for `lsp.ts`

**Purpose**: Provide general LSP queries such as definitions and references, plus proof-goal queries at the current position.

**Backend (decided 2026-10-09):** Lean LSP is used for file-level diagnostics and read-only lookups (hover, definitions, references, symbols; no goal operation, DECISIONS D3); tactic execution and goal states the agent acts on come from Pantograph — see [`BACKEND_DECISION.md`](../../BACKEND_DECISION.md).

**Decided 2026-10-09 (DECISIONS D3):** agents may call `lsp` for hover, go-to-definition, references, document and workspace symbols only; remove `proofGoals` from the Lean tool.


**1. proofGoals Interface | Modify, Large**

- **Location**: [Line 87](../../../prosabuddy-rocq/packages/opencode/src/tool/lsp.ts#L87).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Rocq goal query, [From line 87](../../../prosabuddy-rocq/packages/opencode/src/tool/lsp.ts#L87):

```ts
        case "proofGoals":
          ProofContext.setBinding(ctx.sessionID, file, { line: position.line, character: position.character })
          SessionProof.set(ctx.sessionID, file, { line: position.line, character: position.character }, "tool")
          return [await LSP.rocqGoals(position)]
```

- **Current behavior**: Calls `LSP.rocqGoals` after binding the proof position and returns goals using Rocq error/message formats.
- **Recommendation**: Connect Lean goal queries and update `rocqProofGoalErrorText` and Coq hints together; retain position binding and ProofContext refresh.

**2. Corresponding Description File | Modify, Small**

- **Location**: [lsp.txt](../../../prosabuddy-rocq/packages/opencode/src/tool/lsp.txt#L13).

**Description text to update** (excerpt):

proofGoals description, [Line 13](../../../prosabuddy-rocq/packages/opencode/src/tool/lsp.txt#L13):

```text
- proofGoals: Get current Rocq/Coq proof goals, hypotheses, and messages at a position
```

Rocq server requirement, [Line 22](../../../prosabuddy-rocq/packages/opencode/src/tool/lsp.txt#L22):

```text
For `proofGoals`, the file must be handled by `rocq-lsp`/`coq-lsp`.
```

- **Current behavior**: Describes proofGoals as a Rocq proof-state query.
- **Recommendation**: Describe the implemented Lean goal query and update server requirements and example extensions.

General LSP operations such as definition, references, and hover can be retained.
