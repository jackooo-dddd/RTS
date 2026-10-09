# Revision: `tool/checkpoint.ts` — final-gate call only

**File**: [`tool/checkpoint.ts`](../../../prosabuddy-rocq/packages/opencode/src/tool/checkpoint.ts). Only the audit part; the rest of the file is covered by
`tools-advices/01-core-tools/checkpoint-revision.md`. **Change size**: Modify, Small. **Follows**: DECISIONS D2, D4.

- **Location**: import of `CoqAstAudit` and the success branch that runs the final audit ([#L128](../../../prosabuddy-rocq/packages/opencode/src/tool/checkpoint.ts#L128)).
- **Current behavior**: after a successful compile, if `previewFinalTheoremGate` says the theorem looks complete, run
  `CoqAstAudit.runForSession({ stage: "final" })`; on rejection return `status: ast_audit_rejected` with
  "compile/kernel checks passed, but the mandatory structural AST audit failed".
- **Change**: `CoqAstAudit` → `LeanGate` (`../04-audit-backend/coq-ast-audit.ts-revision.md`); status
  `final_gate_rejected`, message "the file checks, but the final gate failed: <reason code>"; drop `extraFlags`
  (Rocq load-path flags; Lake supplies paths). In the Lean version this tool is `checkpoint`.
  The "theorem looks complete" preview must use Lean's notion (no `sorry` left in the target), not `Qed`.
