# Revision: `tool/coq-ast-audit.ts` → `tool/lean-gate.ts`

**File**: [`tool/coq-ast-audit.ts`](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts) (namespace `CoqAstAudit`). **Change size**: Rewrite, Medium.
**Follows**: DECISIONS D4; KNOWN_PROBLEMS K1, K9.

**Keep the public shape** so the three callers change only by name: `Stage = "submission" | "final"`
([#L11](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L11)), `Result` (status `accepted`/`rejected`/`unavailable`/`disabled`, `reasons[]` with
`code`, `message`, `line`), `runForSession(...)` ([#L398](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L398)), `passed(...)`
([#L448](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L448)), `formatReasons(...)` ([#L452](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L452)),
`maxSubmissionRepairs()` ([#L98](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L98)). Namespace `CoqAstAudit` → `LeanGate`.

**Replace** `run(...)` ([#L259](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L259); fcc astdump, classifier, Python validator) and the
Rocq-only helpers (`trustedRequireKeys` [#L212](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L212), `DEFAULT_TRUSTED_REQUIRE_ROOTS`
[#L54](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L54), fcc/classifier/validator paths in `config()` [#L80-L96](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L80)) with:

| Stage | Checks (in order; first failure gives the reason code) |
|---|---|
| `final` | 1. `FROZEN_CHANGED`: frozen files differ from their sha256 (benchmark: `benchmark/frozen_sha256.json`; general case: the statement module and everything outside the solution file). 2. `FORBIDDEN_TOKEN`: token scan (DECISIONS D4 list) of the solution file and every non-frozen module it imports, comments stripped. 3. `BUILD_FAILED`: `lake build <solution module>`. 4. `STATEMENT_MISMATCH`: a fresh probe file `theorem gate_check : <statement> := <solution>` fails to elaborate. 5. `AXIOMS`: `#print axioms gate_check` lists anything beyond `propext`, `Classical.choice`, `Quot.sound`. |
| `submission` (a lemma region) | 1. `REGION_OUTSIDE_EDIT`: the candidate differs from the baseline outside the assigned `:= (by …)` region (except added `import`s of package modules in the header, K1). 2. `FORBIDDEN_TOKEN` inside the region (`sorry` allowed only where the assignment allows a split). 3. `REGION_DOES_NOT_ELABORATE`: `lean_check` of the staged file reports an error inside the region. |

- **Benchmark mode** (the target is a `Solution.lean` listed in `benchmark/tasks.json`): implement stage `final` by
  running `python3 benchmark/check.py <task-id> --json <tmp>` in the staged workspace and mapping its FAIL reason to
  the codes above. This makes the agent's final gate and the runner's success test literally the same code (K9).
- **General mode**: the same five checks implemented in TypeScript (statement = the declaration's type in the
  baseline file).
- Environment variables: `OPENCODE_COQ_AST_AUDIT*` → `OPENCODE_LEAN_GATE*` (`mode` off/auto/required,
  `timeoutMs` — raise the default: `lake build` of a case study takes tens of seconds even with a warm cache).
- Messages to the model say "final gate" / "region check", never "Rocq AST audit".
