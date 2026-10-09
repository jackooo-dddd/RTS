# Revision: `session/system.ts` (loads the system prompts)

**File**: [`system.ts`](../../../prosabuddy-rocq/packages/opencode/src/session/system.ts) (36 lines). **Change size**: Modify, Small. **Follows**: R4.

| Line(s) | Current | Change |
|---|---|---|
| [#L3](../../../prosabuddy-rocq/packages/opencode/src/session/system.ts#L3) | `import PROMPT_COQPROVER from "./prompt/coqprover.txt"` | `import PROMPT_LEANPROVER from "./prompt/leanprover.txt"` (file renamed, see `coqprover.txt-revision.md`). |
| [#L14](../../../prosabuddy-rocq/packages/opencode/src/session/system.ts#L14), [#L18](../../../prosabuddy-rocq/packages/opencode/src/session/system.ts#L18) | `PROMPT_COQPROVER` | `PROMPT_LEANPROVER`. |
| [#L25](../../../prosabuddy-rocq/packages/opencode/src/session/system.ts#L25) | `` `You are CoqProver powered by ${model.api.id}.` `` | `` `You are LeanProver powered by ${model.api.id}.` `` |

Any function name that says "coq" in this file (if renamed during the port) must be renamed together with its callers
in `session/prompt.ts`; `test/session/system.test.ts` checks the identity line (see gap-revisions §7).
