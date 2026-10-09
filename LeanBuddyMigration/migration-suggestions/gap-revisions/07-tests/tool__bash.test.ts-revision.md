# Revision: `test/tool/bash.test.ts`

**File**: [`test/tool/bash.test.ts`](../../../prosabuddy-rocq/packages/opencode/test/tool/bash.test.ts) (22 tests; 23 lines with Rocq content; 5 references to a live Rocq run).
**Tests**: bash tool permissions and direct-compiler guidance. **Decision**: Port.

**Change**: Replace the `coqc`/`coqtop`-via-bash cases with `lake env lean <file>` / `lake build <module>` (allowed per the runner config, gap-revisions §5 item 4); keep the permission and truncation tests.
