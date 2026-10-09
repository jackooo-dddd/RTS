# Revision: `test/tool/coq-project.test.ts`

**File**: [`test/tool/coq-project.test.ts`](../../../prosabuddy-rocq/packages/opencode/test/tool/coq-project.test.ts) (11 tests; 9 lines with Rocq content; 0 references to a live Rocq run).
**Tests**: project discovery: `_CoqProject` parsing, load paths, temp scripts. **Decision**: Port (rename).

**Change**: → `tool/lean-project.test.ts`: find `lakefile.lean`/`lean-toolchain`, resolve the module name of a file, run `lake env lean` on a temporary file inside the project.
