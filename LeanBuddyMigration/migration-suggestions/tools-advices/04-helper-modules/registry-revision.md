# Lean 4 Migration Notes for `registry.ts`

**Purpose**: Register built-in tools and discover and load custom tools in the project.

**Decided 2026-10-09 (DECISIONS D2):** register `lean_session`, `lean_query`, `lean_check`; no tool may keep a Rocq name.

**1. Built-In Proof Tool Registration | Modify, Small**

- **Location**: [Line 25](../../../prosabuddy-rocq/packages/opencode/src/tool/registry.ts#L25).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Built-in proof tool imports, [From line 25](../../../prosabuddy-rocq/packages/opencode/src/tool/registry.ts#L25):

```ts
import { CoqcTool } from "./coqc"
import { CoqtopTool } from "./coqtop"
import { ProofPlanTool } from "./proof-plan"
import { CoqSessionTool } from "./coq-session"
import { CheckpointTool } from "./checkpoint"
import { PetanqueTool } from "./petanque"
```

- **Current behavior**: Explicitly imports and registers tools such as coqc/coqtop/coq-session/petanque.
- **Recommendation**: Replace these with exports and IDs of the Lean tools retained after migration; checkpoint/proof_plan may keep their general names.

**2. Discovery of Legacy Custom Tools | Modify, Small**

- **Location**: [Line 99](../../../prosabuddy-rocq/packages/opencode/src/tool/registry.ts#L99).

**Related source code** (retain the call or general mechanism and adapt its dependencies):

Scanning logic that will still discover old Coq custom tools, [From line 107](../../../prosabuddy-rocq/packages/opencode/src/tool/registry.ts#L107):

```ts
      for (const dirname of ["tool", "tools"]) {
        const dir = path.join(root, dirname)
        const entries = await fs.readdir(dir, { withFileTypes: true }).catch(() => [])
        for (const entry of entries) {
          if (!entry.isFile()) continue
          if (!entry.name.endsWith(".ts") && !entry.name.endsWith(".js")) continue
```

- **Current behavior**: Automatically scans TS/JS files in custom tool/tools directories.
- **Recommendation**: If consolidating coq-check (coq-serapi was removed as unused, GAPS.md §8), remove its discoverable entry point too; changing built-in registration alone will not stop old custom tools from loading. Retain the scanning mechanism itself.

The registry, tool discovery, and plugin-loading mechanisms can be retained.
