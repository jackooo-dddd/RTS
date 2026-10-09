# Lean 4 Migration Notes for `server.ts`

**Purpose**: Configure and launch LSP servers for different languages, including project discovery and initialization for Rocq.

**Backend (decided 2026-10-09):** Lean LSP is used for file-level diagnostics and read-only lookups (hover, definitions, references, symbols; no goal operation, DECISIONS D3); tactic execution and goal states the agent acts on come from Pantograph — see [`BACKEND_DECISION.md`](../../BACKEND_DECISION.md).

**1. Proof Language Server Configuration | Modify, Medium**

- **Location**: [Line 2071: RocqLsp](../../../prosabuddy-rocq/packages/opencode/src/lsp/server.ts#L2071).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Opening Rocq server configuration, [From line 2071](../../../prosabuddy-rocq/packages/opencode/src/lsp/server.ts#L2071):

```ts
  export const RocqLsp: Info = {
    id: "rocq-lsp",
    extensions: [".v"],
    root: NearestRoot(["_RocqProject", "_CoqProject", "Makefile.conf", "dune-project"]),
    async spawn(root, input) {
      // Try coq-lsp (works for both Coq 8.x and Rocq 9.x)
```

Coq initialization options, [From line 69](../../../prosabuddy-rocq/packages/opencode/src/lsp/server.ts#L69):

```ts
  const RocqDefaults = {
    check_only_on_request: false,
    goal_after_tactic: true,
    send_perf_data: false,
    pp_type: 0,
  } as const
```

- **Current behavior**: Registers `.v`, finds project roots using Coq markers, locates coq-lsp/rocq-lsp executables, and applies RocqDefaults.
- **Recommendation**: Register `.lean`, locate projects through Lake/lean-toolchain, and launch the Lean server in the project's toolchain environment; replace RocqDefaults rather than inheriting Coq initialization options. For dual-backend support, add Lean configuration instead of overwriting Rocq configuration.

Other language servers and the general launch framework can be retained.
