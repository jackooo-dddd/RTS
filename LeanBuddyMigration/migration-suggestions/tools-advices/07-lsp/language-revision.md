# Lean 4 Migration Notes for `language.ts`

**Purpose**: Maintain the mapping from file extensions to LSP language IDs.

**1. Lean language ID | Modify, Small**

- **Location**: [Line 109](../../../prosabuddy-rocq/packages/opencode/src/lsp/language.ts#L109).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq file language ID mapping, [Line 109](../../../prosabuddy-rocq/packages/opencode/src/lsp/language.ts#L109):

```ts
  ".v": "rocq",
```

- **Current behavior**: Maps `.v` to rocq and has no `.lean` mapping.
- **Recommendation**: Add `.lean` → `lean` for didOpen; retain `.v` only if Rocq support is still required.

Other language-extension mappings can be retained.
