# Lean 4 Migration Notes for `session-proof.sql.ts`

**Purpose**: Define database tables for session proof bindings, positions, document versions, and original source.

**1. Persistence Fields | Retain, None**

- **Location**: [Line 9: SessionProofTable](../../../prosabuddy-rocq/packages/opencode/src/session/session-proof.sql.ts#L9).

**Source code to retain** (excerpt):

Proof-binding position fields, [From line 15](../../../prosabuddy-rocq/packages/opencode/src/session/session-proof.sql.ts#L15):

```ts
    file: text().notNull(),
    uri: text().notNull(),
    line: integer().notNull(),
    character: integer().notNull(),
    source: text().notNull().$type<"auto" | "tool" | "ide" | "parent" | "manual">(),
```

- **Current behavior**: Stores file/uri, position, origin, document version, and canonical_source without a `.v` restriction.
- **Recommendation**: Retain the structure; `.lean` baseline capture and event updates belong in session-proof.ts.

No database structure change is inherently required for Coq → Lean migration.
