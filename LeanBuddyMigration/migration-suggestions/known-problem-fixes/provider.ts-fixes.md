# Fixes: `provider/provider.ts` and the runner check (K10)

**File**: [`provider/provider.ts`](../../prosabuddy-rocq/packages/opencode/src/provider/provider.ts). **Implements**: D12 (K10).

- **Location**: custom model limit default [#L896-L897](../../prosabuddy-rocq/packages/opencode/src/provider/provider.ts#L896) (`context: model.limit?.context ?? existingModel?.limit?.context ?? 0`); compaction skipped when context is 0 ([session/compaction.ts#L52-L56](../../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L52)).
- **Change**: when a model used by a proof agent has no `limit.context`, fail at session start with a clear error instead of silently disabling compaction. The runner (gap-revisions §5) checks the provider config before staging. Document the required `limit` block in the runner README (e.g. `{"limit": {"context": 400000, "output": 32000}}` for gpt-6-luna).
