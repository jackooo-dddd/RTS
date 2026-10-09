# Revision: `scripts/scripts_junyi/test_opencode_runner_config.py`

**File**: [`scripts/scripts_junyi/test_opencode_runner_config.py`](../../../prosabuddy-rocq/scripts/scripts_junyi/test_opencode_runner_config.py). **Tests**: runner config defaults and nohup/lock handling. **Decision**: Port.

**Change**: Expect the Lean defaults (gap-revisions §5 opencode_runner_config): `OPENCODE_LEAN_PACKAGE_DIR` required, direct probe off, `OPENCODE_MAX_INFRA_RECOVERIES`.
