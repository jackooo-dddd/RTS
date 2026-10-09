# Revision: `opencode_runner_config.py` and `opencode_runner_config.env`

**Files**: [`opencode_runner_config.py`](../../../prosabuddy-rocq/scripts/scripts_junyi/opencode_runner_config.py) (565 lines), [`opencode_runner_config.env`](../../../prosabuddy-rocq/scripts/scripts_junyi/opencode_runner_config.env) (37 lines).
**Change size**: Modify, Small. **Follows**: DECISIONS D5, R7.

| Location | Current | Change |
|---|---|---|
| [.py #L65-L79](../../../prosabuddy-rocq/scripts/scripts_junyi/opencode_runner_config.py#L65) defaults | `OPENCODE_FULL_PROSA`, `OPENCODE_MIN/FULL_PROSA_SOURCE_DIR=/home/junyi/prosabuddy/prosaworkspace`, `OPENCODE_CONFIG_DIR=/home/junyi/prosabuddy/.opencode`, direct probe on (`OPENCODE_OUR_DIRECT_PROSA_PROBE=1`, agent `whole-lemma`, 50 steps, 1800 s) | `OPENCODE_LEAN_PACKAGE_DIR` (no default home path; fail fast if unset); `OPENCODE_CONFIG_DIR` = the Lean app's `.opencode` (skills only, GAPS §8); direct probe **default off** (R7); add `OPENCODE_MAX_INFRA_RECOVERIES=20` (D5) and `OPENCODE_LEAN_GATE_TIMEOUT_SECONDS`. |
| [.py #L106-L130](../../../prosabuddy-rocq/scripts/scripts_junyi/opencode_runner_config.py#L106) `_run_identity` | identity hash includes the Prosa source dirs | include `OPENCODE_LEAN_PACKAGE_DIR` and the toolchain version. |
| nohup / lock / state management (rest of .py) | generic | keep unchanged. |
| .env | Rocq paths, retry and token limits | Lean paths; keep `OPENCODE_MAX_TOTAL_TOKENS`, `OPENCODE_MAX_RETRIES`; set a model `limit.context` in the provider config (KNOWN_PROBLEMS K10). |
