# Revision: `scripts/scripts_junyi/test_run_casestudy_continuation_prompt.py`

**File**: [`scripts/scripts_junyi/test_run_casestudy_continuation_prompt.py`](../../../prosabuddy-rocq/scripts/scripts_junyi/test_run_casestudy_continuation_prompt.py). **Tests**: continuation prompt text. **Decision**: Port.

**Change**: Expected strings per gap-revisions §5 (`Solution.lean`, final gate, D4 token list); add D5 tests: a controller stop and an API error do not consume a retry; the infrastructure cap ends the run with `infrastructure_limit`.
