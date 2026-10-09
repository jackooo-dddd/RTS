# Known-problem fixes — revision set

Per-file changes that implement DECISIONS D8–D12 (fix KNOWN_PROBLEMS K2–K8, K10, K11 in the Lean version). They
come **on top of** the translation notes (`tools-advices/`, `gap-revisions/`): translate a file first, then apply its
fixes here. Code links: pure upstream baseline 8e1de8c.

| File | Fixes | Revision |
|---|---|---|
| `session/proof-workflow.ts` | K2, K4, K5, K7, K8, S26 | [proof-workflow.ts-fixes.md](proof-workflow.ts-fixes.md) |
| `tool/proof-plan.ts` | K2 (amendment action), K6, K7 (prose `normal_form`) | [proof-plan.ts-fixes.md](proof-plan.ts-fixes.md) |
| `tool/proof-schema.ts` | K2 limits and amendment schema | [proof-schema.ts-fixes.md](proof-schema.ts-fixes.md) |
| `lean_session` (new tool, Pantograph) | K6, K7: statement-equivalence service | [lean_session-equivalence.md](lean_session-equivalence.md) |
| `session/prompt.ts` | K3, K4, S14 | [prompt.ts-fixes.md](prompt.ts-fixes.md) |
| `session/proof-projection.ts` | K4 (rule 19), LSP wording | [proof-projection.ts-fixes.md](proof-projection.ts-fixes.md) |
| `agent/prompt/prover.txt` | K2 (how to amend) | [prover.txt-fixes.md](prover.txt-fixes.md) |
| `agent/prompt/lemma.txt` | LSP wording, K8 | [lemma.txt-fixes.md](lemma.txt-fixes.md) |
| `agent/prompt/whole-lemma.txt` | LSP wording | [whole-lemma.txt-fixes.md](whole-lemma.txt-fixes.md) |
| `session/proof-context.ts` | S25 stale diagnostics | [proof-context.ts-fixes.md](proof-context.ts-fixes.md) |
| `provider/provider.ts` | K10 | [provider.ts-fixes.md](provider.ts-fixes.md) |

K1 (imports) and K9 (one success definition) are settled by the Lean benchmark rules and D4
(`gap-revisions/04-audit-backend/`); K3's runner part and S32 by D5 (`gap-revisions/05-benchmark-runner/`).

Tests to add with these fixes (in addition to `gap-revisions/07-tests/`): an amendment adds a bridge node and its
region (K2); a rejected amendment leaves the count unchanged (K2); a child session and a fresh session see the
accepted plan (K5); `no_ready_region` is returned when every region is escalated (K4); the 4th same-type escalation
of a region is not dispatched (K8); a formatting-only root-goal or `normal_form` difference is accepted without
spending a revision (K6); a region with `sorry` is never reported solved (S26).
