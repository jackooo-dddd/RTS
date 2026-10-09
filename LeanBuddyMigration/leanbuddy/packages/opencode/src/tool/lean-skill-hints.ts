/**
 * Optional skill lookups suggested next to Lean diagnostics (edit/write/apply_patch results, `lean_check`).
 * The names are the skills under `.opencode/skill/`; the patterns are Lean 4 diagnostic texts, matched loosely
 * because messages vary between Lean versions.
 */
export type LeanSkillHint = {
  name: string
  reason: string
}

export function leanSkillHintsFor(message: string): LeanSkillHint[] {
  const text = message.toLowerCase()
  const hints: LeanSkillHint[] = []
  const seen = new Set<string>()
  const add = (name: string, reason: string) => {
    if (seen.has(name)) return
    seen.add(name)
    hints.push({ name, reason })
  }

  if (/unsolved goals|no goals|too many goals|expected .*·|case tag|focus|unexpected token '·'|invalid 'case'/.test(text)) {
    add(
      "goal-focus-discipline",
      "the active goals differ from what the next tactic expects (unsolved or extra goals, a `·`/`case` focusing mistake); inspect the goals before continuing",
    )
  }

  if (
    /countp|list\.count|finset\.card|finset\.sum|list\.sum|finset\.filter|list\.filter|\bmin\b|nat\.min|ite .* 1 0|if .* then 1 else 0/.test(text)
  ) {
    add(
      "lean-count-bridging",
      "the same quantity may appear as an indicator sum, a filtered count, a card and a min-bound; fix one representation before the arithmetic",
    )
  }

  if (
    /motive is not type correct|did not find instance of the pattern|rewrite failed|pattern is a metavariable|simp made no progress|linarith failed|omega could not prove/.test(
      text,
    )
  ) {
    add(
      "lean-rewrite-discipline",
      "the rewrite or arithmetic step does not match the exact current goal; choose the step from the goal's actual form, or state a connecting equality",
    )
  }

  if (
    /don't know how to synthesize|failed to synthesize|typeclass instance problem is stuck|function expected|unable to unify|invalid argument|argument .* has type|could not unify|metavariable/.test(
      text,
    )
  ) {
    add(
      "lean-goal-driven-apply",
      "applying the lemma may be blocked by an implicit argument, an instance, or a `variable` argument before any ordinary premise appears",
    )
  }

  if (/type mismatch|application type mismatch|unknown identifier|unknown constant|unexpected token|expected term|declaration uses 'sorry'/.test(text)) {
    add(
      "lean-proof-methodology",
      "a typing, naming, syntax or incomplete-proof error: inspect the goal and the exact types, then make one small checked change",
    )
  }

  if (hints.length === 0) {
    add("lean-proof-methodology", "general error recovery starts from the exact goal and one small checked step")
  }
  return hints
}

export function formatLeanSkillHints(message: string) {
  const hints = leanSkillHintsFor(message)
  return [
    "",
    "<lean_skill_hints>",
    "Lean error detected. These are optional targeted skill lookups, not a blocker before editing.",
    "Use at most one skill lookup only if it directly explains the current failing goal; then make the next proof-producing edit in the current block. If the next repair is already clear, skip skill lookup and edit now.",
    "Suggested optional skills:",
    ...hints.map((hint) => `- ${hint.name}: ${hint.reason}`),
    `Optional call order: ${hints.map((hint) => `skill({ name: "${hint.name}" })`).join(" -> ")}`,
    "</lean_skill_hints>",
  ].join("\n")
}
