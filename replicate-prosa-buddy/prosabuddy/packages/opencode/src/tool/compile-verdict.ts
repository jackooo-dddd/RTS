// [replicate-prosa-buddy patch 1] Last compiler verdict per session, so the prover's
// transaction-recovery reminder can tell whether the current staged revision was already
// compiled. Without this, the reminder kept asking for a checkpoint that could not change
// anything (e.g. a decomposition-drift blocker), and the model re-ran it indefinitely.
import { createHash } from "crypto"

export type CompileVerdict = {
  tool: "checkpoint" | "coqc"
  sourceHash: string
  status: string
  detail?: string
  repeats: number
}

const verdicts = new Map<string, CompileVerdict>()

export function hashSource(source: string) {
  return createHash("sha256").update(source).digest("hex")
}

export function recordCompileVerdict(
  sessionID: string,
  input: { tool: CompileVerdict["tool"]; source: string; status: string; detail?: string },
) {
  const sourceHash = hashSource(input.source)
  const previous = verdicts.get(sessionID)
  verdicts.set(sessionID, {
    tool: input.tool,
    sourceHash,
    status: input.status,
    detail: input.detail,
    repeats: previous?.sourceHash === sourceHash ? previous.repeats + 1 : 1,
  })
}

export function lastCompileVerdict(sessionID: string) {
  return verdicts.get(sessionID)
}
