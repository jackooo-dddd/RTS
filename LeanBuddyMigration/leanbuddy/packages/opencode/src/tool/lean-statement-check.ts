import { createHash } from "crypto"
import { LeanProject } from "./lean-project"
import { LeanRegion } from "./lean-region"
import { LeanTerm } from "./lean-term"
import { LeanProofSource } from "@/session/lean-proof-source"

/**
 * D10 (K6, K7): propositions are compared by elaboration, not by text. A check compiles a probe of the staged file
 * with `lake env lean`: the two propositions must be definitionally equal (`Iff.rfl`) in the context where they are
 * used — the theorem's own context (opens, variables, binders) for a root goal, the region's local proof context for
 * a region target. The compiler gives that exact context, and one compile covers every region of a file.
 */
export namespace LeanStatementCheck {
  export type Verdict = "equivalent" | "different" | "unchecked"
  export type Result = { verdict: Verdict; detail?: string }

  const cache = new Map<string, Result>()
  let generation = 0

  /** Changes whenever a new verdict is cached, so reviews computed before it can be recomputed. */
  export function cacheGeneration() {
    return generation
  }

  function key(parts: string[]) {
    return createHash("sha256").update(parts.join("\u0000")).digest("hex")
  }

  function store(k: string, result: Result) {
    if (result.verdict === "unchecked") return result
    if (cache.size > 1024) cache.clear()
    cache.set(k, result)
    generation += 1
    return result
  }

  /** Whitespace- and comment-insensitive text, used only to skip the compiler when two texts are identical. */
  export function sameText(a: string, b: string) {
    const norm = (text: string) =>
      LeanSource_blank(text).replace(/\s+/g, " ").replace(/\(\s+/g, "(").replace(/\s+\)/g, ")").trim()
    return norm(a) === norm(b)
  }

  function LeanSource_blank(text: string) {
    return text.replace(/\/-[\s\S]*?-\//g, " ").replace(/--[^\n]*/g, " ")
  }

  function lineOf(text: string, offset: number) {
    return text.slice(0, offset).split("\n").length
  }

  /** K6: is the submitted root goal the bound theorem's conclusion, in the theorem's own context? */
  export async function rootGoal(input: {
    file: string
    source: string
    theorem: string
    submitted: string
    signal?: AbortSignal
  }): Promise<Result> {
    const span = LeanProofSource.theoremSpans(input.source).find(
      (candidate) => LeanProofSource.shortName(candidate.name) === LeanProofSource.shortName(input.theorem),
    )
    if (!span || span.assign === undefined || !span.rootGoal) {
      return { verdict: "unchecked", detail: `theorem ${input.theorem} with a proof body was not found` }
    }
    if (sameText(input.submitted, span.rootGoal)) return { verdict: "equivalent" }
    const scan = LeanTerm.scan(input.submitted)
    if (!scan.ok) return { verdict: "different", detail: scan.reason }
    const declaration = input.source.slice(span.start, span.assign).replace(/\s+$/, "")
    const conclusionAt = declaration.lastIndexOf(span.rootGoal)
    if (conclusionAt < 0) return { verdict: "unchecked", detail: "could not isolate the theorem conclusion" }
    const k = key(["root", input.file, input.source.slice(0, span.assign), scan.text])
    const cached = cache.get(k)
    if (cached) return cached
    const root = LeanProject.findRoot(input.file)
    if (!root) return { verdict: "unchecked", detail: "no Lake project" }

    const prefix = input.source.slice(0, span.start).replace(/\s*$/, "\n\n")
    const head = declaration
      .slice(0, conclusionAt)
      .replace(/\b(theorem|lemma)\s+\S+/, "theorem __lb_root_goal_probe")
    const probe = `${prefix}${head}(${scan.text}) ↔ (${span.rootGoal}) := Iff.rfl\n`
    const firstProbeLine = lineOf(probe, prefix.length)
    try {
      const { result, diagnostics } = await LeanProject.checkSource(root, input.file, probe, { signal: input.signal })
      if (result.timedOut) return { verdict: "unchecked", detail: "the elaboration check timed out" }
      const errors = diagnostics.filter((d) => d.severity === "error" && d.line >= firstProbeLine)
      return store(
        k,
        errors.length === 0
          ? { verdict: "equivalent" }
          : { verdict: "different", detail: errors.map((d) => d.message).join("\n").slice(0, 1200) },
      )
    } catch (error) {
      if (input.signal?.aborted) throw error
      return { verdict: "unchecked", detail: error instanceof Error ? error.message : String(error) }
    }
  }

  function regionKey(file: string, admitID: string, target: string, normalForm: string) {
    const norm = (text: string) => text.replace(/\s+/g, " ").trim()
    return key(["region", file, admitID, norm(target), norm(normalForm)])
  }

  /** K7: a cached verdict for a region target versus its plan normal form (no compile). */
  export function cachedRegion(file: string, admitID: string, target: string, normalForm: string): Result | undefined {
    if (sameText(target, normalForm)) return { verdict: "equivalent" }
    return cache.get(regionKey(file, admitID, target, normalForm))
  }

  /**
   * K7: compare each region's exported target with its plan normal form inside the region's local proof context.
   * Region proofs are masked to `sorry`, and before each region a probe
   * `have __lb_nf_<i> : (target) ↔ (normal form) := by first | (exact Iff.rfl; trace EQ) | (trace NE; sorry)` is
   * inserted. The probe never fails on a mere difference (an error would stop the rest of the tactic block and drop
   * its messages); an error on the probe line means a statement does not elaborate. Probes not reached because an
   * earlier one failed are compiled again without it.
   */
  export async function regionTargets(input: {
    file: string
    source: string
    pairs: { admit_id: string; normal_form: string }[]
    signal?: AbortSignal
  }): Promise<Map<string, Result>> {
    const out = new Map<string, Result>()
    const parsed = LeanRegion.parse(input.source).regions
    const masked = LeanRegion.maskRegions(input.source, parsed)
    const regions = new Map(LeanRegion.parse(masked).regions.map((region) => [region.admit_id, region]))
    const probes: { index: number; admit_id: string; at: number; text: string; key: string }[] = []
    for (const [index, pair] of input.pairs.entries()) {
      const region = regions.get(pair.admit_id)
      if (!region?.target) {
        out.set(pair.admit_id, { verdict: "unchecked", detail: "region or exported target not found" })
        continue
      }
      const target = region.target.statement
      if (sameText(target, pair.normal_form)) {
        out.set(pair.admit_id, { verdict: "equivalent" })
        continue
      }
      const scan = LeanTerm.scan(pair.normal_form)
      if (!scan.ok) {
        out.set(pair.admit_id, { verdict: "different", detail: `normal_form: ${scan.reason}` })
        continue
      }
      const k = regionKey(input.file, pair.admit_id, target, pair.normal_form)
      const cached = cache.get(k)
      if (cached) {
        out.set(pair.admit_id, cached)
        continue
      }
      const lineStart = masked.lastIndexOf("\n", region.beginStart - 1) + 1
      const haveLineStart = masked.lastIndexOf("\n", region.target.haveStart - 1) + 1
      const indent = /^[ \t]*/.exec(masked.slice(haveLineStart))![0]
      if (masked.slice(lineStart, region.beginStart).trim()) {
        out.set(pair.admit_id, { verdict: "unchecked", detail: "the region begin marker does not start its line" })
        continue
      }
      probes.push({
        index,
        admit_id: pair.admit_id,
        at: lineStart,
        key: k,
        text: [
          `${indent}have __lb_nf_${index} : (${target}) ↔ (${scan.text}) := by`,
          `${indent}  first`,
          `${indent}  | (exact Iff.rfl; trace "LB_NF_EQ_${index}")`,
          `${indent}  | (trace "LB_NF_NE_${index}"; sorry)`,
          "",
        ].join("\n"),
      })
    }
    if (probes.length === 0) return out
    const root = LeanProject.findRoot(input.file)
    if (!root) {
      for (const probe of probes) out.set(probe.admit_id, { verdict: "unchecked", detail: "no Lake project" })
      return out
    }
    let pending = probes
    while (pending.length > 0) {
      let text = masked
      for (const probe of [...pending].sort((a, b) => b.at - a.at)) {
        text = text.slice(0, probe.at) + probe.text + text.slice(probe.at)
      }
      const probeLines = new Map<number, number>()
      text.split("\n").forEach((line, i) => {
        const m = /^\s*have __lb_nf_(\d+) :/.exec(line)
        if (m) probeLines.set(Number(m[1]), i + 1)
      })
      let diagnostics: LeanProject.Diagnostic[]
      let timedOut = false
      try {
        const checked = await LeanProject.checkSource(root, input.file, text, { signal: input.signal })
        diagnostics = checked.diagnostics
        timedOut = checked.result.timedOut
      } catch (error) {
        if (input.signal?.aborted) throw error
        for (const probe of pending) {
          out.set(probe.admit_id, { verdict: "unchecked", detail: error instanceof Error ? error.message : String(error) })
        }
        return out
      }
      const traced = (tag: string) => diagnostics.some((d) => d.severity === "info" && d.message.trim() === tag)
      const unreached: typeof pending = []
      let failed = false
      for (const probe of pending) {
        const errors = diagnostics.filter((d) => d.severity === "error" && d.line === probeLines.get(probe.index))
        if (errors.length > 0) {
          failed = true
          out.set(probe.admit_id, store(probe.key, {
            verdict: "different",
            detail: `does not elaborate: ${errors.map((d) => d.message).join("\n").slice(0, 1200)}`,
          }))
        } else if (traced(`LB_NF_EQ_${probe.index}`)) {
          out.set(probe.admit_id, store(probe.key, { verdict: "equivalent" }))
        } else if (traced(`LB_NF_NE_${probe.index}`)) {
          out.set(probe.admit_id, store(probe.key, { verdict: "different", detail: "not definitionally equal" }))
        } else if (failed && !timedOut) {
          unreached.push(probe)
        } else {
          out.set(probe.admit_id, {
            verdict: "unchecked",
            detail: timedOut ? "the elaboration check timed out" : "the probe was not reached",
          })
        }
      }
      pending = unreached
    }
    return out
  }
}
