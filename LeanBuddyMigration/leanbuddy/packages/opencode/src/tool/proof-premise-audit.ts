import { createHash } from "crypto"
import type z from "zod"
import { ProofRouteLedger } from "@/session/proof-route-ledger"
import { LeanProject } from "./lean-project"
import { LeanProofSource } from "@/session/lean-proof-source"
import { CandidateLemmaAudit, ProofPlanCandidateLemma, ProofPlanStep } from "./proof-schema"

type PlanStep = z.infer<typeof ProofPlanStep>
type Candidate = z.infer<typeof ProofPlanCandidateLemma>

async function mapLimit<T, R>(items: T[], limit: number, fn: (item: T, index: number) => Promise<R>) {
  const results = new Array<R>(items.length)
  let cursor = 0
  const workers = Array.from({ length: Math.min(Math.max(1, limit), items.length) }, async () => {
    while (true) {
      const index = cursor++
      if (index >= items.length) return
      results[index] = await fn(items[index]!, index)
    }
  })
  await Promise.all(workers)
  return results
}

function hash(value: string) {
  return createHash("sha256").update(value).digest("hex")
}

function normalize(value: string) {
  return value.replace(/\s+/g, " ").trim()
}

/**
 * The probe context for a theorem (tools-advices proof-premise-audit-revision.md §1): the file text before the
 * theorem (imports, namespaces, `open`s, `variable`s, helper declarations), and the theorem's signature for a renamed
 * copy in which the candidate is applied.
 */
function theoremProbeContext(source: string, theorem: string) {
  const span = LeanProofSource.theoremSpans(source).find(
    (candidate) => LeanProofSource.shortName(candidate.name) === LeanProofSource.shortName(theorem),
  )
  if (!span || span.assign === undefined) return undefined
  const declaration = source.slice(span.start, span.assign).trim()
  const renamed = declaration.replace(/\b(theorem|lemma)\s+\S+/, "theorem __opencode_premise_audit")
  return { prefix: source.slice(0, span.start), declaration: renamed }
}

/** Residual goal targets from a `trace_state` message (goals separated by blank lines, target after `⊢`). */
function residualGoals(state: string) {
  if (/^\s*no goals\s*$/i.test(state)) return []
  return state
    .split(/\n\s*\n/)
    .map((goal) => {
      const turnstile = goal.lastIndexOf("⊢")
      return normalize(turnstile >= 0 ? goal.slice(turnstile + 1) : goal)
    })
    .filter(Boolean)
}

export async function auditCandidateLemma(input: {
  file: string
  source: string
  theorem: string
  formalGoal: string
  candidate: Candidate
  signal?: AbortSignal
}): Promise<z.infer<typeof CandidateLemmaAudit>> {
  const auditedAt = Date.now()
  const targetFingerprint = ProofRouteLedger.targetContractFingerprint(input.formalGoal)
  const context = theoremProbeContext(input.source, input.theorem)
  const root = LeanProject.findRoot(input.file)
  if (!context || !root) {
    return CandidateLemmaAudit.parse({
      lemma: input.candidate.name,
      target_contract_fingerprint: targetFingerprint,
      conclusion_compatible: false,
      verdict: "audit_error",
      diagnostic: !root
        ? `No Lake project contains ${input.file}; the premise audit needs the project environment.`
        : `Could not isolate theorem ${input.theorem} for a premise audit.`,
      audited_at: auditedAt,
    })
  }

  const marker = `OPENCODE_PREMISE_AUDIT_${hash(`${input.candidate.name}\n${input.formalGoal}`).slice(0, 12)}`
  const role = input.candidate.role ?? "direct_apply"
  const directApplication = role === "direct_apply"
  const name = input.candidate.name.trim()
  const head = `${context.prefix.replace(/\s*$/, "\n\n")}#check @${name}\n`
  const checkLine = head.split("\n").length - 1
  const probe = [
    head,
    directApplication ? `${context.declaration} := by` : undefined,
    // A plan node may quantify its own variables after the theorem context is introduced; open both before
    // applying the candidate, so its conclusion is unified with the node conclusion, not with a binder's type.
    directApplication ? "  intros" : undefined,
    directApplication ? `  have __opencode_candidate_goal : (${input.formalGoal}) := by` : undefined,
    directApplication ? "    intros" : undefined,
    directApplication ? `    apply ${name}` : undefined,
    directApplication ? "    all_goals (try assumption)" : undefined,
    directApplication ? "    all_goals (try rfl)" : undefined,
    directApplication ? `    trace "${marker}_RESIDUAL"` : undefined,
    directApplication ? "    trace_state" : undefined,
    directApplication ? `    trace "${marker}_DONE"` : undefined,
    directApplication ? "    all_goals sorry" : undefined,
    directApplication ? "  sorry" : undefined,
    "",
  ]
    .filter((line): line is string => line !== undefined)
    .join("\n")

  try {
    const { result, diagnostics } = await LeanProject.checkSource(root, input.file, probe, { signal: input.signal })
    const combined = diagnostics.map((d) => `${d.line}: ${d.severity}: ${d.message}`).join("\n")
    const compilerOutputHash = hash(combined)
    const checkMessage = diagnostics.find((d) => d.line === checkLine)
    // the full `#check` line (`name : type`), like the Rocq `Check` output it replaces
    const typeText = checkMessage && checkMessage.severity !== "error" ? normalize(checkMessage.message) : ""
    const errors = diagnostics.filter((d) => d.severity === "error")
    if (result.timedOut || !typeText || errors.length > 0) {
      return CandidateLemmaAudit.parse({
        lemma: input.candidate.name,
        exact_type: typeText || undefined,
        lemma_type_fingerprint: typeText ? hash(typeText) : undefined,
        target_contract_fingerprint: targetFingerprint,
        conclusion_compatible: false,
        verdict: result.timedOut ? "audit_error" : "interface_mismatch",
        diagnostic:
          (errors.map((d) => `line ${d.line}: ${d.message}`).join("\n").slice(-4000) || (result.timedOut ? "premise audit timed out" : "")) ||
          `Lean rejected ${input.candidate.name} for the candidate target.`,
        compiler_output_hash: compilerOutputHash,
        audited_at: auditedAt,
      })
    }

    if (!directApplication) {
      return CandidateLemmaAudit.parse({
        lemma: input.candidate.name,
        exact_type: typeText,
        lemma_type_fingerprint: hash(typeText),
        target_contract_fingerprint: targetFingerprint,
        instantiation_fingerprint: hash([role, typeText, normalize(input.formalGoal)].join("\n")),
        conclusion_compatible: false,
        residual_premises: [],
        residual_premise_fingerprints: [],
        verdict: "available",
        diagnostic:
          `Lean resolved ${input.candidate.name} with role ${role}. ` +
          "This role is type-checked for availability but is not required to close the complete plan-node target; its concrete rewrite, transport, local-fact, or automation use will be checked during proof materialization.",
        compiler_output_hash: compilerOutputHash,
        audited_at: auditedAt,
      })
    }

    const traces = diagnostics.filter((d) => d.severity === "info").map((d) => d.message.trim())
    const residualAt = traces.findIndex((message) => message === `${marker}_RESIDUAL`)
    const doneAt = traces.findIndex((message) => message === `${marker}_DONE`)
    if (residualAt < 0 || doneAt < 0) {
      return CandidateLemmaAudit.parse({
        lemma: input.candidate.name,
        exact_type: typeText,
        lemma_type_fingerprint: hash(typeText),
        target_contract_fingerprint: targetFingerprint,
        conclusion_compatible: false,
        verdict: "audit_error",
        diagnostic: "the premise-audit probe did not report its goal state",
        compiler_output_hash: compilerOutputHash,
        audited_at: auditedAt,
      })
    }
    const premises = traces.slice(residualAt + 1, doneAt).flatMap(residualGoals)
    const premiseFingerprints = premises.map(ProofRouteLedger.premiseFingerprint)
    return CandidateLemmaAudit.parse({
      lemma: input.candidate.name,
      exact_type: typeText,
      lemma_type_fingerprint: hash(typeText),
      target_contract_fingerprint: targetFingerprint,
      instantiation_fingerprint: hash([typeText, normalize(input.formalGoal), ...premiseFingerprints].join("\n")),
      conclusion_compatible: true,
      residual_premises: premises,
      residual_premise_fingerprints: premiseFingerprints,
      verdict: premises.length === 0 ? "usable" : "bridge_required",
      diagnostic:
        premises.length === 0
          ? "Lean applied the candidate and discharged every residual premise with the live local context."
          : `Lean's \`apply\` left ${premises.length} residual premise(s); each must be mapped to a dependency or current compiler certificate before materialization.`,
      compiler_output_hash: compilerOutputHash,
      audited_at: auditedAt,
    })
  } catch (error) {
    if (input.signal?.aborted) throw error
    return CandidateLemmaAudit.parse({
      lemma: input.candidate.name,
      target_contract_fingerprint: targetFingerprint,
      conclusion_compatible: false,
      verdict: "audit_error",
      diagnostic: error instanceof Error ? error.message : String(error),
      audited_at: auditedAt,
    })
  }
}

export async function auditPlanLibraryCandidates(input: {
  file: string
  source: string
  theorem: string
  nodes: PlanStep[]
  signal?: AbortSignal
}) {
  // Each audit starts a Lean subprocess. Bound concurrency per proof_plan
  // so two experiment workers cannot multiply a large candidate list into an
  // unbounded burst and create resource-driven false timeouts.
  return mapLimit(input.nodes, 1, async (node) => {
    const candidates = [
      ...(node.prosa_candidate_lemmas ?? []).map((candidate) => ({ kind: "prosa" as const, candidate })),
      ...(node.mathlib_candidate_lemmas ?? []).map((candidate) => ({ kind: "mathlib" as const, candidate })),
    ]
    const audited = await mapLimit(candidates, 2, async ({ kind, candidate }) => ({
      kind,
      ...candidate,
      audit: await auditCandidateLemma({
        file: input.file,
        source: input.source,
        theorem: input.theorem,
        formalGoal: node.formal_goal,
        candidate,
        signal: input.signal,
      }),
    }))
    return {
      ...node,
      prosa_candidate_lemmas: audited
        .filter((entry) => entry.kind === "prosa")
        .map(({ kind: _, ...candidate }) => candidate),
      mathlib_candidate_lemmas: audited
        .filter((entry) => entry.kind === "mathlib")
        .map(({ kind: _, ...candidate }) => candidate),
    }
  })
}
