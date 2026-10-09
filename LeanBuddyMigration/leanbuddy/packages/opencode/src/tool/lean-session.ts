import z from "zod"
import path from "path"
import { createHash, randomBytes } from "crypto"
import { Tool } from "./tool"
import DESCRIPTION from "./lean-session.txt"
import { Instance } from "../project/instance"
import type { EnvFeedback, SessionSummary } from "./proof-schema"
import { ContextNormalizationAuditSchema, type ContextNormalizationAudit } from "@/session/lemma-assignment"
import { SessionProofWorkflow } from "@/session/proof-workflow"
import { ProofEditTransaction } from "@/session/proof-edit-transaction"
import { LeanProject } from "./lean-project"
import { LeanSource } from "./lean-source"
import { LeanRegion } from "./lean-region"
import { LeanTerm } from "./lean-term"
import { Pantograph } from "./pantograph"

/**
 * `lean_session`: interactive Lean proof states through Pantograph (DECISIONS D1, D2; BACKEND_DECISION.md).
 *
 * Goal states always come from the staged source (rule 2): the file body without its import header (the REPL is
 * started with those imports), every delegated region's proof masked to `(by sorry)` so that one broken region cannot
 * hide the others, and the text cut after the target declaration. `frontend.distil` then returns the declaration's
 * goals; a region's goal is found among them (they come in reverse source order) and confirmed with
 * `show <region statement>`. A session holds Pantograph state handles; they belong to one source hash and one REPL
 * generation (rule 3): when either changes, the session re-opens from the source and replays its successful tactics.
 * The source file stays the authority (rule 1): a "no goals" here is not a certificate.
 */

function fingerprint(text: string) {
  return createHash("sha256").update(text).digest("hex")
}

function compactText(text: string, limit = 240) {
  const normalized = text.replace(/\s+/g, " ").trim()
  return normalized.length <= limit ? normalized : normalized.slice(0, limit - 3) + "..."
}

type TacticRecord = { tactic: string; result: "success" | "failure"; feedback: EnvFeedback; time: string }

type Snapshot = {
  id: string
  stateId: number
  generation: number
  goals: Pantograph.Goal[]
  tactic_index: number
  summary?: SessionSummary
}

export type LeanSessionState = {
  session_id: string
  file: string
  theorem: string
  scope: "theorem" | "assigned_region"
  admit_id?: string
  /** Region statement (the exported `have` type), for region scope. */
  region_statement?: string
  expected_goal?: string
  root: string
  modules: string[]
  source_hash: string
  generation: number
  /** Goal names of the declaration that this session does not own (other regions, the trailing goal). */
  foreign: string[]
  stateId: number
  goals: Pantograph.Goal[]
  tactic_history: TacticRecord[]
  snapshots: Record<string, Snapshot>
  last_error: string | null
  desync_count: number
  summary?: SessionSummary
  /** Pretty-printed entry goal and its fingerprint (for workflow consumers). */
  entry_goal: string
  entry_fingerprint: string
}

const sessions = new Map<string, LeanSessionState>()
const contextAudits = new Map<string, Map<string, ContextNormalizationAudit>>()
const MAX_CONTEXT_AUDITS_PER_SESSION = 16
const MAX_CONTEXT_AUDIT_SESSIONS = 256

function recordContextAudit(sessionID: string, audit: ContextNormalizationAudit) {
  const parsed = ContextNormalizationAuditSchema.parse({ ...audit, verified: true })
  const existing = contextAudits.get(sessionID) ?? new Map<string, ContextNormalizationAudit>()
  existing.set(parsed.audit_id, parsed)
  while (existing.size > MAX_CONTEXT_AUDITS_PER_SESSION) {
    const first = existing.keys().next().value
    if (!first) break
    existing.delete(first)
  }
  contextAudits.set(sessionID, existing)
  while (contextAudits.size > MAX_CONTEXT_AUDIT_SESSIONS) {
    const first = contextAudits.keys().next().value
    if (!first) break
    contextAudits.delete(first)
  }
  return parsed
}

export function findContextNormalizationAudit(sessionID: string, auditID: string) {
  return contextAudits.get(sessionID)?.get(auditID)
}

/** The live proof state of a session (consumed by the task tool for lemma handoffs). */
export function currentProofState(sessionID: string) {
  const session = sessions.get(sessionID)
  if (!session) return undefined
  return {
    goal: renderGoals(session.goals),
    hypotheses: session.goals[0]?.vars.map(renderVar) ?? [],
    goal_fingerprint: fingerprint(renderGoals(session.goals)),
    expected_goal_fingerprint: session.expected_goal ? fingerprint(session.expected_goal) : undefined,
    source_hash: session.source_hash,
    certified_prefix_fingerprint: session.source_hash,
    admit_id: session.admit_id,
    last_error: session.last_error,
  }
}

function renderVar(v: Pantograph.Variable) {
  const name = v.isInaccessible && !v.userName.endsWith("✝") ? `${v.userName}✝` : v.userName
  // A masked region's `have` shows up with a metavariable value (`:= ?m.2`); that is not information for the agent.
  const value = v.value?.pp && !/^\?m\.\d+$/.test(v.value.pp.trim()) ? ` := ${v.value.pp}` : ""
  return `${name} : ${v.type?.pp ?? "?"}${value}`
}

/** Goals in Lean's usual display (`hyps ⊢ target`), numbered when there are several. */
export function renderGoals(goals: Pantograph.Goal[]) {
  if (!goals.length) return "No goals"
  return goals
    .map((g, i) => {
      const head = goals.length > 1 ? `case ${i + 1}/${goals.length}${g.userName ? ` (${g.userName})` : ""}\n` : ""
      return head + [...g.vars.map(renderVar), `⊢ ${g.target.pp ?? "?"}`].join("\n")
    })
    .join("\n\n")
}

function classify(messages: Pantograph.Message[] = []): EnvFeedback {
  const text = messages.map((m) => m.data).join("\n")
  const summary = compactText(text, 600) || "tactic failed"
  if (/unknown (?:identifier|constant)|unknownIdentifier|unknown namespace|failed to synthesize/i.test(text)) {
    const missing = /unknown (?:identifier|constant) [`'‘]?([^`'’\s]+)/i.exec(text)?.[1]
    return { kind: "environment_problem", summary, missing_symbol: missing }
  }
  if (/unexpected token|expected|unknown tactic|parse error/i.test(text)) return { kind: "syntax_or_engine_problem", summary }
  return { kind: "environment_problem", summary }
}

function summarize(session: LeanSessionState, fb?: EnvFeedback, previous?: string): SessionSummary {
  const last = session.tactic_history.at(-1)
  const now = renderGoals(session.goals)
  return {
    last_success: last?.result === "success" ? last.tactic : session.summary?.last_success ?? null,
    last_failure: last?.result === "failure" ? last.tactic : session.summary?.last_failure ?? null,
    last_error_class: fb ? fb.kind : session.summary?.last_error_class ?? null,
    remaining_goals: session.goals.length,
    frontier: compactText(now, 300),
    changed: previous !== undefined && previous !== now,
  }
}

// ---------------------------------------------------------------------------------------------------------------
// Building goal states from the staged source

type Prepared = {
  root: string
  modules: string[]
  body: string
  bodyLine: number
  decl: LeanSource.Declaration
  regions: LeanRegion.Region[]
  region?: LeanRegion.Region
}

/** Header split, masked regions, text cut after the target declaration (positions are body-relative). */
export function prepareSource(file: string, content: string, theorem: string, admitID?: string): Prepared {
  const root = LeanProject.findRoot(file)
  if (!root) throw new Error(`no Lake project contains ${file}`)
  const header = LeanSource.header(content)
  const body = content.slice(header.bodyOffset)
  const decl = LeanSource.findDeclaration(body, theorem)
  if (!decl || decl.assign === undefined) throw new Error(`declaration ${theorem} with a proof was not found in ${path.basename(file)}`)
  const parsed = LeanRegion.parse(body)
  const regions = parsed.regions.filter((r) => r.beginStart >= decl.start && r.endEnd <= decl.end)
  const region = admitID ? regions.find((r) => r.admit_id === admitID) : undefined
  if (admitID && !region) {
    const error = parsed.errors.find((e) => e.admit_id === admitID)
    throw new Error(`proof_region ${admitID} not found in ${theorem}${error ? `: ${error.message}` : ""}`)
  }
  if (region && !region.target) throw new Error(`proof_region ${admitID} has no \`have … := (by …)\` target`)
  const masked = LeanRegion.maskRegions(body.slice(0, decl.end), regions.filter((r) => r.target))
  return { root, modules: header.imports, body: masked, bodyLine: header.bodyLine, decl, regions, region }
}

/** Body text for a theorem-scope session: the declaration's proof replaced by `sorry`. */
function theoremScopeBody(prepared: Prepared) {
  const declStart = prepared.decl.start
  const masked = prepared.body
  const assign = LeanSource.findDeclaration(masked.slice(declStart), prepared.decl.name)?.assign
  if (assign === undefined) throw new Error(`could not locate the proof of ${prepared.decl.name}`)
  return masked.slice(0, declStart + assign) + ":= by\n  sorry\n"
}

type Entry = { stateId: number; goals: Pantograph.Goal[]; foreign: string[]; generation: number }

async function distilLast(proc: Pantograph.Process, body: string, bodyLine: number) {
  let reply: { targets: { stateId: number; goals: Pantograph.Goal[] }[] }
  try {
    reply = await proc.request("frontend.distil", { file: body, ignoreValues: false })
  } catch (error) {
    if (error instanceof Pantograph.PantographError && error.kind === "command") {
      // positions in the message are body-relative; report file lines
      const message = error.message.replace(/<anonymous>:(\d+):(\d+)/g, (_, l, c) => `line ${Number(l) + bodyLine}:${c}`)
      throw new Error(`the staged file does not elaborate up to the target: ${compactText(message, 1500)}`)
    }
    throw error
  }
  const target = reply.targets.at(-1)
  if (!target) throw new Error("the target declaration has no open goal (is its proof already complete?)")
  return target
}

async function openEntry(prepared: Prepared, scope: "theorem" | "assigned_region"): Promise<Entry> {
  const proc = Pantograph.forProject(prepared.root, prepared.modules)
  if (scope === "theorem") {
    const target = await distilLast(proc, theoremScopeBody(prepared), prepared.bodyLine)
    return { stateId: target.stateId, goals: target.goals, foreign: [], generation: proc.generation }
  }
  const region = prepared.region!
  const target = await distilLast(proc, prepared.body, prepared.bodyLine)
  const statement = region.target!.statement
  const scan = LeanTerm.scan(statement)
  if (!scan.ok) throw new Error(`region ${region.admit_id} statement is not a closed proposition: ${scan.reason}`)
  // Regions come back in reverse source order; try the expected position first, then the others.
  const order = [...prepared.regions].filter((r) => r.target).sort((a, b) => a.target!.open - b.target!.open)
  const position = order.findIndex((r) => r.admit_id === region.admit_id)
  // [trailing goal?, r(n-1), …, r0]: region at source position p sits at goals.length - 1 - p
  const expectedIndex = target.goals.length - 1 - position
  const indices = [expectedIndex, ...target.goals.map((_, i) => i).filter((i) => i !== expectedIndex)].filter(
    (i) => i >= 0 && i < target.goals.length,
  )
  for (const goalId of indices) {
    const shown = await proc.request<Pantograph.TacticResult>("goal.tactic", {
      stateId: target.stateId,
      goalId,
      tactic: `show ${scan.text}`,
    })
    if (!shown.goals || shown.nextStateId === undefined) continue
    const others = target.goals.filter((_, i) => i !== goalId).map((g) => g.name)
    const ours = shown.goals.filter((g) => !others.includes(g.name))
    if (ours.length !== 1) continue
    return { stateId: shown.nextStateId, goals: shown.goals, foreign: others, generation: proc.generation }
  }
  throw new Error(`session_state_desync: no goal of ${prepared.decl.name} matches the statement of proof_region ${region.admit_id}`)
}

function ownGoals(session: { goals: Pantograph.Goal[]; foreign: string[] }) {
  return session.goals.filter((g) => !session.foreign.includes(g.name))
}

async function runTactic(session: LeanSessionState, tactic: string) {
  const proc = Pantograph.forProject(session.root, session.modules)
  const own = ownGoals(session)
  if (!own.length) return { reply: { messages: [{ severity: "error", data: "no goals remain in this session" }] } as Pantograph.TacticResult, proc }
  const goalId = session.goals.findIndex((g) => g.name === own[0].name)
  const reply = await proc.request<Pantograph.TacticResult>("goal.tactic", { stateId: session.stateId, goalId, tactic })
  return { reply, proc }
}

/** Re-open from the current source and replay the successful tactics (source changed or REPL restarted). */
async function resynchronize(sessionID: string, session: LeanSessionState) {
  const content = await ProofEditTransaction.readSource(sessionID, session.file)
  const hash = fingerprint(content)
  const proc = Pantograph.forProject(session.root, session.modules)
  if (hash === session.source_hash && proc.generation === session.generation) return { ok: true as const, resynced: false }
  const prepared = prepareSource(session.file, content, session.theorem, session.scope === "assigned_region" ? session.admit_id : undefined)
  if (prepared.modules.join(" ") !== session.modules.join(" ")) session.modules = prepared.modules
  const entry = await openEntry(prepared, session.scope)
  Object.assign(session, { stateId: entry.stateId, goals: entry.goals, foreign: entry.foreign, generation: entry.generation, source_hash: hash })
  for (const record of session.tactic_history.filter((r) => r.result === "success")) {
    const { reply } = await runTactic(session, record.tactic)
    if (!reply.goals || reply.nextStateId === undefined) {
      session.last_error = `session_state_desync: replaying \`${record.tactic}\` on the changed source failed: ${compactText(reply.messages?.map((m) => m.data).join(" ") ?? "", 600)}`
      session.desync_count++
      return { ok: false as const }
    }
    session.stateId = reply.nextStateId
    session.goals = reply.goals
  }
  session.snapshots = {}
  session.desync_count = 0
  return { ok: true as const, resynced: true }
}

function assertTactic(tactic: string) {
  const hits = LeanSource.forbiddenTokens(tactic)
  if (hits.length) throw new Error(`lean_session step rejects forbidden tokens: ${hits.join(", ")}`)
  if (/\bnative_decide\b/.test(tactic)) throw new Error("lean_session step rejects `native_decide` (its axiom is rejected by the final gate)")
  if (tactic.length > 4000) throw new Error("lean_session step accepts one tactic or a short tactic block")
}

function backendMessage(error: unknown) {
  if (error instanceof Pantograph.PantographError) return `${error.kind === "backend" ? "backend_error" : "command_error"} [${error.code}]: ${error.message}`
  return error instanceof Error ? error.message : String(error)
}

export const LeanSessionTool = Tool.define("lean_session", {
  description: DESCRIPTION,
  parameters: z.object({
    op: z.enum(["open", "step", "goal", "inspect", "snapshot", "undo", "close", "status"]).describe("Session operation"),
    file: z.string().optional().describe("Path to the .lean file containing the theorem (for open)"),
    theorem: z.string().optional().describe("Theorem name to prove (for open)"),
    tactic: z.string().optional().describe("One Lean tactic (or a short tactic block) to run on the session's first goal (for step)"),
    snapshot_id: z.string().optional().describe("Snapshot ID to return to (for undo)"),
    scope: z
      .enum(["theorem", "assigned_region"])
      .optional()
      .describe("Open at the theorem's proof start, or at the active assigned proof_region"),
    admit_id: z.string().optional().describe("proof_region identifier for a region-scoped open"),
    expected_goal: z.string().optional().describe("Expected region entry proposition (checked by elaboration, not text)"),
    symbols: z
      .array(z.string().regex(/^[\p{L}_][\p{L}\p{N}_'!?]*(?:\.[\p{L}_][\p{L}\p{N}_'!?]*)*$/u))
      .max(8)
      .optional()
      .describe("Up to eight declaration names whose types to show during inspect"),
    left_expression: z.string().max(2000).optional().describe("Left Lean term for inspect (definitional equality test)"),
    right_expression: z.string().max(2000).optional().describe("Right Lean term for inspect"),
  }),
  async execute(params, ctx): Promise<{ title: string; output: string; metadata: Record<string, any> }> {
    await ctx.ask({ permission: "lean_session", patterns: ["*"], always: ["*"], metadata: { op: params.op } })
    const key = ctx.sessionID

    try {
      switch (params.op) {
        case "open": {
          if (!params.file) throw new Error("open requires file")
          if (!params.theorem) throw new Error("open requires theorem")
          const file = path.isAbsolute(params.file) ? params.file : path.resolve(Instance.directory, params.file)
          if (!file.endsWith(".lean")) throw new Error("lean_session works on .lean files")
          ProofEditTransaction.assertStagedReadSynchronized(ctx.sessionID, file, "opening a Lean session")
          const assignment = SessionProofWorkflow.activeLemmaAssignment(ctx.sessionID)
          if (ctx.agent === "lemma" && assignment && params.scope === "theorem") {
            throw new Error(
              `session_state_desync: lemma worker ${ctx.sessionID} is assigned to proof_region ${assignment.admit_id}; theorem-scope open is not permitted`,
            )
          }
          const admitID = params.scope === "theorem" ? undefined : params.admit_id ?? assignment?.admit_id
          const scope = admitID ? ("assigned_region" as const) : ("theorem" as const)
          if (params.scope === "assigned_region" && !admitID) throw new Error("assigned_region open requires admit_id or a live lemma assignment")
          const content = await ProofEditTransaction.readSource(ctx.sessionID, file)
          const prepared = prepareSource(file, content, params.theorem, admitID)
          const entry = await openEntry(prepared, scope)
          const session: LeanSessionState = {
            session_id: "sess_" + randomBytes(4).toString("hex"),
            file,
            theorem: params.theorem,
            scope,
            admit_id: admitID,
            region_statement: prepared.region?.target?.statement,
            expected_goal: params.expected_goal,
            root: prepared.root,
            modules: prepared.modules,
            source_hash: fingerprint(content),
            generation: entry.generation,
            foreign: entry.foreign,
            stateId: entry.stateId,
            goals: entry.goals,
            tactic_history: [],
            snapshots: {},
            last_error: null,
            desync_count: 0,
            entry_goal: "",
            entry_fingerprint: "",
          }
          session.goals = entry.goals
          const shown = renderGoals(ownGoals(session))
          session.entry_goal = shown
          session.entry_fingerprint = fingerprint(shown)
          session.snapshots.initial = {
            id: "initial",
            stateId: entry.stateId,
            generation: entry.generation,
            goals: entry.goals,
            tactic_index: 0,
          }
          // Expected entry goal: compared by elaboration on the live goal (D10), never by text.
          let entryMatches = true
          if (params.expected_goal) {
            const scan = LeanTerm.scan(params.expected_goal)
            if (!scan.ok) entryMatches = false
            else {
              const { reply } = await runTactic(session, `show ${scan.text}`)
              entryMatches = Boolean(reply.goals)
            }
          }
          if (!entryMatches) session.desync_count = 2
          session.summary = summarize(session)
          sessions.set(key, session)
          return {
            title: entryMatches
              ? `Session opened for ${params.theorem}${admitID ? `:${admitID}` : ""}`
              : `session_state_desync: ${params.theorem}${admitID ? `:${admitID}` : ""}`,
            output: [
              `Session ${session.session_id}`,
              `Scope: ${admitID ? `proof_region ${admitID}` : "theorem start"}`,
              entryMatches ? undefined : `session_state_desync: the live goal is not definitionally equal to expected_goal (${compactText(params.expected_goal ?? "", 400)})`,
              `Goal:\n${shown}`,
            ]
              .filter((line): line is string => Boolean(line))
              .join("\n"),
            metadata: {
              op: "open",
              session_id: session.session_id,
              scope,
              admit_id: admitID,
              goal_fingerprint: session.entry_fingerprint,
              kind: entryMatches ? "proof_progress" : "session_state_desync",
            },
          }
        }

        case "step": {
          const session = sessions.get(key)
          if (!session) throw new Error("No session open. Use open first.")
          if (!params.tactic) throw new Error("step requires a tactic")
          assertTactic(params.tactic)
          if (session.desync_count >= 2) {
            return {
              title: "session_state_desync",
              output: `session_state_desync\n${session.last_error ?? "the session's entry goal does not match"}\nThe tactic was not run. Re-open the session.`,
              metadata: { op: "step", session_id: session.session_id, kind: "session_state_desync", tactic_applied: false },
            }
          }
          const sync = await resynchronize(key, session)
          if (!sync.ok) {
            return {
              title: "session_state_desync",
              output: `session_state_desync\n${session.last_error}\nThe tactic was not run. Re-open the session.`,
              metadata: { op: "step", session_id: session.session_id, kind: "session_state_desync", admit_id: session.admit_id, tactic_applied: false },
            }
          }
          const previous = renderGoals(ownGoals(session))
          const { reply } = await runTactic(session, params.tactic)
          const ok = Boolean(reply.goals) && reply.nextStateId !== undefined
          const feedback: EnvFeedback = ok
            ? {
                kind: "proof_progress",
                summary: ownGoals({ goals: reply.goals!, foreign: session.foreign }).length ? "tactic succeeded" : "no goals remain in this session",
                remaining_goals: ownGoals({ goals: reply.goals!, foreign: session.foreign }).length,
              }
            : classify(reply.messages)
          session.tactic_history.push({ tactic: params.tactic, result: ok ? "success" : "failure", feedback, time: new Date().toISOString() })
          if (ok) {
            session.stateId = reply.nextStateId!
            session.goals = reply.goals!
            session.last_error = null
          } else session.last_error = feedback.summary
          session.summary = summarize(session, feedback, previous)
          const now = renderGoals(ownGoals(session))
          const warnings = (reply.messages ?? []).filter((m) => m.severity !== "error").map((m) => m.data)
          return {
            title: `step: ${params.tactic.slice(0, 40)} [${feedback.kind}]`,
            output: [
              `[${feedback.kind}] ${feedback.summary}`,
              warnings.length ? `messages: ${compactText(warnings.join(" | "), 600)}` : undefined,
              reply.hasSorry ? "warning: the resulting proof term contains `sorry`" : undefined,
              `Goal:\n${now.slice(0, 4000)}`,
            ]
              .filter((line): line is string => Boolean(line))
              .join("\n"),
            metadata: {
              op: "step",
              session_id: session.session_id,
              kind: feedback.kind,
              resynced: sync.resynced,
              goal_fingerprint: fingerprint(now),
              remaining_goals: ownGoals(session).length,
              admit_id: session.admit_id,
            },
          }
        }

        case "goal": {
          const session = sessions.get(key)
          if (!session) throw new Error("No session open. Use open first.")
          const sync = await resynchronize(key, session)
          if (!sync.ok) {
            return {
              title: "session_state_desync",
              output: `session_state_desync\n${session.last_error}`,
              metadata: { op: "goal", session_id: session.session_id, kind: "session_state_desync", admit_id: session.admit_id },
            }
          }
          const now = renderGoals(ownGoals(session))
          return {
            title: "Current goal",
            output: `Goal:\n${now}\nRemaining: ${ownGoals(session).length}`,
            metadata: {
              op: "goal",
              session_id: session.session_id,
              kind: "proof_progress",
              goal_fingerprint: fingerprint(now),
              admit_id: session.admit_id,
              resynced: sync.resynced,
            },
          }
        }

        case "inspect": {
          const session = sessions.get(key)
          if (!session) throw new Error("No session open. Use open first.")
          if (!params.left_expression || !params.right_expression) throw new Error("inspect requires left_expression and right_expression")
          for (const [label, text] of [["left_expression", params.left_expression], ["right_expression", params.right_expression]] as const) {
            LeanTerm.assertPureTerm(label, text)
            const scan = LeanTerm.scan(text)
            if (!scan.ok) throw new Error(`${label}: ${scan.reason}`)
          }
          const sync = await resynchronize(key, session)
          if (!sync.ok) {
            return {
              title: "session_state_desync",
              output: "session_state_desync: inspection was not run because the live goal could not be resynchronized",
              metadata: { op: "inspect", session_id: session.session_id, kind: "session_state_desync" },
            }
          }
          const proc = Pantograph.forProject(session.root, session.modules)
          const symbols = params.symbols ?? []
          const types: string[] = []
          for (const symbol of symbols) {
            try {
              const info = await proc.request<{ type?: Pantograph.Expression }>("env.inspect", { name: symbol })
              types.push(`${symbol} : ${info.type?.pp ?? "?"}`)
            } catch (error) {
              types.push(`${symbol}: ${backendMessage(error)}`)
            }
          }
          const { reply } = await runTactic(session, `have __lb_audit : (${params.left_expression}) = (${params.right_expression}) := rfl`)
          const diagnostic = compactText((reply.messages ?? []).map((m) => m.data).join("\n"), 1000)
          const outcome: ContextNormalizationAudit["outcome"] = reply.goals
            ? "convertible"
            : /type mismatch|not definitionally equal|failed to unify|The rfl tactic/i.test(diagnostic)
              ? "not_convertible"
              : "inconclusive"
          const audit = recordContextAudit(key, {
            audit_id: "audit_" + randomBytes(6).toString("hex"),
            outcome,
            inspected_symbols: symbols,
            left_expression: params.left_expression,
            right_expression: params.right_expression,
            left_summary: compactText(params.left_expression),
            right_summary: compactText(params.right_expression),
            goal_fingerprint: fingerprint(renderGoals(ownGoals(session))),
            hypotheses_fingerprint: fingerprint((ownGoals(session)[0]?.vars ?? []).map(renderVar).join("\n")),
            diagnostic: diagnostic || undefined,
            verified: true,
          })
          return {
            title: `Context audit: ${audit.outcome}`,
            output: [
              `audit_id: ${audit.audit_id}`,
              `outcome: ${audit.outcome}`,
              `left: ${audit.left_summary}`,
              `right: ${audit.right_summary}`,
              types.length ? `symbols:\n${types.join("\n")}` : undefined,
              audit.diagnostic ? `diagnostic: ${audit.diagnostic}` : undefined,
              "next_action: treat this as diagnostic evidence only; convertible favors a local bridge, not proof completion",
            ]
              .filter((line): line is string => Boolean(line))
              .join("\n"),
            metadata: { op: "inspect", session_id: session.session_id, context_audit: audit },
          }
        }

        case "snapshot": {
          const session = sessions.get(key)
          if (!session) throw new Error("No session open. Use open first.")
          const id = "snap_" + randomBytes(4).toString("hex")
          session.snapshots[id] = {
            id,
            stateId: session.stateId,
            generation: session.generation,
            goals: session.goals,
            tactic_index: session.tactic_history.length,
            summary: session.summary ? { ...session.summary } : undefined,
          }
          return {
            title: `Snapshot created: ${id}`,
            output: `Snapshot ${id} at tactic ${session.tactic_history.length}\nGoal:\n${renderGoals(ownGoals(session)).slice(0, 4000)}`,
            metadata: { op: "snapshot", session_id: session.session_id },
          }
        }

        case "undo": {
          const session = sessions.get(key)
          if (!session) throw new Error("No session open. Use open first.")
          if (!params.snapshot_id) throw new Error("undo requires snapshot_id")
          const snap = session.snapshots[params.snapshot_id]
          if (!snap) throw new Error(`Snapshot not found: ${params.snapshot_id}. Available: ${Object.keys(session.snapshots).join(", ")}`)
          session.tactic_history = session.tactic_history.slice(0, snap.tactic_index)
          if (snap.generation === Pantograph.forProject(session.root, session.modules).generation) {
            session.stateId = snap.stateId
            session.goals = snap.goals
          } else {
            // the REPL restarted: rebuild from the source and replay the kept history
            session.generation = -1
            const sync = await resynchronize(key, session)
            if (!sync.ok) throw new Error(session.last_error ?? "could not rebuild the snapshot")
          }
          session.last_error = null
          session.desync_count = 0
          session.summary = snap.summary ? { ...snap.summary } : session.summary
          return {
            title: `Rolled back to snapshot ${params.snapshot_id}`,
            output: `Restored to tactic ${snap.tactic_index}\nGoal:\n${renderGoals(ownGoals(session)).slice(0, 4000)}`,
            metadata: { op: "undo", session_id: session.session_id },
          }
        }

        case "close": {
          const session = sessions.get(key)
          if (!session) throw new Error("No session open. Use open first.")
          const successes = session.tactic_history.filter((t) => t.result === "success").length
          const failures = session.tactic_history.length - successes
          sessions.delete(key)
          return {
            title: "Session closed",
            output: `Session ${session.session_id} closed. ${successes} successful, ${failures} failed tactics. ${Object.keys(session.snapshots).length} snapshots.`,
            metadata: { op: "close", session_id: session.session_id },
          }
        }

        case "status": {
          const session = sessions.get(key)
          if (!session) throw new Error("No session open. Use open first.")
          const lines = [
            `Session: ${session.session_id}`,
            `Scope: ${session.admit_id ? `proof_region ${session.admit_id}` : "theorem"}`,
            `Desync count: ${session.desync_count}`,
            `Goal:\n${renderGoals(ownGoals(session)).slice(0, 4000)}`,
            `Tactics: ${session.tactic_history.length} (${session.tactic_history.filter((t) => t.result === "success").length} ok)`,
            `Snapshots: ${Object.keys(session.snapshots).join(", ")}`,
            session.last_error ? `Last error: ${session.last_error}` : "",
          ].filter(Boolean)
          return { title: "Session status", output: lines.join("\n"), metadata: { op: "status", session_id: session.session_id } }
        }

        default:
          throw new Error(`Unknown operation: ${params.op}`)
      }
    } catch (error) {
      // Backend failures are tool errors (free under D5), never a semantic mismatch.
      if (error instanceof Pantograph.PantographError && error.kind === "backend") {
        return {
          title: "lean_session backend error",
          output: `backend_error [${error.code}]: ${error.message}\nThis is a tool failure, not a proof result. Retry the operation; the session re-opens from the source.`,
          metadata: { op: params.op, kind: "backend_error", code: error.code },
        }
      }
      throw error
    }
  },
})

// ---------------------------------------------------------------------------------------------------------------
// Statement-equivalence service (DECISIONS D10, known-problem-fixes/lean_session-equivalence.md)

export namespace LeanEquivalence {
  export type Verdict = "equivalent" | "different" | "a_does_not_elaborate" | "b_does_not_elaborate" | "backend_error"

  const cache = new Map<string, { verdict: Verdict; detail?: string }>()

  function normalize(text: string) {
    return text.replace(/\s+/g, " ").replace(/\(\s+/g, "(").replace(/\s+\)/g, ")").trim()
  }

  /**
   * Compare two closed propositions (e.g. a plan's `root_goal` with the theorem's statement) in the context of the
   * Lake project of `file`: `goal.start a`, then `show b` (definitional equality, default transparency). `levels`
   * declares the universe names the statements use.
   */
  export async function equivalentClosed(input: {
    file: string
    modules: string[]
    a: string
    b: string
    levels?: string[]
  }): Promise<{ verdict: Verdict; detail?: string }> {
    if (normalize(input.a) === normalize(input.b)) return { verdict: "equivalent" }
    const scanA = LeanTerm.scan(input.a)
    if (!scanA.ok) return { verdict: "a_does_not_elaborate", detail: scanA.reason }
    const scanB = LeanTerm.scan(input.b)
    if (!scanB.ok) return { verdict: "b_does_not_elaborate", detail: scanB.reason }
    const root = LeanProject.findRoot(input.file)
    if (!root) return { verdict: "backend_error", detail: "no Lake project" }
    const key = fingerprint([root, input.modules.join(" "), scanA.text, scanB.text, (input.levels ?? []).join(",")].join("\n"))
    const cached = cache.get(key)
    if (cached) return cached
    const proc = Pantograph.forProject(root, input.modules)
    let verdict: { verdict: Verdict; detail?: string }
    try {
      const start = await proc.request<{ stateId: number }>("goal.start", { expr: scanA.text, ...(input.levels?.length ? { levels: input.levels } : {}) })
      const shown = await proc.request<Pantograph.TacticResult>("goal.tactic", {
        stateId: start.stateId,
        tactic: `set_option maxHeartbeats 200000 in show ${scanB.text}`,
      })
      if (shown.goals) verdict = { verdict: "equivalent" }
      else {
        const detail = (shown.messages ?? []).map((m) => m.data).join("\n")
        verdict = /not definitionally equal|type mismatch/i.test(detail)
          ? { verdict: "different", detail: compactText(detail, 600) }
          : { verdict: "b_does_not_elaborate", detail: compactText(detail, 600) }
      }
    } catch (error) {
      verdict =
        error instanceof Pantograph.PantographError && error.kind === "command"
          ? { verdict: "a_does_not_elaborate", detail: compactText(error.message, 600) }
          : { verdict: "backend_error", detail: backendMessage(error) }
    }
    if (verdict.verdict !== "backend_error") {
      if (cache.size > 512) cache.clear()
      cache.set(key, verdict)
    }
    return verdict
  }
}
