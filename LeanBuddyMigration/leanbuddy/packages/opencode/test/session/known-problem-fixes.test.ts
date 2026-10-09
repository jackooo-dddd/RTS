import { describe, expect, test } from "bun:test"
import type { Tool } from "../../src/tool/tool"
import { ProofPlanTool } from "../../src/tool/proof-plan"
import type { ProofPlanStep as ProofPlanStepValue } from "../../src/tool/proof-schema"
import { Instance } from "../../src/project/instance"
import { Session } from "../../src/session"
import { SessionProof } from "../../src/session/session-proof"
import { SessionProofWorkflow } from "../../src/session/proof-workflow"
import { tmpdir } from "../fixture/fixture"

// Tests listed in known-problem-fixes/README.md: K4 (no_ready_region), K5 (shared plan), K8 (repeated escalation),
// S14 (checked source before ending), S26 (solved is recomputed from the source). K2 and K6/K7 are covered in
// test/tool/proof-review.test.ts and test/tool/lean-statement-check.test.ts.

function context(sessionID: string): Tool.Context {
  return {
    sessionID,
    messageID: `msg-${sessionID}`,
    callID: `call-${sessionID}`,
    agent: "prover",
    abort: AbortSignal.any([]),
    messages: [],
    metadata: () => {},
    ask: async () => {},
  }
}

function node(overrides: Partial<ProofPlanStepValue> = {}): ProofPlanStepValue {
  return {
    paper_step_id: "step-1",
    node_id: "leaf-1",
    kind: "semantic_bridge",
    layer: "semantic",
    paper_claim: "Prove a strict intermediate fact.",
    formal_goal: "A",
    candidate_lemmas: [],
    prosa_candidate_lemmas: [],
    mathlib_candidate_lemmas: [],
    required_hypotheses: [],
    fallback_plan: [],
    done_when: "The strict child is available.",
    depends_on: [],
    dependency_uses: [],
    consumers: ["parent_composition"],
    claim_delta: "Replace A ∧ B with the strict child A.",
    transformations: ["semantic_bound"],
    delegation_candidate: true,
    risk: "low",
    evidence_status: "candidate",
    target_normal_form: "A",
    ...overrides,
  }
}

function skeleton(proof = "sorry") {
  return [
    "theorem demo (A B : Prop) (HA : A) (HB : B) : A ∧ B := by",
    "/- proof_region begin owner: lemma admit_id: gap-a theorem: demo target: Ha plan_node: leaf-1 -/",
    "/- contract plan_node: leaf-1 depends_on: none source: context-derived input: HA output: Ha expected: local_fact normal_form: \"A\" evidence: local:HA -/",
    `have Ha : A := (by ${proof})`,
    "/- proof_region end admit_id: gap-a -/",
    "  exact ⟨Ha, HB⟩",
    "",
  ].join("\n")
}

/** An accepted one-node plan for `demo`, materialised as region gap-a. */
async function acceptedPlan(dir: string, name: string) {
  const file = `${dir}/${name}.lean`
  await Bun.write(file, "theorem demo (A B : Prop) (HA : A) (HB : B) : A ∧ B := by\n  sorry\n")
  const session = await Session.create({})
  SessionProof.set(session.id, file, { line: 0, character: 0 }, "manual")
  const tool = await ProofPlanTool.init()
  const accepted = await tool.execute({ theorem: "demo", root_goal: "A ∧ B", nodes: [node()], edges: [] }, context(session.id))
  expect(accepted.metadata.planning_status).toBe("accepted")
  const source = skeleton()
  await Bun.write(file, source)
  const state = SessionProofWorkflow.refresh(session.id, file, source).state
  expect(state.queue.map((item) => item.admit_id)).toEqual(["gap-a"])
  return { file, session, source }
}

function escalate(
  sessionID: string,
  type: "needs_preceding_bridge" | "not_local",
  history = 0,
) {
  const state = SessionProofWorkflow.get(sessionID)!
  SessionProofWorkflow.set(sessionID, {
    ...state,
    queue: state.queue.map((item) => ({
      ...item,
      status: "escalated" as const,
      escalation_type: type,
      escalation_reason: "the region needs another fact",
      escalations: Array.from({ length: history }, () => ({ type, source_hash: item.region_fingerprint! })),
    })),
    updated: Date.now(),
  })
}

describe("known-problem fixes", () => {
  test("K4: an empty schedule is explained with a required action", async () => {
    await using tmp = await tmpdir({ git: true })
    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const { session, source } = await acceptedPlan(tmp.path, "k4")
        escalate(session.id, "needs_preceding_bridge")
        expect(await SessionProofWorkflow.suggestNextSubtask(session.id, [], source)).toBeUndefined()
        const status = await SessionProofWorkflow.schedulerStatus(session.id, source)
        expect(status?.kind).toBe("no_ready_region")
        expect(status?.admit_ids).toEqual(["gap-a"])
        expect(status?.reason).toContain("escalated")
        expect(status?.required_action).toContain('proof_plan amendment (action "amend")')
        expect(status?.required_action).toContain("gap-a")
        await Session.remove(session.id)
      },
    })
  })

  test("K4: a running task is an explicit, bounded wait", async () => {
    await using tmp = await tmpdir({ git: true })
    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const { session, source } = await acceptedPlan(tmp.path, "k4-running")
        const state = SessionProofWorkflow.get(session.id)!
        SessionProofWorkflow.set(session.id, {
          ...state,
          active_admit_id: "gap-a",
          active_task_id: "task-1",
          queue: state.queue.map((item) => ({
            ...item,
            status: "running" as const,
            task_id: "task-1",
            running_started_at: Date.now(),
            running_lease_expires_at: Date.now() + 600_000,
          })),
          updated: Date.now(),
        })
        const status = await SessionProofWorkflow.schedulerStatus(session.id, source)
        expect(status?.reason).toContain("running")
        expect(status?.required_action).toStartWith("none")
        await Session.remove(session.id)
      },
    })
  })

  test("K8: the fourth same-type escalation of an unchanged region is not dispatched", async () => {
    await using tmp = await tmpdir({ git: true })
    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const { file, session, source } = await acceptedPlan(tmp.path, "k8")
        escalate(session.id, "not_local", SessionProofWorkflow.REPEATED_ESCALATION_LIMIT)
        // the history survives a refresh of the unchanged region
        const refreshed = SessionProofWorkflow.refresh(session.id, file, source).state
        expect(refreshed.queue[0]?.escalations).toHaveLength(SessionProofWorkflow.REPEATED_ESCALATION_LIMIT)
        expect(SessionProofWorkflow.repeatedEscalationBlocked(refreshed.queue[0]!)).toBe(true)
        await expect(
          SessionProofWorkflow.assertProofTaskDispatchAllowed({
            sessionID: session.id,
            subagentType: "lemma",
            proofProducing: true,
            lemmaAssignment: { file, theorem: "demo", admit_id: "gap-a" } as any,
          }),
        ).rejects.toThrow("escalated 3 times")
        const status = await SessionProofWorkflow.schedulerStatus(session.id, source)
        expect(status?.reason).toContain("escalated 3 times")
        // a blocked region unlocks an amendment even though `not_local` alone would not
        expect(SessionProofWorkflow.getPlanAmendmentEligibility(session.id, file).available).toBe(true)

        // changing the region text resets the history
        const changed = source.replace("(by sorry)", "(by\n  sorry)")
        await Bun.write(file, changed)
        const afterChange = SessionProofWorkflow.refresh(session.id, file, changed).state
        expect(afterChange.queue[0]?.escalations).toBeUndefined()
        expect(SessionProofWorkflow.repeatedEscalationBlocked(afterChange.queue[0]!)).toBe(false)
        await Session.remove(session.id)
      },
    })
  })

  test("K5: a fresh session bound to the same theorem sees the accepted plan", async () => {
    await using tmp = await tmpdir({ git: true })
    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const { file, session, source } = await acceptedPlan(tmp.path, "k5")
        const owner = SessionProofWorkflow.getDecompositionPlanState(session.id, file)
        const fresh = await Session.create({})
        SessionProof.set(fresh.id, file, { line: 0, character: 0 }, "manual")
        const recovered = SessionProofWorkflow.refresh(fresh.id, file, source).state.decomposition_plan
        expect(recovered?.status).toBe("accepted")
        expect(recovered?.accepted_semantic_fingerprint).toBe(owner?.accepted_semantic_fingerprint)
        await Session.remove(fresh.id)
        await Session.remove(session.id)
      },
    })
  })

  test("S26 and S14: a region with sorry is never solved; checks are remembered per source", async () => {
    await using tmp = await tmpdir({ git: true })
    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const { file, session, source } = await acceptedPlan(tmp.path, "s26")
        expect(SessionProofWorkflow.sourceChecked(file, source)).toBe(false)
        await SessionProofWorkflow.recordCompilerResult({
          sessionID: session.id,
          file,
          source,
          validator: "checkpoint",
          ok: true,
        })
        expect(SessionProofWorkflow.sourceChecked(file, source)).toBe(true)
        const pending = SessionProofWorkflow.refresh(session.id, file, source).state
        expect(pending.queue[0]?.status).not.toBe("solved")

        const proved = skeleton("exact HA")
        await Bun.write(file, proved)
        expect(SessionProofWorkflow.sourceChecked(file, proved)).toBe(false)
        await SessionProofWorkflow.recordCompilerResult({
          sessionID: session.id,
          file,
          source: proved,
          validator: "checkpoint",
          ok: true,
        })
        expect(SessionProofWorkflow.refresh(session.id, file, proved).state.queue[0]?.status).toBe("solved")
        await Session.remove(session.id)
      },
    })
  })
})
