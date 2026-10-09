import path from "path"
import { describe, expect, spyOn, test } from "bun:test"
import { fileURLToPath } from "url"
import { Instance } from "../../src/project/instance"
import { Session } from "../../src/session"
import { MessageV2 } from "../../src/session/message-v2"
import { SessionPrompt } from "../../src/session/prompt"
import { SessionProof } from "../../src/session/session-proof"
import { SessionProofWorkflow } from "../../src/session/proof-workflow"
import { Log } from "../../src/util/log"
import { Identifier } from "../../src/id/id"
import { tmpdir } from "../fixture/fixture"

Log.init({ print: false })

const ROLLOVER = 1_786_706_395_136

test("controller stop text is completed so the CLI can emit its reason", async () => {
  await using tmp = await tmpdir({
    git: true,
    config: {
      provider: {
        test: {
          npm: "@ai-sdk/openai-compatible",
          options: { apiKey: "test", baseURL: "http://127.0.0.1:1/v1" },
          models: { test: { name: "Test" } },
        },
      },
    },
  })
  await Instance.provide({
    directory: tmp.path,
    fn: async () => {
      const file = path.join(tmp.path, "theorem.v")
      await Bun.write(file, "Lemma demo : True. Proof. admit. Admitted.\n")
      const session = await Session.create({})
      const guard = spyOn(SessionProofWorkflow, "assessFallbackGuard").mockResolvedValue({
        tripped: true,
        guard: {},
        assignment: { admit_id: "gap_1" },
        message: "same checkpoint failure recurred; parent repair budget exhausted",
      } as any)
      try {
        await SessionPrompt.prompt({
          sessionID: session.id,
          agent: "prover",
          model: { providerID: "test", modelID: "test" },
          noReply: true,
          parts: [{ type: "text", text: "Continue the proof of demo in theorem.v." }],
        })
        SessionProof.set(session.id, file, { line: 0, character: 0 }, "manual")
        const reply = await SessionPrompt.loop({ sessionID: session.id })
        const stop = reply.parts.find((part) => part.type === "text" && part.text.startsWith("stalled_wide_fallback:"))
        if (reply.info.role !== "assistant" || stop?.type !== "text") throw new Error("missing controller stop")
        expect(reply.info.finish).toBe("stop")
        expect(stop.synthetic).toBe(true)
        expect(stop.time?.end).toBeNumber()
        expect(stop.time?.end).toBe(reply.info.time.completed)
        expect(stop.text).toContain("parent repair budget exhausted")
      } finally {
        guard.mockRestore()
        SessionProof.clear(session.id)
        await Session.remove(session.id)
      }
    },
  })
})

function promptMessage(
  role: "user" | "assistant",
  id: string,
  created: number,
  text: string,
): MessageV2.WithParts {
  const info = role === "user"
    ? {
        id,
        sessionID: "ses_rollover",
        role,
        time: { created },
        agent: "prover",
        model: { providerID: "test", modelID: "test" },
      }
    : {
        id,
        sessionID: "ses_rollover",
        role,
        time: { created, completed: created + 1 },
        parentID: "msg_parent",
        modelID: "test",
        providerID: "test",
        mode: "",
        agent: "prover",
        path: { cwd: "/tmp", root: "/tmp" },
        cost: 0,
        tokens: { input: 0, output: 0, reasoning: 0, cache: { read: 0, write: 0 } },
        finish: "stop",
      }
  return {
    info: info as MessageV2.Info,
    parts: [{
      id: `prt_${id}`,
      sessionID: "ses_rollover",
      messageID: id,
      type: "text",
      text,
    }],
  }
}

describe("session.prompt queued user messages", () => {
  test("does not rewrite historical prompts when legacy IDs roll over", () => {
    const historical = promptMessage("user", "msg_ffffff973001AAAAAAAAAAAAAA", ROLLOVER - 2_000, "original prompt")
    const finished = promptMessage("assistant", "msg_000002652001BBBBBBBBBBBBBB", ROLLOVER + 1_000, "answer")
    const queued = promptMessage("user", "msg_000003652001CCCCCCCCCCCCCC", ROLLOVER + 2_000, "new request")
    const messages = [historical, finished, queued]

    SessionPrompt.wrapQueuedUserMessages(messages, finished.info as MessageV2.Assistant)

    expect((historical.parts[0] as MessageV2.TextPart).text).toBe("original prompt")
    expect((queued.parts[0] as MessageV2.TextPart).text).toContain("<system-reminder>")
    expect((queued.parts[0] as MessageV2.TextPart).text).toContain("new request")
  })
})

describe("session.prompt accepted-plan materialization tool gate", () => {
  test("stops cross-turn lookup after an edit even when proof regions already exist", async () => {
    await using tmp = await tmpdir({ git: true, config: {
      provider: { test: {
        npm: "@ai-sdk/openai-compatible", options: { apiKey: "test", baseURL: "http://127.0.0.1:1/v1" },
        models: { test: { name: "Test" } },
      } },
    } })
    await Instance.provide({ directory: tmp.path, fn: async () => {
      const file = path.join(tmp.path, "demo.v")
      await Bun.write(file, [
        "Lemma demo : True.", "Proof.",
        "(* proof_region begin owner: lemma admit_id: gap theorem: demo kind: semantic_bridge target: Hgap *)",
        "have Hgap : True. { admit. }", "(* proof_region end admit_id: gap *)", "Admitted.",
      ].join("\n"))
      const session = await Session.create({})
      const spies = [
        spyOn(SessionProofWorkflow, "assessFallbackGuard").mockResolvedValue(undefined),
        spyOn(SessionProofWorkflow, "planNextSubtask").mockResolvedValue(undefined),
        spyOn(SessionProofWorkflow, "getDecompositionPlanState").mockReturnValue({ status: "accepted", theorem: "demo", accepted_at: 1 } as any),
        spyOn(SessionProofWorkflow, "previewDecompositionMaterialization").mockReturnValue({ review: { status: "matched" } } as any),
        spyOn(SessionProofWorkflow, "getAcceptedPlanRepairEligibility").mockReturnValue({ available: false } as any),
        spyOn(SessionProofWorkflow, "currentValidationCertificates").mockReturnValue([]),
      ]
      try {
        const user = await SessionPrompt.prompt({
          sessionID: session.id, agent: "prover", model: { providerID: "test", modelID: "test" },
          noReply: true, parts: [{ type: "text", text: "Continue demo in demo.v." }],
        })
        SessionProof.set(session.id, file, { line: 1, character: 0 }, "manual")
        for (let index = 0; index <= 20; index++) {
          const id = Identifier.ascending("message")
          const now = Date.now()
          const message = promptMessage("assistant", id, now, "").info as MessageV2.Assistant
          await Session.updateMessage({ ...message, sessionID: session.id, parentID: user.info.id, finish: "tool-calls" })
          await Session.updatePart({
            id: Identifier.ascending("part"), messageID: id, sessionID: session.id, type: "tool",
            tool: index === 0 ? "edit" : "read", callID: `call_lookup_${index}`,
            state: { status: "completed", input: { filePath: file, offset: index % 2 ? 1 : 2 },
              output: index === 0 ? "Edit applied successfully." : "unchanged theorem",
              title: "demo.v", metadata: {}, time: { start: now, end: now },
            },
          })
        }
        const reply = await SessionPrompt.loop({ sessionID: session.id })
        const stop = reply.parts.find((p) => p.type === "text" && p.text.startsWith("materialization_livelock:"))
        expect(stop?.type).toBe("text")
        if (stop?.type === "text") {
          expect(stop.text).toContain('"reason":"passive_lookup_stagnation"')
          expect(stop.text).toContain('"passive_lookup_streak":20')
          expect(stop.time?.end).toBeNumber()
        }
        expect((reply.info as MessageV2.Assistant).finish).toBe("stop")
      } finally {
        spies.forEach((spy) => spy.mockRestore())
        SessionProofWorkflow.clear(session.id)
        SessionProof.clear(session.id)
        await Session.remove(session.id)
      }
    } })
  })

  test("a fresh compiler certificate resets the lookup window after child progress", () => {
    const target = "/tmp/demo.v"
    const messages = [10, 20, 30].map((end) => ({ parts: [{
      type: "tool", tool: "read", state: { status: "completed", input: { filePath: target }, time: { start: end - 1, end } },
    }] })) as any
    expect(SessionPrompt.acceptedPlanMaterializationLookupStreakForTest(messages, target)).toBe(3)
    expect(SessionPrompt.acceptedPlanMaterializationLookupStreakForTest(messages, target, 25)).toBe(1)
  })

  test("rejected and unchanged proof steps do not reset the lookup window", () => {
    for (const metadata of [
      { kind: "session_state_desync", tactic_applied: false },
      { kind: "syntax_or_engine_problem" },
      { kind: "proof_progress", summary: { changed: false } },
    ]) {
      const messages = [{ parts: [
        { type: "tool", tool: "read", state: { status: "completed", input: { filePath: "/tmp/demo.v" } } },
        { type: "tool", tool: "coq_session", state: { status: "completed", input: { op: "step", tactic: "idtac." }, metadata } },
      ] }] as any
      expect(SessionPrompt.acceptedPlanMaterializationLookupStreakForTest(messages, "/tmp/demo.v")).toBe(1)
    }
  })

  test("stops only after five stagnant materialization observations and resets on hard progress", () => {
    let state: SessionPrompt.MaterializationLivelockState | undefined
    for (let index = 0; index < 4; index++) {
      const observation = SessionPrompt.observeMaterializationLivelock(state, {
        key: "plan-a",
        missing_count: 5,
        certificate_count: 0,
      })
      state = observation.state
      expect(observation.tripped).toBe(false)
    }

    const fifth = SessionPrompt.observeMaterializationLivelock(state, {
      key: "plan-a",
      missing_count: 5,
      certificate_count: 0,
    })
    expect(fifth.tripped).toBe(true)

    const progressed = SessionPrompt.observeMaterializationLivelock(fifth.state, {
      key: "plan-a",
      missing_count: 4,
      certificate_count: 0,
    })
    expect(progressed.tripped).toBe(false)
    expect(progressed.state.stagnant_observations).toBe(1)

    const certified = SessionPrompt.observeMaterializationLivelock(progressed.state, {
      key: "plan-a",
      missing_count: 4,
      certificate_count: 1,
    })
    expect(certified.tripped).toBe(false)
    expect(certified.state.stagnant_observations).toBe(1)
  })

  test("keeps lookup tools available during the soft reminder grace window", () => {
    const tools: Record<string, unknown> = {
      read: {},
      grep: {},
      edit: {},
      coq_session: {},
      checkpoint: {},
    }

    const gate = SessionPrompt.applyAcceptedPlanMaterializationToolGate(tools, 15)

    expect(gate).toMatchObject({ active: false, warning_limit: 12, hard_limit: 16 })
    expect(Object.keys(tools).sort()).toEqual(["checkpoint", "coq_session", "edit", "grep", "read"])
  })

  test("gates broad lookup without changing the provider tool schema", async () => {
    const executable = () => ({ execute: async () => ({ output: "original" }) })
    const tools: Record<string, unknown> = {
      read: executable(),
      grep: executable(),
      glob: executable(),
      lsp: executable(),
      coqtop: executable(),
      bash: executable(),
      task: executable(),
      proof_plan: executable(),
      edit: {},
      multiedit: {},
      write: {},
      apply_patch: {},
      coq_session: {},
      petanque: {},
      checkpoint: {},
      coqc: {},
    }

    const gate = SessionPrompt.applyAcceptedPlanMaterializationToolGate(tools, 16)

    expect(gate.active).toBe(true)
    expect(gate.blocked_tools).toEqual(expect.arrayContaining([
      "read",
      "grep",
      "glob",
      "lsp",
      "coqtop",
      "bash",
      "task",
      "proof_plan",
    ]))
    expect(Object.keys(tools).sort()).toEqual([
      "apply_patch",
      "bash",
      "checkpoint",
      "coq_session",
      "coqc",
      "edit",
      "glob",
      "grep",
      "lsp",
      "multiedit",
      "petanque",
      "proof_plan",
      "read",
      "task",
      "coqtop",
      "write",
    ].sort())
    const blocked = await (tools.read as { execute: () => Promise<{ output: string }> }).execute()
    expect(blocked.output).toContain("accepted_plan_materialization_gate")
    expect(gate.removed_tools).toEqual([])
  })

  test("does not let invalid lookup or validation reset the passive lookup streak", () => {
    const targetFile = "/tmp/workspace/Lemma4.v"
    const messages = [
      {
        parts: [
          {
            type: "tool",
            tool: "read",
            state: { status: "completed", input: { filePath: "/tmp/workspace/prosa/example.v" } },
          },
          {
            type: "tool",
            tool: "invalid",
            state: {
              status: "completed",
              input: { tool: "read", error: "Model tried to call unavailable tool 'read'." },
            },
          },
          {
            type: "tool",
            tool: "coqc",
            state: { status: "completed", input: { filePath: targetFile } },
          },
          {
            type: "tool",
            tool: "checkpoint",
            state: { status: "completed", input: { filePath: targetFile } },
          },
        ],
      },
    ] as unknown as MessageV2.WithParts[]

    expect(SessionPrompt.acceptedPlanMaterializationLookupStreakForTest(messages, targetFile)).toBe(1)
  })

  test("resets the passive lookup streak only after an active proof attempt", () => {
    const targetFile = "/tmp/workspace/Lemma4.v"
    const messages = [
      {
        parts: [
          {
            type: "tool",
            tool: "read",
            state: { status: "completed", input: { filePath: "/tmp/workspace/prosa/example.v" } },
          },
          {
            type: "tool",
            tool: "invalid",
            state: { status: "completed", input: { tool: "read", error: "unavailable" } },
          },
          {
            type: "tool",
            tool: "coq_session",
            state: { status: "completed", input: { op: "step", tactic: "intros." } },
          },
        ],
      },
    ] as unknown as MessageV2.WithParts[]

    expect(SessionPrompt.acceptedPlanMaterializationLookupStreakForTest(messages, targetFile)).toBe(0)
  })
})

describe("session.prompt proof cache projection", () => {
  test("enables compact lemma history by default without changing ordinary agents", async () => {
    await using tmp = await tmpdir()
    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const previous = process.env.OPENCODE_CACHE_PROJECT_TOOL_OUTPUTS
        process.env.OPENCODE_CACHE_PROJECT_TOOL_OUTPUTS = ""
        try {
          expect(SessionPrompt.cacheProjectionOptions({ name: "lemma" } as any)).toMatchObject({
            enabled: true,
            maxToolOutputChars: 2_000,
            maxProofToolOutputChars: 4_000,
            maxEditToolOutputChars: 1_000,
            maxEditToolInputChars: 1_000,
            maxAssistantTextChars: 4_000,
            maxReasoningChars: 2_000,
          })
          expect(SessionPrompt.cacheProjectionOptions({ name: "build" } as any)).toEqual({ enabled: false })
        } finally {
          if (previous === undefined) delete process.env.OPENCODE_CACHE_PROJECT_TOOL_OUTPUTS
          else process.env.OPENCODE_CACHE_PROJECT_TOOL_OUTPUTS = previous
        }
      },
    })
  })
})

describe("session.prompt missing file", () => {
  test("auto-binds Coq target files named in benchmark prompts", async () => {
    await using tmp = await tmpdir({
      git: true,
      init: async (dir) => {
        await Bun.write(path.join(dir, "Lemma3.v"), "Lemma demo : True. Proof. exact I. Qed.\n")
      },
    })

    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const session = await Session.create({})

        await SessionPrompt.prompt({
          sessionID: session.id,
          agent: "prover",
          noReply: true,
          parts: [
            {
              type: "text",
              text: "The target file is `Lemma3.v`. The theorem to prove is `demo`. Validate with `coqc Lemma3.v`.",
            },
          ],
        })

        const binding = SessionProof.get(session.id)
        expect(binding?.file).toBe(path.join(tmp.path, "Lemma3.v"))

        await Session.remove(session.id)
        SessionProof.clear(session.id)
      },
    })
  })

  test("prefers the explicit proof target over an attached placeholder file", async () => {
    await using tmp = await tmpdir({
      git: true,
      init: async (dir) => {
        await Bun.write(path.join(dir, "Lemma4.v"), "Lemma demo : True. Proof. exact I. Qed.\n")
        await Bun.write(path.join(dir, "DO_NOT_CREATE.v"), "From mathcomp Require Import all_ssreflect.\n")
      },
    })

    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const session = await Session.create({})
        const placeholder = path.join(tmp.path, "DO_NOT_CREATE.v")

        await SessionPrompt.prompt({
          sessionID: session.id,
          agent: "prover",
          noReply: true,
          parts: [
            {
              type: "file",
              filename: "DO_NOT_CREATE.v",
              mime: "text/plain",
              url: `file://${placeholder}`,
            },
            {
              type: "text",
              text: "The target file is `Lemma4.v`, the theorem is `demo`. Validate with `coqc Lemma4.v`.",
            },
          ],
        })

        expect(SessionProof.get(session.id)?.file).toBe(path.join(tmp.path, "Lemma4.v"))
        await Session.remove(session.id)
        SessionProof.clear(session.id)
      },
    })
  })

  test("repairs a persisted automatic placeholder binding on continuation", async () => {
    await using tmp = await tmpdir({
      git: true,
      init: async (dir) => {
        await Bun.write(path.join(dir, "Lemma4.v"), "Lemma demo : True. Proof. exact I. Qed.\n")
        await Bun.write(path.join(dir, "DO_NOT_CREATE.v"), "From mathcomp Require Import all_ssreflect.\n")
      },
    })

    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const session = await Session.create({})
        SessionProof.set(
          session.id,
          path.join(tmp.path, "DO_NOT_CREATE.v"),
          { line: 0, character: 0 },
          "auto",
        )

        await SessionPrompt.prompt({
          sessionID: session.id,
          agent: "prover",
          noReply: true,
          parts: [
            {
              type: "text",
              text: "The target file is `Lemma4.v`, the theorem is `demo`. Validate with `coqc Lemma4.v`.",
            },
          ],
        })

        expect(SessionProof.get(session.id)?.file).toBe(path.join(tmp.path, "Lemma4.v"))
        await Session.remove(session.id)
        SessionProof.clear(session.id)
      },
    })
  })

  test("does not fail the prompt when a file part is missing", async () => {
    await using tmp = await tmpdir({
      git: true,
      config: {
        agent: {
          build: {
            model: "openai/gpt-5.2",
          },
        },
      },
    })

    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const session = await Session.create({})

        const missing = path.join(tmp.path, "does-not-exist.ts")
        const msg = await SessionPrompt.prompt({
          sessionID: session.id,
          agent: "build",
          noReply: true,
          parts: [
            { type: "text", text: "please review @does-not-exist.ts" },
            {
              type: "file",
              mime: "text/plain",
              url: `file://${missing}`,
              filename: "does-not-exist.ts",
            },
          ],
        })

        if (msg.info.role !== "user") throw new Error("expected user message")

        const hasFailure = msg.parts.some(
          (part) => part.type === "text" && part.synthetic && part.text.includes("Read tool failed to read"),
        )
        expect(hasFailure).toBe(true)

        await Session.remove(session.id)
      },
    })
  })

  test("keeps stored part order stable when file resolution is async", async () => {
    await using tmp = await tmpdir({
      git: true,
      config: {
        agent: {
          build: {
            model: "openai/gpt-5.2",
          },
        },
      },
    })

    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const session = await Session.create({})

        const missing = path.join(tmp.path, "still-missing.ts")
        const msg = await SessionPrompt.prompt({
          sessionID: session.id,
          agent: "build",
          noReply: true,
          parts: [
            {
              type: "file",
              mime: "text/plain",
              url: `file://${missing}`,
              filename: "still-missing.ts",
            },
            { type: "text", text: "after-file" },
          ],
        })

        if (msg.info.role !== "user") throw new Error("expected user message")

        const stored = await MessageV2.get({
          sessionID: session.id,
          messageID: msg.info.id,
        })
        const text = stored.parts.filter((part) => part.type === "text").map((part) => part.text)

        expect(text[0]?.startsWith("Called the Read tool with the following input:")).toBe(true)
        expect(text[1]?.includes("Read tool failed to read")).toBe(true)
        expect(text[2]).toBe("after-file")

        await Session.remove(session.id)
      },
    })
  })
})

describe("session.prompt special characters", () => {
  test("handles filenames with # character", async () => {
    await using tmp = await tmpdir({
      git: true,
      init: async (dir) => {
        await Bun.write(path.join(dir, "file#name.txt"), "special content\n")
      },
    })

    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const session = await Session.create({})
        const template = "Read @file#name.txt"
        const parts = await SessionPrompt.resolvePromptParts(template)
        const fileParts = parts.filter((part) => part.type === "file")

        expect(fileParts.length).toBe(1)
        expect(fileParts[0].filename).toBe("file#name.txt")
        expect(fileParts[0].url).toContain("%23")

        const decodedPath = fileURLToPath(fileParts[0].url)
        expect(decodedPath).toBe(path.join(tmp.path, "file#name.txt"))

        const message = await SessionPrompt.prompt({
          sessionID: session.id,
          parts,
          noReply: true,
        })
        const stored = await MessageV2.get({ sessionID: session.id, messageID: message.info.id })
        const textParts = stored.parts.filter((part) => part.type === "text")
        const hasContent = textParts.some((part) => part.text.includes("special content"))
        expect(hasContent).toBe(true)

        await Session.remove(session.id)
      },
    })
  })
})

describe("session.prompt agent variant", () => {
  test("applies agent variant only when using agent model", async () => {
    const prev = process.env.OPENAI_API_KEY
    process.env.OPENAI_API_KEY = "test-openai-key"

    try {
      await using tmp = await tmpdir({
        git: true,
        config: {
          agent: {
            build: {
              model: "openai/gpt-5.2",
              variant: "xhigh",
            },
          },
        },
      })

      await Instance.provide({
        directory: tmp.path,
        fn: async () => {
          const session = await Session.create({})

          const other = await SessionPrompt.prompt({
            sessionID: session.id,
            agent: "build",
            model: { providerID: "opencode", modelID: "kimi-k2.5-free" },
            noReply: true,
            parts: [{ type: "text", text: "hello" }],
          })
          if (other.info.role !== "user") throw new Error("expected user message")
          expect(other.info.variant).toBeUndefined()

          const match = await SessionPrompt.prompt({
            sessionID: session.id,
            agent: "build",
            noReply: true,
            parts: [{ type: "text", text: "hello again" }],
          })
          if (match.info.role !== "user") throw new Error("expected user message")
          expect(match.info.model).toEqual({ providerID: "openai", modelID: "gpt-5.2" })
          expect(match.info.variant).toBe("xhigh")

          const override = await SessionPrompt.prompt({
            sessionID: session.id,
            agent: "build",
            noReply: true,
            variant: "high",
            parts: [{ type: "text", text: "hello third" }],
          })
          if (override.info.role !== "user") throw new Error("expected user message")
          expect(override.info.variant).toBe("high")

          await Session.remove(session.id)
        },
      })
    } finally {
      if (prev === undefined) delete process.env.OPENAI_API_KEY
      else process.env.OPENAI_API_KEY = prev
    }
  })
})
