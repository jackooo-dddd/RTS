import { afterEach, beforeEach, describe, expect, test } from "bun:test"
import path from "path"
import { Instance } from "../../src/project/instance"
import { CoqAstAudit } from "../../src/tool/coq-ast-audit"
import { tmpdir } from "../fixture/fixture"

const ENV_KEYS = [
  "OPENCODE_COQ_AST_AUDIT",
  "OPENCODE_COQ_AST_FCC",
  "OPENCODE_COQ_AST_TRUSTED_REQUIRE_ROOTS",
] as const

describe("coq AST audit", () => {
  const previous = new Map<string, string | undefined>()

  beforeEach(() => {
    for (const key of ENV_KEYS) previous.set(key, process.env[key])
    process.env.OPENCODE_COQ_AST_AUDIT = "required"
  })

  afterEach(() => {
    for (const key of ENV_KEYS) {
      const value = previous.get(key)
      if (value === undefined) delete process.env[key]
      else process.env[key] = value
    }
    previous.clear()
  })

  test("derives exact allowlist keys only from trusted logical roots", () => {
    const records = [
      {
        phase: "VernacSynterp",
        vernac_kind: "VernacRequire",
        require: { from: "mathcomp", modules: [{ name: "all_ssreflect" }] },
      },
      {
        phase: "VernacSynterp",
        vernac_kind: "VernacRequire",
        require: { from: null, modules: [{ name: "prosa.analysis.facts" }, { name: "Coq.Init.Nat" }] },
      },
    ]
    expect(CoqAstAudit.trustedRequireKeys(records, new Set(["mathcomp", "prosa"]))).toEqual([
      "mathcomp::all_ssreflect",
      "prosa.analysis.facts",
    ])
  })

  test("accepts an ordinary final Qed against an admitted baseline", async () => {
    await using tmp = await tmpdir()
    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const file = path.join(tmp.path, "demo.v")
        const result = await CoqAstAudit.run({
          file,
          theorem: "demo",
          baselineSource: "Lemma demo : True.\nAdmitted.\n",
          candidateSource: "Lemma demo : True.\nProof. exact I. Qed.\n",
          stage: "final",
        })
        expect(result.status).toBe("accepted")
        expect(result.reasons).toEqual([])
      },
    })
  }, 30_000)

  test("rejects a proof-body side effect even when the file can be elaborated", async () => {
    await using tmp = await tmpdir()
    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const file = path.join(tmp.path, "demo.v")
        const result = await CoqAstAudit.run({
          file,
          theorem: "demo",
          baselineSource: "Lemma demo : True.\nAdmitted.\n",
          candidateSource: [
            "Lemma demo : True.",
            "Proof.",
            "  Axiom cheat : True.",
            "  exact cheat.",
            "Qed.",
            "",
          ].join("\n"),
          stage: "final",
        })
        expect(result.status).toBe("rejected")
        expect(result.reasons.map((reason) => reason.code)).toContain("PROOF_SIDE_EFFECT")
      },
    })
  }, 30_000)

  test("allows exact imports under trusted roots and rejects other additions", async () => {
    await using tmp = await tmpdir()
    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const file = path.join(tmp.path, "demo.v")
        const baselineSource = "Lemma demo : True.\nAdmitted.\n"
        const trusted = await CoqAstAudit.run({
          file,
          theorem: "demo",
          baselineSource,
          candidateSource: "From mathcomp Require Import all_ssreflect.\nLemma demo : True.\nProof. exact I. Qed.\n",
          stage: "final",
        })
        expect(trusted.status).toBe("accepted")
        expect(trusted.allowed_additions).toHaveLength(1)

        const untrusted = await CoqAstAudit.run({
          file,
          theorem: "demo",
          baselineSource,
          candidateSource: "Require Import Coq.Init.Nat.\nLemma demo : True.\nProof. exact I. Qed.\n",
          stage: "final",
        })
        expect(untrusted.status).toBe("rejected")
        expect(untrusted.reasons.some((reason) => reason.code.startsWith("EXTERIOR_"))).toBe(true)
      },
    })
  }, 30_000)

  test("fails closed in required mode when tooling is unavailable", async () => {
    await using tmp = await tmpdir()
    process.env.OPENCODE_COQ_AST_FCC = path.join(tmp.path, "missing-fcc")
    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        const result = await CoqAstAudit.run({
          file: path.join(tmp.path, "demo.v"),
          theorem: "demo",
          baselineSource: "Lemma demo : True.\nAdmitted.\n",
          candidateSource: "Lemma demo : True.\nProof. exact I. Qed.\n",
          stage: "final",
        })
        expect(result.status).toBe("error")
        expect(result.reasons[0]?.code).toBe("AST_AUDIT_TOOLING_UNAVAILABLE")
      },
    })
  })
})
