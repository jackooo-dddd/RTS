import { describe, expect, test } from "bun:test"
import { runProcess } from "../../src/util/bounded-process"

describe("bounded-process", () => {
  test("runProcess kills a timed-out process group", async () => {
    const result = await runProcess(["sh", "-c", "sleep 5"], process.cwd(), { timeoutMs: 50 })
    expect(result.timedOut).toBe(true)
    expect(result.exit).not.toBe(0)
  })

  test("runProcess caps combined subprocess output", async () => {
    const result = await runProcess(
      ["sh", "-c", "head -c 65536 /dev/zero | tr '\\0' x"],
      process.cwd(),
      { timeoutMs: 5_000, maxOutputBytes: 1024 },
    )
    expect(result.outputLimitExceeded).toBe(true)
    expect(Buffer.byteLength(result.stdout) + Buffer.byteLength(result.stderr)).toBeLessThanOrEqual(1024)
  })
})
