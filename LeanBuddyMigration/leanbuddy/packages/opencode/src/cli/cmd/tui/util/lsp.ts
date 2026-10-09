import type { LspStatus } from "@opencode-ai/sdk/v2"
import path from "path"

export type LeanStatus = {
  /** Files with ranges still being elaborated by the Lean server (`$/lean/fileProgress`). */
  progress: {
    path: string
    count: number
  }[]
}

export type RichLspStatus = LspStatus & {
  lean?: LeanStatus
}

export function pickLsp(list: RichLspStatus[], dir: string) {
  const lean = list.filter((item) => item.lean)
  if (lean.length <= 1) return list

  const here = path.resolve(dir)
  const pick = lean
    .map((item) => ({
      item,
      root: path.resolve(here, item.root || "."),
      depth: item.root.split("/").filter(Boolean).length,
    }))
    .toSorted((a, b) => {
      const ax = a.root === here ? 1 : 0
      const bx = b.root === here ? 1 : 0
      if (ax !== bx) return bx - ax
      if (a.depth !== b.depth) return a.depth - b.depth
      return a.item.root.localeCompare(b.item.root)
    })[0]?.item

  if (!pick) return list
  return list.filter((item) => !item.lean || item === pick)
}

function join(list: string[], total: number) {
  const text = list.join(", ")
  const extra = total - list.length
  if (extra <= 0) return text
  return `${text}, +${extra} more`
}

export function leanProgress(input: LeanStatus) {
  const busy = input.progress.filter((item) => item.count > 0)
  if (busy.length === 0) return
  return `Processing ${join(
    busy.slice(0, 2).map((item) => `${item.path} (${item.count})`),
    busy.length,
  )}`
}
