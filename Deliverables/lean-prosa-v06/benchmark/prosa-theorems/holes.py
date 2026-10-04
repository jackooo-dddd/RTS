"""Locate a theorem's proof in a Lean source file and replace it by `sorry` (shared by prepare.py and check.py).

A declaration starts at the line `theorem <name>` (optionally indented, `private`/`protected`, with attributes) and
ends before the next line, at the same or a smaller indentation, that starts a Lean command (`theorem`, `def`,
`end`, `namespace`, `/--`, `@[`, ...).  Its proof is everything after the first `:=` outside brackets, comments
and strings.  Blank and comment-only lines just before the next command stay outside the proof.
"""
import re

COMMAND = re.compile(
    r"(?:@\[|/--|/-!|#|(?:private|protected|noncomputable|partial|unsafe|scoped|local|theorem|lemma|def|abbrev|"
    r"instance|structure|class|inductive|namespace|section|end|open|variable|universe|set_option|attribute|example|"
    r"macro|macro_rules|syntax|notation|infix|infixl|infixr|prefix|postfix|mutual|export|omit|include|elab|opaque|"
    r"axiom|initialize|alias|deriving)\b)")
OPEN, CLOSE = "([{⦃⟨", ")]}⦄⟩"


def _indent(line):
    return len(line) - len(line.lstrip(" \t"))


def find(text, name):
    """(decl_start, proof_start, proof_end) character offsets of theorem `name` (its last name component)."""
    lines = text.split("\n")
    pat = re.compile(r"^([ \t]*)(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:theorem|lemma) "
                     + re.escape(name) + r"(?![\w'.])")
    hits = [i for i, l in enumerate(lines) if pat.match(l)]
    if len(hits) != 1:
        raise ValueError(f"theorem {name}: found {len(hits)} declarations")
    i0 = hits[0]
    ind = _indent(lines[i0])
    j = i0 + 1
    while j < len(lines):
        l = lines[j]
        if l.strip() and _indent(l) <= ind and COMMAND.match(l.strip()):
            break
        j += 1
    # keep trailing blank / comment-only lines (they belong to what follows)
    k = j
    while k - 1 > i0 and (not lines[k - 1].strip() or lines[k - 1].lstrip().startswith("--")):
        k -= 1
    offs = [0]
    for l in lines:
        offs.append(offs[-1] + len(l) + 1)
    start, end = offs[i0], offs[k] - 1          # end: the newline after the last proof line
    # first `:=` at bracket depth 0, skipping comments and strings
    s, depth, p = text, 0, start
    while p < end:
        c = s[p]
        if s.startswith("--", p):
            p = s.find("\n", p); p = end if p < 0 else p; continue
        if s.startswith("/-", p):
            d = 1; p += 2
            while p < end and d:
                if s.startswith("/-", p): d += 1; p += 2
                elif s.startswith("-/", p): d -= 1; p += 2
                else: p += 1
            continue
        if c == '"':
            p += 1
            while p < end and s[p] != '"':
                p += 2 if s[p] == "\\" else 1
            p += 1; continue
        if c in OPEN: depth += 1
        elif c in CLOSE: depth -= 1
        elif depth == 0 and s.startswith(":=", p):
            return start, p, end
        p += 1
    raise ValueError(f"theorem {name}: no top-level `:=`")


def indent_of(text, decl_start):
    return _indent(text[decl_start:text.find("\n", decl_start)])


def statement(text, name):
    start, proof, _ = find(text, name)
    return text[start:proof].rstrip()


def proof(text, name):
    _, p, end = find(text, name)
    return text[p + 2:end]


def hole(text, name):
    """`text` with the proof of `name` replaced by `by sorry` (everything else unchanged)."""
    start, p, end = find(text, name)
    return text[:p] + ":= by\n" + " " * (indent_of(text, start) + 2) + "sorry" + text[end:]
