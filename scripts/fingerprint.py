#!/usr/bin/env python3
"""Public-signature fingerprint for the statement-invariance gate.

Extracts every non-private declaration signature (keyword through the type,
i.e. up to the `:=`/`where`/`by` that starts the body), comment-stripped and
whitespace-normalized, from all .lean files under the given roots. Output is
sorted, so it is invariant under moving declarations between files.

Usage: python3 scripts/fingerprint.py [root ...] > fp.txt
Defaults to Laplace Laplace.lean Statements.lean Solutions.lean.
"""

import re
import sys
from pathlib import Path

DECL_KW = r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|opaque|axiom)"
# Declaration headers, possibly preceded by modifiers/attributes on the same line.
HEAD = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|protected\s+|scoped\s+)*" + DECL_KW + r"\b"
)
PRIVATE = re.compile(r"^(?:@\[[^\]]*\]\s*)*private\b")


def strip_comments(text: str) -> str:
    out = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth > 0:
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def body_start(sig: str) -> int:
    """Index where the proof/body begins (first top-level `:=` or `where` or
    trailing `by` after the type's colon). Conservative: scans for `:=` not
    inside brackets is hard; instead find the earliest of ` := `, `\nwhere`,
    ` where ` occurring at bracket depth 0."""
    depth = 0
    i = 0
    n = len(sig)
    while i < n:
        c = sig[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0:
            if sig.startswith(":=", i):
                return i
            if sig.startswith("where", i) and (i == 0 or not sig[i - 1].isalnum()):
                nxt = i + 5
                if nxt >= n or not (sig[nxt].isalnum() or sig[nxt] == "_"):
                    return i
        i += 1
    return n


def extract(path: Path):
    text = strip_comments(path.read_text())
    lines = text.splitlines()
    sigs = []
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if PRIVATE.match(stripped):
            i += 1
            continue
        if HEAD.match(stripped):
            # Gather until the next line that starts a new top-level construct
            # (non-indented non-continuation) — declarations here start at col 0
            # after attribute lines; body lines are indented or begin with `:=`.
            chunk = [stripped]
            j = i + 1
            while j < len(lines):
                nxt = lines[j]
                if nxt and not nxt[0].isspace():
                    break
                chunk.append(nxt.strip())
                j += 1
            sig = " ".join(chunk)
            sig = sig[: body_start(sig)]
            sig = re.sub(r"\s+", " ", sig).strip()
            if sig:
                sigs.append(sig)
            i = j
        else:
            i += 1
    return sigs


def main():
    roots = sys.argv[1:] or ["Laplace", "Laplace.lean", "Statements.lean", "Solutions.lean"]
    files = []
    for r in roots:
        p = Path(r)
        files.extend(sorted(p.rglob("*.lean")) if p.is_dir() else [p])
    allsigs = []
    for f in files:
        allsigs.extend(extract(f))
    for s in sorted(allsigs):
        print(s)


if __name__ == "__main__":
    main()
