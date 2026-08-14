#!/usr/bin/env python3
"""Turn Lean inductive declarations into inference rules.

The rules on the generated page used to be hand-typed, which is precisely the
drift hazard the rest of this directory exists to eliminate: a rule that no
longer matches `Machine.lean` would look authoritative and be wrong.  Here the
constructors are **parsed** from the source, split into premises and conclusion
at top-level arrows, and rendered.

Two outputs:

* `rules.tex` — mathpartir, ready to `\\input` into a paper.
* an HTML fragment — the same rules, rendered by KaTeX in the browser.

Only the *notation* is a transcription (the table below).  The *content* —
which premises a rule has, and what its conclusion is — comes from the parse, so
adding a premise in Lean adds it here.  Every rule is displayed next to the Lean
it came from, so the notation map is checkable too.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

# ---------------------------------------------------------------- parsing

OPEN, CLOSE = "([{⟨", ")]}⟩"


def split_top(text: str, sep: str = "→") -> list[str]:
    """Split on `sep`, ignoring occurrences nested inside brackets."""
    out, depth, cur = [], 0, ""
    for ch in text:
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


@dataclass
class Rule:
    name: str
    binders: str
    premises: list[str]
    conclusion: str
    doc: str
    source: str


def parse_inductive(text: str, name: str) -> list[Rule]:
    """Extract the constructors of `inductive name` from `text`."""
    m = re.search(rf"^inductive\s+{re.escape(name)}\b.*?\bwhere\s*$", text, re.M)
    if not m:
        raise SystemExit(f"inductive {name} not found")
    lines = text[m.end():].split("\n")
    # the body runs until a line that is not indented and not blank
    body: list[str] = []
    for line in lines:
        if line.strip() and not line[0].isspace():
            break
        body.append(line)

    rules: list[Rule] = []
    cur: list[str] = []
    doc: list[str] = []
    pending_doc: list[str] = []

    def flush():
        if not cur:
            return
        src = "\n".join(cur).rstrip()
        head = "\n".join(cur)
        cm = re.match(r"\s*\|\s*(\w+)\s*(.*)", head, re.S)
        if not cm:
            return
        cname, tail = cm.group(1), cm.group(2)
        # the binders end at the first `:` outside any bracket — `{c : Config α}`
        # contains one, so a plain split on the first colon is wrong.
        depth, cut = 0, None
        for i, ch in enumerate(tail):
            if ch in OPEN:
                depth += 1
            elif ch in CLOSE:
                depth -= 1
            elif ch == ":" and depth == 0:
                cut = i
                break
        if cut is None:
            return
        binders, rest = tail[:cut].strip(), tail[cut + 1:]
        parts = split_top(" ".join(rest.split()))
        rules.append(Rule(cname, binders, parts[:-1], parts[-1],
                          " ".join(doc).strip(), src))

    in_doc = False
    for line in body:
        st = line.strip()
        if st.startswith("/--"):
            in_doc = True
            pending_doc = [st[3:].strip()]
            if st.endswith("-/"):
                pending_doc = [st[3:-2].strip()]
                in_doc = False
            continue
        if in_doc:
            if st.endswith("-/"):
                pending_doc.append(st[:-2].strip())
                in_doc = False
            else:
                pending_doc.append(st)
            continue
        if st.startswith("|"):
            flush()
            cur, doc = [line], pending_doc
            pending_doc = []
        elif cur:
            cur.append(line)
    flush()
    return rules


# ---------------------------------------------------------------- notation

#: Lean surface syntax → LaTeX.  Applied longest-first, so more specific
#: patterns win.  This is the one transcribed part of the pipeline, which is
#: why every rule is shown beside the Lean it was parsed from.
NOTATION: list[tuple[str, str]] = [
    (r"Result\.vis\s+stepEv\s+(\w+)", r"\\vis{\\opstep}{\1}"),
    (r"Result\.vis\s+yieldEv\s+(\w+)", r"\\vis{\\opyield}{\1}"),
    (r"Result\.vis\s+forkEv\s+(\w+)", r"\\vis{\\opfork}{\1}"),
    (r"Result\.vis\s+endthreadEv\s+(\w+)", r"\\vis{\\opend}{\1}"),
    (r"Result\.vis\s+\(modifyEv\s+(\w+)\)\s+(\w+)", r"\\vis{\\opmod\\,\1}{\2}"),
    (r"c\.focus\s*=\s*some\s*\((.*?)\)$", r"\\focus(c) = \1"),
    (r"c\.focus\s*=\s*some\s*", r"\\focus(c) = "),
    (r"c\.setFocus\s*\((.*?)\)", r"c[\\focus \\mapsto \1]"),
    (r"c\.setFocus\s+(\w+)", r"c[\\focus \\mapsto \1]"),
    (r"\{\s*(.*?)\s+with\s+heap\s*:=\s*(\S+?)\s*\}", r"\1[\\heap \\mapsto \2]"),
    (r"\{\s*(.*?)\s+with\s+current\s*:=\s*(\S+?)\s*\}", r"\1[\\cur \\mapsto \2]"),
    (r"\(\s*(.*?)\s*\)\.Alive\s+(\w+)", r"\\alive(\1, \2)"),
    (r"c\.kill\.Alive\s+(\w+)", r"\\alive(\\killt(c), \1)"),
    (r"(\w+)\.Alive\s+(\w+)", r"\\alive(\1, \2)"),
    # record literals are rendered literally rather than simplified: `fork`
    # setting `current := c.current` is exactly the fact that it does not
    # switch threads, and hiding it would hide the point.
    # `fork`'s record sets `current` and `heap` to their own values, so the
    # only real update is `threads`.  Rendering it as a single field update is
    # faithful, not a simplification -- and that fork does not switch threads is
    # carried by the rule's note, which comes from the Lean docstring.
    (r"\{\s*threads\s*:=\s*(.*?),\s*current\s*:=\s*c\.current,\s*heap\s*:=\s*c\.heap\s*\}",
     r"c[\\threads \\mapsto \1]"),
    (r"Step\s+(\w+)\s+(\w+)$", r"\1 \\stepto \2"),
    (r"Step\s+(\w+)\s+", r"\1 \\stepto "),
    (r"Reaches\s+(\S+)\s+(\S+)$", r"\1 \\stepsto \2"),
    (r"Reaches\s+(\S+)\s+", r"\1 \\stepsto "),
    (r"c\.threads", r"\\threads(c)"),
    (r"c\.current", r"\\cur(c)"),
    (r"c\.heap", r"\\heap(c)"),
    (r"c\.kill", r"\\killt(c)"),
    (r"PUnit\.unit", r"()"),
    (r"ConcE\.Tags\.cur", r"\\tagcur"),
    (r"ConcE\.Tags\.new", r"\\tagnew"),
    (r"\.alive\s+", r"\\alivet\\,"),
    (r"\.set\s+", r"\\,\\setidx\\,"),
    (r"\bsome\b", ""),
    (r"₁", r"_1"), (r"₂", r"_2"), (r"₃", r"_3"), (r"₄", r"_4"),
    (r"σ'", r"\\sigma'"),
    (r"σ", r"\\sigma"),
    (r"\balpha\b", r"\\alpha"),
    (r"⟶", r"\\stepto"),
    (r"≠", r"\\neq"),
    (r"∀", r"\\forall"),
    (r"∃", r"\\exists"),
    (r"∧", r"\\wedge"),
    (r"∨", r"\\vee"),
    (r"¬", r"\\neg"),
    (r"↦", r"\\mapsto"),
    (r"\+\+", r"\\dplus"),
]

PREAMBLE = r"""% Generated by AeneasIris/Semantics/docs/rules.py — do not edit by hand.
% Requires: \usepackage{mathpartir}
\providecommand{\focus}{\mathrm{focus}}
\providecommand{\heap}{\mathrm{heap}}
\providecommand{\cur}{\mathrm{cur}}
\providecommand{\threads}{\mathrm{threads}}
% \kill is already a LaTeX command (tabbing), and \providecommand would
% silently decline to redefine it, so this one is \killt.
\providecommand{\killt}{\mathrm{kill}}
\providecommand{\alive}{\mathrm{alive}}
\providecommand{\alivet}{\mathsf{alive}}
\providecommand{\setidx}{\mathrm{set}}
\providecommand{\dplus}{\mathbin{+\!\!+}}
\providecommand{\stepto}{\longrightarrow}
\providecommand{\stepsto}{\longrightarrow^{*}}
\providecommand{\opstep}{\mathsf{step}}
\providecommand{\opyield}{\mathsf{yield}}
\providecommand{\opfork}{\mathsf{fork}}
\providecommand{\opend}{\mathsf{endthread}}
\providecommand{\opmod}{\mathsf{modify}}
\providecommand{\tagcur}{\mathsf{cur}}
\providecommand{\tagnew}{\mathsf{new}}
\providecommand{\vis}[2]{\mathsf{vis}\;#1\;#2}
"""

#: The same macros, for KaTeX, which has no \providecommand.
KATEX_MACROS = {
    "\\focus": "\\mathrm{focus}", "\\heap": "\\mathrm{heap}",
    "\\cur": "\\mathrm{cur}", "\\threads": "\\mathrm{threads}",
    "\\killt": "\\mathrm{kill}", "\\alive": "\\mathrm{alive}",
    "\\alivet": "\\mathsf{alive}", "\\setidx": "\\mathrm{set}",
    "\\dplus": "\\mathbin{+\\!\\!+}", "\\stepto": "\\longrightarrow", "\\stepsto": "\\longrightarrow^{*}",
    "\\opstep": "\\mathsf{step}", "\\opyield": "\\mathsf{yield}",
    "\\opfork": "\\mathsf{fork}", "\\opend": "\\mathsf{endthread}",
    "\\opmod": "\\mathsf{modify}", "\\tagcur": "\\mathsf{cur}",
    "\\tagnew": "\\mathsf{new}", "\\vis": "\\mathsf{vis}\\;#1\\;#2",
}


def to_latex(s: str) -> str:
    out = " ".join(s.split())
    for pat, rep in NOTATION:
        out = re.sub(pat, rep, out)
    return " ".join(out.split())


# ---------------------------------------------------------------- emitting

def strip_outer(s: str) -> str:
    """Drop one redundant enclosing paren pair, if it wraps the whole term."""
    t = s.strip()
    if not (t.startswith("(") and t.endswith(")")):
        return t
    depth = 0
    for i, ch in enumerate(t):
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
            if depth == 0 and i != len(t) - 1:
                return t
    return t[1:-1].strip()


def strip_arrow_parens(s: str) -> str:
    r"""`c \stepto (X)` reads better as `c \stepto X` when X is balanced."""
    m = re.match(r"^(.*?\\stepto\s*)\((.*)\)$", s.strip(), re.S)
    if not m:
        return s
    inner, depth = m.group(2), 0
    for ch in inner:
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
            if depth < 0:
                return s
    return m.group(1) + inner if depth == 0 else s


def rule_tex(r: Rule) -> str:
    prem = " \\\\ ".join(to_latex(p) for p in r.premises) or "\\ "
    return ("\\inferrule*[left=\\textsc{%s}]\n  {%s}\n  {%s}"
            % (r.name.replace("_", "\\_"), prem, strip_arrow_parens(strip_outer(to_latex(r.conclusion)))))


def rules_tex(groups: list[tuple[str, str, list[Rule]]]) -> str:
    body = [PREAMBLE]
    for title, note, rs in groups:
        body.append(f"\n% ---- {title}\n% {note}\n")
        body.append("\\begin{mathpar}\n"
                    + "\n\n".join(rule_tex(r) for r in rs)
                    + "\n\\end{mathpar}\n")
    return "".join(body)


# ---------------------------------------------------------------- checking

def check_tex(tex: str) -> tuple[bool, str]:
    r"""Compile the rules with `tectonic`, if it is installed.

    `\kill` is already a LaTeX command and `\providecommand` declines to
    redefine it, which produced a file that *looked* fine and would not build.
    Nothing about the notation table is self-checking, so the generator compiles
    its own output rather than trusting it.
    """
    import shutil, subprocess, tempfile, os
    exe = shutil.which("tectonic")
    if exe is None:
        return True, "skipped (tectonic not installed)"
    with tempfile.TemporaryDirectory() as d:
        (pathlib.Path(d) / "rules.tex").write_text(tex, encoding="utf-8")
        (pathlib.Path(d) / "t.tex").write_text(
            "\\documentclass{article}\n\\usepackage{amsmath,amssymb}\n"
            "\\usepackage{mathpartir}\n\\begin{document}\n"
            "\\input{rules.tex}\n\\end{document}\n", encoding="utf-8")
        r = subprocess.run([exe, "t.tex"], cwd=d, capture_output=True,
                           text=True, timeout=600)
        if r.returncode != 0:
            return False, r.stderr.strip().split("\n")[-1]
        if "Overfull" in r.stderr or "Underfull" in r.stderr:
            return True, "compiles, with box warnings"
        return True, "compiles cleanly"


import pathlib  # noqa: E402  (used by check_tex)
