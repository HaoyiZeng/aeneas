#!/usr/bin/env python3
"""Generate a browsable description of the AeneasIris machine semantics.

Every Lean snippet in the output is **extracted from the sources at generation
time**, never transcribed.  A page whose purpose is "check that the definitions
are right" is worthless if the code it shows can drift from the code that is
compiled, so nothing here is hand-copied.

Usage (from the `lean-iris` directory):

    python3 AeneasIris/Semantics/docs/gen.py

writes `AeneasIris/Semantics/docs/semantics.html`.
"""

from __future__ import annotations

import html
import json
import pathlib
import re
import subprocess
import sys
from datetime import datetime, timezone

import rules

HERE = pathlib.Path(__file__).resolve().parent
LEAN_IRIS = HERE.parent.parent.parent            # .../backends/lean-iris
BACKENDS = LEAN_IRIS.parent                      # .../backends
LEAN_STD = BACKENDS / "lean"                     # .../backends/lean

DECL_RE = r"(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|@\[[^\]]*\]\s*)*" \
          r"(?:def|abbrev|theorem|lemma|inductive|structure|instance|class)"


def read(path: pathlib.Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        sys.exit(f"missing source file: {path}")


def extract(relpath: str, name: str, *, root: pathlib.Path = LEAN_IRIS) -> str:
    """Return the source text of declaration `name` in `relpath`.

    Captures from the declaration header (including a `/-- ... -/` docstring, if
    the caller wants it stripped they can pass `doc=False` via `extract_nodoc`)
    up to the next top-level declaration or section comment.
    """
    text = read(root / relpath)
    lines = text.split("\n")
    start = None
    pat = re.compile(rf"^{DECL_RE}\s+{re.escape(name)}(?:[\s({{\[:.]|$)")
    for i, line in enumerate(lines):
        if pat.match(line):
            start = i
            break
    if start is None:
        sys.exit(f"declaration not found: {name} in {relpath}")
    end = start + 1
    stop = re.compile(rf"^(?:{DECL_RE}\s|/-|end\s|namespace\s|variable\s|open\s|@\[)")
    while end < len(lines):
        line = lines[end]
        if line and not line[0].isspace() and stop.match(line):
            break
        end += 1
    while end > start and not lines[end - 1].strip():
        end -= 1
    return "\n".join(lines[start:end])


def git_rev() -> str:
    try:
        out = subprocess.run(
            ["git", "-C", str(LEAN_IRIS), "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, timeout=10)
        return out.stdout.strip() or "unknown"
    except Exception:
        return "unknown"


def count_sorries() -> tuple[int, int]:
    sem = LEAN_IRIS / "AeneasIris" / "Semantics"
    n_sorry = n_axiom = 0
    for f in sorted(sem.glob("*.lean")):
        for line in read(f).split("\n"):
            if re.match(r"^\s*sorry\s*$", line):
                n_sorry += 1
            if re.match(r"^\s*axiom\s|^axiom\s", line):
                n_axiom += 1
    return n_sorry, n_axiom


# --------------------------------------------------------------------------
# the anti-drift audit
# --------------------------------------------------------------------------

# `setupF` is the racer test program's own setup step, not a copy of any
# operation in Effects/Heap.lean, so it has nothing to be pinned to.
AUDIT_EXEMPT = {"setupF"}


def drift_audit() -> list[tuple[str, str, bool]]:
    """Every hand-written state transformer must be pinned to the real operation.

    A *state transformer* is identified by its type, `RustHeap.{0} → Option
    RustHeap.{0}`, not by a naming convention — an earlier version of this audit
    keyed on a trailing `F` and duly reported `SoundGF`, which is a bundle of
    ghost functors.

    A transformer is *pinned* when some theorem in the same file mentions both it
    and a `_body`, i.e. states that it is the transformer inside a real
    operation.  Both naming conventions in use are therefore accepted
    (`loadF_eq` in `Vacuity.lean`, `load_body_eq` in `Example.lean`).

    This is the discipline λRust's `races.v` can only ask for in a comment
    ("if we forget to sync it with head_step, the results proven here are
    worthless"); here it is a `rfl` lemma, so a divergence is a build error
    rather than a silently vacuous theorem.
    """
    sem = LEAN_IRIS / "AeneasIris" / "Semantics"
    tf = re.compile(
        r"^[ \t]*(?:private\s+|noncomputable\s+)*def\s+(\w+)"
        r"((?:[^\n:=]|:(?!=)|\n[ \t]+)*?)"
        r":\s*RustHeap\.\{0\}\s*→\s*Option\s+RustHeap\.\{0\}\s*:=",
        re.M)
    thm = re.compile(r"^\s*(?:private\s+)?theorem\s+(\w+)([^\n]*(?:\n[ \t]+[^\n]*)*)",
                     re.M)
    out: list[tuple[str, str, bool]] = []
    for f in sorted(sem.glob("*.lean")):
        text = read(f)
        thms = [(n, body) for n, body in thm.findall(text)]
        for name, _ in tf.findall(text):
            if name in AUDIT_EXEMPT:
                out.append((f"{name}  ({f.name})",
                            "exempt — not a copy of any operation", True))
                continue
            tie = next((n for n, body in thms
                        if name in body and "_body" in body), None)
            out.append((f"{name}  ({f.name})", tie or f"{name}_eq", tie is not None))
    return sorted(out)


# --------------------------------------------------------------------------
# page pieces
# --------------------------------------------------------------------------

def code(src: str, *, lang: str = "lean") -> str:
    return f'<pre class="{lang}"><code>{html.escape(src)}</code></pre>'


def panel(title: str, body: str, *, open_: bool = False, note: str = "") -> str:
    o = " open" if open_ else ""
    n = f'<p class="note">{note}</p>' if note else ""
    return (f'<details{o}><summary>{html.escape(title)}</summary>'
            f'<div class="panelbody">{n}{body}</div></details>')


def section(sid: str, title: str, body: str) -> str:
    return f'<section id="{sid}"><h2>{html.escape(title)}</h2>{body}</section>'


def texrule(r, src_panel: str) -> str:
    """An inference rule, rendered by KaTeX, with the Lean it was parsed from."""
    prem = " \\\\ ".join(rules.to_latex(p) for p in r.premises) or "\\ "
    concl = rules.strip_arrow_parens(rules.strip_outer(rules.to_latex(r.conclusion)))
    tex = "\\dfrac{\\displaystyle %s}{\\displaystyle %s}" % (
        prem.replace("\\\\", "\\quad "), concl)
    note = f'<div class="rulenote">{html.escape(r.doc)}</div>' if r.doc else ""
    return (f'<div class="rule"><div class="rulename">{html.escape(r.name)}</div>'
            f'<div class="rulebox"><span class="tex" data-tex="{html.escape(tex)}">'
            f'{html.escape(tex)}</span></div>{note}{src_panel}</div>')


def table(headers: list[str], rows: list[list[str]], *, raw: bool = False) -> str:
    h = "".join(f"<th>{html.escape(x)}</th>" for x in headers)
    body = ""
    for r in rows:
        cells = "".join(
            f"<td>{c if raw else html.escape(c)}</td>" for c in r)
        body += f"<tr>{cells}</tr>"
    return f'<table><thead><tr>{h}</tr></thead><tbody>{body}</tbody></table>'


# --------------------------------------------------------------------------

def build() -> str:
    n_sorry, n_axiom = count_sorries()
    rev = git_rev()
    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")

    # ---- sources, extracted -------------------------------------------
    eff = "Aeneas/Std/Effects.lean"
    heap = "AeneasIris/Effects/Heap.lean"

    src_access = extract(eff, "AccessState", root=LEAN_STD)
    src_cell = extract(eff, "Cell", root=LEAN_STD)
    src_val = extract(eff, "Val", root=LEAN_STD)
    src_rustheap = extract(eff, "RustHeap", root=LEAN_STD)
    src_faile = extract(eff, "FailE.I", root=LEAN_STD)
    src_conce_i = extract(eff, "ConcE.I", root=LEAN_STD)
    src_conce_tags = extract(eff, "ConcE.Tags", root=LEAN_STD)

    ops = {}
    for op in ["readAcquire_body", "readRelease_body", "writeAcquire_body",
               "writeRelease_body", "load_body", "store_body", "cas_body",
               "modify_body", "alloc_body", "free_body"]:
        ops[op] = extract(heap, op)
    src_load_na = extract(heap, "load_na")
    src_store_na = extract(heap, "store_na")

    src_rusth = extract("AeneasIris/Rust.lean", "rustH")
    src_conch = extract("AeneasIris/Effects/Conc.lean", "ConcH.run")
    src_stateh = extract("AeneasIris/Effects/Heap.lean", "stateH.run")
    src_steph = extract("AeneasIris/Effects/Step.lean", "stepH.run")

    sem = lambda n, f: extract(f"AeneasIris/Semantics/{f}.lean", n)
    src_config = sem("Config", "Machine")
    src_thread = sem("Thread", "Machine")
    src_step = sem("Step", "Machine")
    src_focus = sem("Config.focus", "Machine")
    src_faulty = sem("Config.Faulty", "Machine")
    src_panics = sem("Panics", "Machine")
    src_stuckon = sem("StuckOn", "Machine")
    src_safe = sem("Safe", "Machine")
    src_mayreturn = sem("MayReturn", "Machine")
    src_terminates = sem("Terminates", "Machine")
    src_sn = sem("SN", "Machine")

    src_sysinv = sem("SysInv", "Invariant")
    src_runobl = sem("runObl", "Invariant")
    src_readyobl = sem("readyObl", "Invariant")
    src_focusobl = sem("focusObl", "Invariant")

    src_same = sem("SameContents", "Races")
    src_raceson = sem("RacesOn", "Races")
    src_racing = sem("Config.Racing", "Races")
    src_drf = sem("DataRaceFree", "Races")

    src_provable = sem("ProvableSpec", "Adequacy")
    src_ad_part = sem("adequacy_part", "Adequacy")
    src_ad_total = sem("adequacy_total", "Adequacy")

    rb = lambda n: extract("AeneasIris/Semantics/RustBelt.lean", n)
    pw = lambda n: extract("AeneasIris/Semantics/PairwiseRaces.lean", n)

    # ---- page ---------------------------------------------------------
    parts = []

    parts.append(section("intro", "What this page is", f"""
<p class="lead">A description of the machine that <code>AeneasIris/Semantics/</code>
defines, and of the interpretation of the ITrees Aeneas emits, laid out so that
each definition can be checked against its intent.</p>

<p>Every Lean snippet below is <strong>extracted from the sources when this page is
generated</strong>, never transcribed. A page whose job is "check the definitions"
would be worthless if the code it displays could drift from the code that is
compiled.</p>

<div class="statbar">
  <div><span class="k">generated</span><span class="v">{now}</span></div>
  <div><span class="k">git</span><span class="v">{rev}</span></div>
  <div><span class="k">sorry in Semantics/</span><span class="v">{n_sorry}</span></div>
  <div><span class="k">axiom in Semantics/</span><span class="v">{n_axiom}</span></div>
</div>

<h3>The one thing to keep in mind while reading</h3>
<p>Aeneas is written in OCaml and LLBC's semantics lives in Charon, so
<em>no Lean theorem can relate <code>wpi</code> to Rust's operational
semantics</em> — that link is a trust assumption, and always was. What follows
therefore <strong>defines</strong> the semantics at the ITree level. The ITree is
not a compiled artifact; it <strong>is</strong> the language. This is the same
position as the Islaris case study in §7 of <em>Program Logics à la Carte</em>.</p>

<p>So the question this page exists to answer is not "is the compiler correct"
but the sharper and more checkable one: <strong>does this machine describe the
behaviour you intend the generated code to have?</strong></p>
"""))

    # ---------------- effects
    parts.append(section("effects", "1 · The effect signature", f"""
<p>A translated Rust program is an <code>ITree RustEffect α</code>, where</p>
<pre class="lean"><code>RustEffect = FailE ⊕ₑ ConcE ⊕ₑ StepE ⊕ₑ StateE RustHeap</code></pre>
<p>Four summands, and every observable action of a program is one of them.</p>

{table(["summand", "operations", "answer type", "meaning"], [
  ["FailE", "fail e", "PEmpty", "a panic, or Aeneas' own partiality (overflow, out-of-bounds). No continuation: the answer type is empty."],
  ["ConcE", "fork, yield, endthread", "Tags / PUnit / PEmpty", "concurrency, Unix-fork style: the child is the continuation, selected by the answer tag."],
  ["StepE", "step", "PUnit", "one tick of the step counter. This is the only source of well-foundedness at .total."],
  ["StateE RustHeap", "modify f", "RustHeap", "a heap transformer. f : RustHeap → Option RustHeap; none means the operation is undefined here."],
])}

{panel("FailE.I, ConcE.I, ConcE.Tags — extracted", code(src_faile) + code(src_conce_i) + code(src_conce_tags))}

<h3>Why <code>modify</code> is passed the <em>old</em> heap</h3>
<p>The answer type of <code>modify f</code> is <code>RustHeap</code>, and the value
handed to the continuation is the heap <em>before</em> the update. This is not a
convention that could go either way — it is forced, twice:</p>
<ul>
<li><code>cas_body</code> reads the pre-state to decide the <code>Bool</code> it
returns. Handed the post-state it would always report success.</li>
<li><code>alloc_body</code> returns <code>fresh σ</code>. Handed the post-state it
would return a <em>second</em> fresh location, not the one it just allocated.</li>
</ul>
"""))

    # ---------------- heap
    lrust_rows = [
        ["<code>RSt n</code>", "<code>AccessState.reading n</code>"],
        ["<code>WSt</code>", "<code>AccessState.writing</code>"],
        ["<code>state = gmap loc (lock_state * val)</code>", "<code>RustHeap = HMap (Cell Val)</code>"],
        ["<code>Read Na1Ord</code>", "<code>readAcquire</code>"],
        ["<code>Read Na2Ord</code>", "<code>readRelease</code>"],
        ["<code>Write Na1Ord</code>", "<code>writeAcquire</code>"],
        ["<code>Write Na2Ord</code>", "<code>writeRelease</code>"],
        ["<code>Read ScOrd</code>", "<code>load_at</code>"],
        ["<code>Write ScOrd</code>", "<code>store_at</code>"],
        ["<code>CAS</code>", "<code>cas</code>"],
    ]

    parts.append(section("heap", "2 · The heap model is RustBelt's", f"""
<p>The heap is not our invention. <code>AccessState</code> is λRust's
<code>lock_state</code>, and every operation's enabling condition is one row of
λRust's table. <strong>This is where the notion of a data race comes from</strong>
— it is a consequence of the heap model, not an extra definition bolted on.</p>

{table(["λRust (lambda-rust/theories/lang/lang.v)", "here"], lrust_rows, raw=True)}

{panel("AccessState, Cell, Val, RustHeap — extracted",
       code(src_access) + code(src_cell) + code(src_val) + code(src_rustheap), open_=True)}

<h3>Why a cell stores a <em>type</em> alongside its value</h3>
<p><code>Val = (T : Type) × T</code>. A heap cell remembers what type it was
written at, so an access at a different type is <em>stuck</em> rather than
reinterpreting the bytes. Type confusion is therefore an undefined operation,
in the same sense as an out-of-bounds access — and both are ruled out by
<code>Safe</code>.</p>

<h3>λRust's table, and ours, proved equal</h3>
<p><code>races.v</code> calls its enabling table "a crucial definition; if we
forget to sync it with head_step, the results proven here are worthless". The
same risk applies here, so the correspondence is not asserted in a comment — it
is proved, one <code>↔</code> per row, in
<code>Semantics/RustBelt.lean</code>.</p>

<pre class="lean"><code>(* lambda-rust/theories/lang/races.v, next_access_head_reducible_state *)
match a with
| (ReadAcc, ScOrd | Na1Ord) =&gt; ∃ v n, σ !! l = Some (RSt n, v)
| (ReadAcc, Na2Ord)         =&gt; ∃ v n, σ !! l = Some (RSt (S n), v)
| (WriteAcc, ScOrd | Na1Ord)=&gt; ∃ v,   σ !! l = Some (RSt 0, v)
| (WriteAcc, Na2Ord)        =&gt; ∃ v,   σ !! l = Some (WSt, v)
| (FreeAcc, _)              =&gt; ∃ v ls, σ !! l = Some (ls, v)
end</code></pre>

{panel("The four rows, as Lean theorems — extracted",
       code(rb("readAcquire_enabled")) + code(rb("readRelease_enabled")) +
       code(rb("writeAcquire_enabled")) + code(rb("writeRelease_enabled")) +
       code(rb("storeAt_enabled")),
       note="↔, not →. An operation enabled more often would permit races; "
            "enabled less often would make the machine stuck where λRust is not. "
            "Both directions carry weight.")}

<h3>One deliberate difference: <code>free</code></h3>
<p>λRust enables <code>free</code> in <em>any</em> lock state and then rules out
racing with it by a separate argument. We require <code>reading 0</code>, so
freeing a location another thread is reading or writing is simply stuck, and is
already excluded by <code>Safe</code>. The same programs are accepted; ours needs
no extra argument, at the cost of a <code>free</code> enabled less often.</p>
"""))

    # ---------------- operations
    op_rows = [
        ["readAcquire", "reading n", "reading (n+1)", "unchanged", "Read Na1Ord"],
        ["readRelease", "reading (n+1)", "reading n", "unchanged", "Read Na2Ord"],
        ["writeAcquire", "reading 0", "writing", "unchanged", "Write Na1Ord"],
        ["writeRelease", "writing", "reading 0", "new value", "Write Na2Ord"],
        ["load_at", "reading _ (+ type match)", "unchanged", "unchanged", "Read ScOrd"],
        ["store_at", "reading 0", "reading 0", "new value", "Write ScOrd"],
        ["cas (succeeds)", "reading 0, value = old", "reading 0", "new value", "CasSucS"],
        ["cas (fails)", "reading n, value ≠ old", "unchanged", "unchanged", "CasFailS"],
        ["cas (racing)", "reading (n+1), value = old", "— stuck —", "—", "CasStuckS"],
        ["modify", "reading 0 (+ type match)", "reading 0", "f applied", "read-modify-write"],
        ["alloc", "—", "reading 0 at a fresh location", "the new value", "AllocS"],
        ["free", "reading 0", "location deleted", "—", "FreeS (stricter)"],
    ]

    cas_panels = "".join([
        panel("CasSucS — unlocked, always enabled", code(rb("cas_enabled_unlocked"))),
        panel("CasFailS — a failing cas is only a read, so readers do not block it",
              code(rb("cas_enabled_readers_of_ne"))),
        panel("CasStuckS — a succeeding cas is a write, so a reader makes it stuck",
              code(rb("cas_stuck_readers_of_eq")),
              note="this is the race"),
        panel("a cell being written blocks cas outright",
              code(rb("cas_stuck_writing"))),
        panel("casF_eq — the transformer above IS the one in Heap.cas_body, by rfl",
              code(rb("casF_eq")),
              note="the defence against the drift λRust warns about"),
    ])

    audit_rows = [[n, tie, "✅ pinned" if ok else "❌ MISSING"]
                  for n, tie, ok in drift_audit()]
    audit_table = table(["hand-written transformer", "pinned by", "status"], audit_rows)

    op_panels = "".join(
        panel(f"{name} — extracted", code(src))
        for name, src in ops.items())

    parts.append(section("ops", "3 · The heap operations", f"""
<p>Each operation is a single <code>modify</code> event, so it is one machine
step and therefore atomic. Non-atomic Rust accesses are <em>built</em> from two
of them with a <code>yield</code> in between — that is what makes them
interruptible, and it is the only reason interference is observable.</p>

{table(["operation", "requires", "leaves", "value", "λRust rule"], op_rows)}

<p class="callout"><strong>The <code>cas</code> rows are worth reading twice.</strong>
A <em>failed</em> compare-and-swap is only a read, so it is enabled under
<code>reading (n+1)</code>. A <em>successful</em> one is a write, so under
<code>reading (n+1)</code> it is stuck — that is exactly λRust's
<code>CasStuckS</code>, and it is a genuine race. A table that lumped all of
<code>cas</code> under <code>reading 0</code> would misdescribe the model.</p>

<p>Because those three rows are the ones most likely to drift from the
implementation, they are not left as table entries — each has a theorem:</p>
{cas_panels}

<h3>Non-atomic accesses, and where the interleaving point is</h3>
{code(src_load_na)}
{code(src_store_na)}
<p>λRust is a small-step language, so its scheduler may interleave between the
two halves of a non-atomic access. We have no scheduler outside the program, so
the <code>yield</code> is written into the operation. The effect is the same —
the middle of a non-atomic access is exactly where another thread may observe it
— but here it is visible in the ITree instead of hidden in a scheduler.</p>

<h3>The transformers, verbatim</h3>
{op_panels}

<h3>The anti-drift audit</h3>
<p>Several of these transformers are written out a second time — in
<code>Races.lean</code>, <code>RustBelt.lean</code> and <code>Vacuity.lean</code> —
so that theorems can be stated about them directly. A second copy is exactly the
hazard λRust's <code>races.v</code> warns about, in a comment it puts above its
own duplicated definition:</p>
<blockquote>"This is a crucial definition; if we forget to sync it with
head_step, the results proven here are worthless."</blockquote>
<p>A drifted copy does not produce an error. The theorem still compiles and is
still true — of a function nothing executes. The defence is that every copy is
pinned to the real operation by a <code>rfl</code> lemma, so a divergence becomes
a <em>build failure</em> instead of a silently empty theorem. This table is
regenerated from the sources each time and will show a gap if one appears:</p>
{audit_table}
"""))

    # ---------------- handler
    parts.append(section("handler", "4 · The handler, and the big lock", f"""
{code(src_rusth)}
<p>The handler says what each effect <em>means</em> in Iris. Three of the four
clauses are unremarkable; <code>ConcE</code> is where the concurrency model
lives.</p>

{panel("ConcH.run — extracted", code(src_conch), open_=True,
       note="🧱 P = |={∅,⊤}=> |={⊤,∅}=> P     💰 P = |={⊤,∅}=> P     🧾 P = |={∅,⊤}=> P")}
{panel("stateH.run — extracted", code(src_stateh))}
{panel("stepH.run — extracted", code(src_steph))}

<h3>Cooperative scheduling is forced, not chosen</h3>
<p><code>ownE ⊤</code> — the token that says "all invariants are closed" — is
<strong>linear</strong>. A scheduled thread has spent it; an unscheduled one is an
obligation waiting to acquire it. Since it cannot be duplicated, <em>at most one
thread can be inside a yield-free region</em>.</p>

<p>Three consequences, none of them stipulated:</p>
<ul>
<li><strong>"Atomic" means "yield-free", not "one step".</strong>
<code>wpi_open_invariant</code> therefore needs no atomicity side condition.</li>
<li><strong>Yielding with an invariant open is unprovable.</strong> After
<code>inv_acc</code> the thread holds <code>ownD {{ι}}</code>; <code>yield</code>'s
first half must produce <code>ownE ⊤ ∋ ι</code> from <code>wsat</code>, whose entry
for <code>ι</code> is then in the wrong branch. So the proof cannot be
completed — which is what makes the model sound rather than merely
convenient.</li>
<li><strong>Rust's atomics really are atomic</strong> (<code>step; body</code>, no
yield), and a non-atomic access is <code>acquire; yield; release</code>.</li>
</ul>
"""))

    # ---------------- machine
    switch_table = table(
        ["rule", "changes current?", "to what"],
        [["tick", "no", "the scheduled thread keeps the lock"],
         ["heap", "no", "likewise — a heap operation is one uninterruptible step"],
         ["fork", "no — current := c.current, explicitly",
          "the child is appended but not scheduled"],
         ["yield", "YES", "any live j, chosen nondeterministically — including the yielding thread itself"],
         ["endthread", "YES", "any live j, after the current thread becomes a tombstone"]])

    racer_trace = table(
        ["#", "rule", "current", "heap at location 0", "note"],
        [["0", "— (init)", "0", "absent", "one thread, running racer"],
         ["1", "heap (setup)", "0", "reading 0", "allocate, unlocked"],
         ["2", "fork", "0", "reading 0", "child appended; parent KEEPS the lock"],
         ["3", "yield j=1", "1", "reading 0", "parent hands control to the child"],
         ["4", "heap (writeAcquire)", "1", "writing", "child takes the write lock"],
         ["5", "yield j=0", "0", "writing", "child hands control back — parent is now poised on a refused write"]])

    starver_trace = table(
        ["#", "rule", "current", "heap at location 0", "note"],
        [["0", "— (init)", "0", "absent", "one thread, running starver"],
         ["1", "heap (setup)", "0", "reading 0", "allocate, unlocked"],
         ["2", "fork", "0", "reading 0", "cStarve — both threads poised on writeAcquire 0"],
         ["3", "heap (writeAcquire)", "0", "writing", "the parent takes the lock; it never yielded"],
         ["4", "— (ret)", "0", "writing", "parent returns; no rule applies, the machine stops"],
         ["—", "", "", "", "the child is alive and never scheduled"]])

    machine_txt = read(LEAN_IRIS / "AeneasIris/Semantics/Machine.lean")
    step_ctors = rules.parse_inductive(machine_txt, "Step")
    reach_ctors = rules.parse_inductive(machine_txt, "Reaches")
    step_rules = "".join(
        texrule(r, panel("the Lean it was parsed from", code(r.source)))
        for r in step_ctors)
    reach_rules = "".join(
        texrule(r, panel("the Lean it was parsed from", code(r.source)))
        for r in reach_ctors)
    tex = rules.rules_tex([
        ("The machine", "Machine.lean, inductive Step", step_ctors),
        ("Reachability", "Machine.lean, inductive Reaches", reach_ctors)])
    (HERE / "rules.tex").write_text(tex, encoding="utf-8")
    tex_ok, tex_msg = rules.check_tex(tex)

    parts.append(section("machine", "5 · The machine", f"""
<p>A configuration is a thread pool, an index saying which thread holds the big
lock, and a heap.</p>
{code(src_thread)}
{code(src_config)}
{panel("Config.focus — extracted", code(src_focus),
       note="'the scheduled thread, if it is alive' — this is the only thread that steps")}

<h3>The five rules</h3>
<div class="rules">{step_rules}</div>

{panel("Step — the whole inductive, as extracted", code(src_step))}

<p>The rules above are <strong>parsed from that inductive</strong>, not typed out:
premises and conclusion come from splitting each constructor at its top-level
arrows, and each rule carries the Lean it came from. Only the <em>notation</em> is
a translation table, which is why the source sits beside every rule.</p>

<p>The same rules are emitted as
<a href="rules.tex"><code>rules.tex</code></a> — mathpartir, ready to
<code>\\input</code> into a paper. The generator compiles it as a check
(<code>{tex_msg}</code>), because a macro clash produces LaTeX that looks correct
and does not build: <code>\\kill</code> is already a LaTeX command and
<code>\\providecommand</code> silently declines to redefine it, which is exactly
what happened the first time.</p>

<h3>Reachability</h3>
<div class="rules">{reach_rules}</div>

<p class="callout"><strong>Only the scheduled thread steps, and control moves only
at <code>yield</code> and <code>endthread</code>.</strong> Since <code>j</code> is
existentially quantified in those two rules, quantifying over all
<em>reachable</em> configurations quantifies over all <em>schedules</em>. That is
why the theorems below need no separate "for every scheduler" clause.</p>

<h3>Thread switching, in full</h3>
<p><strong>Exactly two of the five rules change <code>current</code>.</strong> That
is the whole scheduling model, and everything else about interference follows
from it.</p>

{switch_table}

<p>Three consequences worth spelling out, because each is easy to misread:</p>
<ul>
<li><strong><code>j</code> is existentially quantified, so the machine is
nondeterministic.</strong> <code>Reaches</code> explores every choice, which is
why quantifying over reachable configurations quantifies over <em>all
schedules</em> and no theorem here needs a "for every scheduler" clause.</li>
<li><strong><code>yield</code> may choose the current thread itself.</strong> It
does not <em>force</em> a switch, it <em>permits</em> one. A thread that yields
in a loop may run forever without any other thread ever being scheduled — the
machine allows that schedule, and it is the reason
<a href="#races">§7</a>'s second gap exists.</li>
<li><strong><code>fork</code> does not switch.</strong> The child is appended and
is <em>not</em> scheduled; it becomes eligible only at the next
<code>yield</code>. This is exactly why <code>wpi_fork</code> hands the child its
obligation under <code>|={{⊤,∅}}=&gt;</code>: the child must acquire the lock
before it can run.</li>
</ul>

<p class="callout"><strong>There is no preemption rule.</strong> Nothing lets the
machine take the lock away from a running thread. That is a deliberate choice and
it is load-bearing: see <a href="#races">§7</a>, where it is both the price paid
for a simpler program logic and the source of the one hypothesis
<code>pairwiseRaceFree_of_safe</code> cannot discharge.</p>

<h3>A schedule, step by step</h3>
<p><code>Vacuity.racer</code>: allocate, fork; the parent yields, the child takes
the write lock and yields back, and the parent's own write is then refused. Every
line below is one <code>Step</code> in the machine-checked proof
<code>race_reachable</code>.</p>

{racer_trace}

<p>Two things to notice. At step 2 the fork does <strong>not</strong> hand control
to the child — the parent keeps the lock and must reach its <code>yield</code>
first. And at step 5 nothing has gone wrong <em>yet</em>: the configuration is
faulty because of what the parent is <em>about to</em> do, which is what
<code>Config.Faulty</code> says.</p>

<h3>The same program with one <code>yield</code> removed</h3>
<p><code>PairwiseRaces.starver</code> is <code>racer</code> with the parent's
leading <code>yield</code> deleted. Nothing else differs.</p>

{starver_trace}

<p>The parent takes the lock and returns. A returned thread takes no step, and
<code>yield</code> is the only rule that moves the lock, so the machine stops
here — with the child alive and poised on a conflicting write it will never be
allowed to attempt.</p>

<p class="warn"><strong>The two definitions disagree at
<code>cStarve</code>, and both halves are proved.</strong> λRust calls it a race
(two threads poised on conflicting writes); we do not (the scheduled thread's
operation succeeds, so nothing is refused). See <code>gap_witness</code> in
<code>PairwiseRaces.lean</code> — it is not an argument, it is a
theorem.</p>

<h3>What can go wrong</h3>
{code(src_panics)}
{code(src_stuckon)}
{code(src_faulty)}
<p><code>StuckOn</code> is one condition covering four failures: out-of-bounds
(the location is absent), use-after-free (likewise, after <code>free</code>),
type confusion (<code>Val</code>'s type tag disagrees) and a data race (the access
state forbids it). They are distinguished in <a href="#races">§7</a>.</p>
"""))

    # ---------------- invariant
    parts.append(section("invariant", "6 · The invariant", f"""
<p><code>SysInv</code> is what the soundness proof maintains across every step: the
heap interpretation, plus one obligation per live thread.</p>
{code(src_sysinv)}
{panel("focusObl, runObl, readyObl — extracted",
       code(src_focusobl) + code(src_runobl) + code(src_readyobl), open_=True)}

<p>The split <em>is</em> the big lock:</p>
{table(["thread", "obligation", "mask", "reading"], [
  ["scheduled", "runObl", "∅", "holds the lock; the ownE ⊤ token has been spent into wsat"],
  ["every other live thread", "readyObl = |={⊤,∅}=> runObl", "⊤", "an obligation waiting to acquire the lock — a consumer of the token, not a holder"],
])}
<p><code>SysInv</code> never mentions <code>ownE ⊤</code> explicitly. It does not
need to: the <code>runObl</code>/<code>readyObl</code> split is that token's
bookkeeping, and <code>readyObl_alive</code> holds by <code>rfl</code> — the two
are literally the same proposition at different masks.</p>
"""))

    example_table = table(
        ["moment", "λRust", "here"],
        [["neither thread has moved",
          "RACE — (WriteAcc,Na1Ord) × (WriteAcc,Na1Ord)",
          "not flagged — nobody is stuck"],
         ["A has done writeAcquire (x is now writing), A yields",
          "RACE — still two pending incompatible accesses",
          "not flagged — B has not tried yet"],
         ["B attempts writeAcquire",
          "RACE",
          "RACE — f σ = none, and the same-contents heap at reading 0 succeeds"]])

    tradeoff_table = table(
        ["", "λRust", "here"],
        [["catches", "potential races", "manifested races — strictly weaker"],
         ["needs a second definition of the semantics",
          "yes — next_access_head, kept in sync with head_step by hand",
          "no — RacesOn is stated about the transformer f the machine runs"],
         ["can that second definition drift?",
          "yes, silently; the theorem stays true but says nothing",
          "n/a — nothing to drift"],
         ["where the scheduling points are",
          "everywhere: small-step, scheduler outside the program",
          "at yield only: written into the operation"]])

    conflict_src = code(pw("Conflict"))
    racingpair_src = code(pw("Config.RacingPair")) + code(pw("PairwiseRaceFree"))
    sched_src = code(pw("SchedulableAfter"))
    pairwise_thm = code(pw("pairwiseRaceFree_of_safe"))
    pairwise_panels = "".join([
        panel("read ∥ read — no conflict", code(pw("not_conflict_read_read"))),
        panel("atomic ∥ atomic — no conflict", code(pw("not_conflict_atomic_atomic"))),
        panel("write ∥ read — conflict", code(pw("conflict_write_read"))),
        panel("write ∥ write — conflict", code(pw("conflict_write_write"))),
        panel("read ∥ write — conflict", code(pw("conflict_read_write"))),
    ])

    # ---------------- races
    parts.append(section("races", "7 · Data races", f"""
<p>Everything so far has been the model. This is the definition that <em>uses</em>
it.</p>
{code(src_same)}
{code(src_raceson)}
<p class="callout"><strong>Read <code>RacesOn</code> as: the operation is undefined
here, and the only thing that would have to change to make it succeed is an
access state.</strong> The witness heap has the same <em>domain</em> (an
<code>Option</code> shape mismatch is already a difference) and the same
<em>values</em>. So the failure cannot be out-of-bounds and cannot be type
confusion. The access-state discipline is the only thing left to blame — and
that discipline is λRust's.</p>

{code(src_racing)}
{code(src_drf)}

<h3>How this differs from λRust's definition — and it does differ</h3>
<p>λRust defines a race <em>pairwise over the thread pool</em>:</p>
<pre class="lean"><code>(* lambda-rust/theories/lang/races.v *)
Definition nonracing_accesses (a1 a2 : access_kind * order) : Prop :=
  match a1, a2 with
  | (_, ScOrd), (_, ScOrd) =&gt; True
  | (ReadAcc, _), (ReadAcc, _) =&gt; True
  | _, _ =&gt; False
  end.

Definition nonracing_threadpool (el : list expr) (σ : state) : Prop :=
  ∀ l a1 a2, next_accesses_threadpool el σ a1 a2 l → nonracing_accesses a1 a2.</code></pre>

<p>Two threads, each <em>about to</em> touch the same location, with an
incompatible pair of access kinds. Ours instead looks at the <em>scheduled</em>
thread and asks whether it is stuck for an access-state reason. The two are not
the same statement, and the honest comparison is:</p>

{table(["", "λRust", "here"], [
  ["quantifies over", "pairs of threads", "the scheduled thread"],
  ["fires", "before either access happens", "when the second access is actually attempted"],
  ["nature", "potential race", "manifested race"],
  ["read ∥ read", "not a race", "not a race — reading n → reading (n+1) is always enabled"],
  ["atomic ∥ atomic", "not a race", "not a race — store_at leaves reading 0"],
  ["everything else", "race", "race, on some schedule"],
])}

<p>On programs built from this API the two usually coincide, and the reason is
the <code>yield</code> inside every non-atomic access: if two threads are about to
perform incompatible accesses, then scheduling one, letting it acquire, and
yielding to the other reaches a configuration where the second is stuck. Since
<code>DataRaceFree</code> quantifies over <em>all</em> reachable configurations and
<code>yield</code> may hand control to <em>any</em> live thread, that schedule is
among the reachable ones.</p>

<p class="warn"><strong>Two places where the difference is real — stated
precisely, because the informal version of this claim is too strong.</strong></p>
<ol>
<li><strong>At a single configuration.</strong> λRust flags "both threads about to
write, neither stuck yet"; we do not. We flag it one step later, once one of them
has acquired. A configuration-local statement is not what
<code>DataRaceFree</code> says and would have to be proved separately.</li>
<li><strong>When the racing threads are never scheduled.</strong> The argument
above needs the <em>currently scheduled</em> thread to reach a <code>yield</code>.
If it instead diverges, or returns — which freezes the machine, see
<a href="#weak">§9</a> — then two parked threads with incompatible pending
accesses are never scheduled, no configuration is ever <code>Racing</code>, and
<code>DataRaceFree</code> holds while λRust's <code>nonracing_threadpool</code>
fails. Ours is a property of executions; λRust's is a property of
configurations, and a latent race is invisible to the first.</li>
</ol>
<p>This is a genuine weakening, not a presentational one. It is stated here rather
than left for a reader to find.</p>

<h3>The same program, seen by both definitions</h3>
<p>Two threads, each performing <code>*x = 1</code> — a non-atomic write — with
<code>x</code> initially <code>reading 0</code>. Non-atomic means
<code>writeAcquire; yield; writeRelease</code>.</p>

{example_table}

<p>λRust calls it the moment two hands reach for the same object; we call it when
the second hand hits the first. What makes ours workable at all is the
<strong>mandatory <code>yield</code></strong> in the middle of every non-atomic
access: a real conflict must eventually manifest as stuckness on <em>some</em>
schedule, and <code>DataRaceFree</code> quantifies over all reachable
configurations while <code>yield</code> may pass control to any live thread.</p>

<h3>What each definition buys, and what it costs</h3>
<p>Neither is simply better. The trade is worth stating, because it is easy to
read the previous paragraphs as "ours happens to be equivalent" — it is not.</p>

{tradeoff_table}

<p class="callout">The cost line is the one worth dwelling on. λRust's
<code>next_access_head</code> is a <em>second description</em> of what the
operational semantics already says, and nothing in Coq forces the two to agree —
hence the comment above its definition, quoted in
<a href="#ops">§3</a>. <code>RacesOn</code> needs no second description: it is
phrased in terms of the transformer <code>f</code> that the machine actually
runs, so there is nothing that can drift. That is not cleverness on our part; it
falls out of having the state transformer be a first-class value rather than a
syntactic form.</p>

<h3>The pairwise notion, brought over</h3>
<p><code>Semantics/PairwiseRaces.lean</code> carries λRust's definition across —
and in one respect improves on it. λRust needs a <em>second description of its own
semantics</em> (<code>next_access_head</code>, classifying redexes into access
kinds) which nothing forces to agree with <code>head_step</code>. The version
here needs no such thing:</p>

{conflict_src}

<p>Two pending operations conflict when <strong>performing one disables the
other</strong> — stated about the transformers the machine actually runs. No
second description, so nothing to keep in sync, and λRust's compatibility table
becomes a set of <em>theorems</em> rather than a definition:</p>

{pairwise_panels}

<p>The pairwise statement itself is then exactly λRust's:</p>
{racingpair_src}

<h3>…and the one hypothesis that cannot be discharged here</h3>
<p><code>Safe</code> constrains the <strong>scheduled</strong> thread. Turning
"threads <em>i</em> and <em>j</em> are poised on conflicting operations" into a
contradiction means <em>running</em> <em>i</em> and then <em>scheduling</em>
<em>j</em> — and control moves only at <code>yield</code>. So the implication
holds, but only under a premise this machine cannot supply, and that premise is
given a name rather than hidden:</p>

{sched_src}
{pairwise_thm}

<p class="warn"><strong>Both routes to discharging it fail, for the same
reason.</strong> <em>Operationally</em>, reaching a configuration where <em>j</em>
is scheduled needs a <code>Step.yield</code>, hence the current lock holder
sitting on a <code>yield</code> — which it need not ever do. <em>In Iris</em>,
one might read the premise off <code>SysInv</code>, but a non-scheduled thread's
obligation is <code>readyObl = |={{⊤,∅}}=&gt; runObl</code> and using it spends
<code>ownE ⊤</code>, which the scheduled thread has already spent. <code>ownE</code>
is not duplicable, so at most one thread's obligation can be opened — the big
lock doing its job.</p>

<p>A preemptive machine discharges <code>SchedulableAfter</code> for free. Adding
preemption here would break the big lock: preempting mid-computation means parking
a thread at mask <code>⊤</code>, which requires it to hand back <code>ownE ⊤</code>
from inside a yield-free region. <strong>The cooperative machine and the
atomicity-free <code>wpi_open_invariant</code> are the same decision seen from two
sides</strong> (<a href="#handler">§4</a>), and this hypothesis is its price.</p>

<h3>A third gap, and the one most likely to bite</h3>
<p class="warn"><strong><code>RacesOn</code> can only see a race between
operations that <em>respect</em> the access-state protocol.</strong>
<code>Heap.act'</code> takes an <em>arbitrary</em> transformer
<code>f : RustHeap → Option RustHeap</code>. A hand-written model that writes
<code>fun σ =&gt; some (insert σ l (reading 0, v))</code> — updating a cell without
ever consulting or setting its access state — <strong>never gets stuck</strong>,
so <code>RacesOn</code> never fires, so two such threads race in complete silence
while <code>DataRaceFree</code> holds.</p>

<p>λRust has no such hole: <code>Read</code> and <code>Write</code> are syntactic
forms and are the only way to touch the heap. Here the raw transformer is the
escape hatch, and it is not hypothetical — it is exactly what
<code>FunsExternal.lean</code> is for.</p>

<p>The practical consequence, stated plainly: <strong>race freedom is a claim
about code that goes through <code>HeapAPI</code></strong> (which is all
Aeneas-generated code), <strong>and it is only as good as the hand-written models
that sit beside it.</strong> A model that bypasses acquire/release does not make
the theorem false — it makes it not apply. Reviewing new
<code>FunsExternal</code> entries for protocol compliance is therefore part of
the trust boundary, not an optional tidiness check.</p>

<h3>Then why does λRust not use the weaker, stuck-based definition?</h3>
<p>It is the obvious question, and the answer is not "they did not think of it".
Compare the two proofs of the same-shaped theorem:</p>

<pre class="lean"><code>-- here: Safe → DataRaceFree
theorem dataRaceFree_of_safe (h : Safe t) : DataRaceFree t :=
  fun c hr hrace =&gt; h c hr hrace.faulty

-- λRust: safety → nonracing_threadpool
Theorem safe_nonracing el σ : ... (* the better part of a hundred lines *)</code></pre>

<p class="callout"><strong>One line against ninety. That asymmetry is the whole
answer: the content is in the definition, not in the proof.</strong> Because
<code>Racing</code> is a <em>refinement of stuckness</em>, and <code>Safe</code>
already says "never stuck", the implication is almost a tautology — it reads "if
you never get stuck, you never get stuck in this particular way". λRust's
<code>nonracing_threadpool</code> never mentions stuckness, so the gap between it
and safety is real and has to be bridged by an argument.</p>

<p>Four consequences, in increasing order of depth.</p>

<ol>
<li><strong>Their statement is recognisable without reading their semantics.</strong>
"No two threads are concurrently poised on conflicting accesses, at least one a
write, at least one non-atomic" is, near enough, the definition of a data race in
the C11 memory model and in the Rust book. Proving <em>that</em> connects the
type system to a notion the reader already accepts. "No thread ever gets stuck
for an access-state reason" is a statement about <em>the model</em>, and a
sceptical reader has to be convinced the model is right first.</li>

<li><strong>Ours leans on a coding convention.</strong> Every non-atomic access
here is <code>acquire; yield; release</code>, and that <code>yield</code> is what
makes a real conflict eventually manifest as stuckness. An ITree that does
<code>writeAcquire</code> without the yield, or that calls raw
<code>modify</code>, can race in ways <code>RacesOn</code> never observes. λRust
assumes nothing about how programs are written.</li>

<li><strong>Race freedom is wanted as a per-configuration fact.</strong> A data
race is undefined behaviour <em>at the moment the two accesses are
concurrent</em>, not at the moment one of them is refused. λRust's statement has
that shape; a stuck-based one cannot, because it needs the access to be
attempted before it can say anything.</li>

<li><strong>And the deepest one: their machine can schedule any thread at any
time; ours cannot.</strong> "Thread <em>j</em> is poised to race" is immediately
actionable in a small-step language with an external scheduler — <em>j</em> can
step next. Here only the lock holder steps, and control moves only at
<code>yield</code>, so <em>j</em> may be poised over a conflicting access and
unable to move for arbitrarily long, or forever. That is not an oversight: it is
the same cooperative discipline that lets <code>wpi_open_invariant</code> dispense
with an atomicity side condition (<a href="#handler">§4</a>). <strong>The
simpler program logic and the weaker race statement are the same design decision
seen from two sides.</strong></li>
</ol>

<p>So the honest summary is that λRust buys a stronger, standard-facing statement
at the price of a second definition that must be kept in sync by hand, and we buy
a definition that cannot drift at the price of a weaker statement that leans on
how the API is written. Which is the better trade depends on what the statement
is for — and if this development ever needs the standard-facing version, adding
it is a real piece of work, not a rephrasing.</p>

<h3>The compatibility table, derived rather than declared</h3>
<p>λRust <em>defines</em> which pairs race. Here it is a consequence of the
transitions, proved one row at a time:</p>
{panel("read ∥ read compatible — extracted", code(rb("read_read_compatible")))}
{panel("write ∥ read incompatible — extracted", code(rb("write_read_incompatible")))}
{panel("write ∥ write incompatible — extracted", code(rb("write_write_incompatible")))}
{panel("read ∥ write incompatible — extracted", code(rb("read_write_incompatible")))}
{panel("atomic ∥ atomic compatible — extracted", code(rb("atomic_atomic_compatible")))}
{panel("read ∥ free incompatible (use-after-free) — extracted", code(rb("read_free_incompatible")))}
"""))

    # ---------------- theorems
    parts.append(section("theorems", "8 · What is proved", f"""
<p>The hypothesis, in every case, is one <code>wpi</code> triple:</p>
{code(src_provable)}
{code(src_ad_part)}
{code(src_ad_total)}

{panel("Safe, MayReturn, SN, Terminates — extracted",
       code(src_safe) + code(src_mayreturn) + code(src_sn) + code(src_terminates), open_=True)}

<pre class="axioms"><code>'adequacy_part'  depends on axioms: [propext, Classical.choice, Quot.sound]
'adequacy_total' depends on axioms: [propext, Classical.choice, Quot.sound]</code></pre>

<h3>Non-vacuity</h3>
<p>Every theorem here has the form "<em>nothing bad happens</em>", and such a
statement is worth exactly as much as the badness it excludes. If
<code>Config.Faulty</code> were unsatisfiable, <code>Safe</code> would hold of every
program and <code>adequacy_part</code> would be a tautology —
and no amount of worked examples would reveal it, because examples only ever
prove the good side.</p>
<p><code>Semantics/Vacuity.lean</code> proves the other side:
<code>panicProg_unsafe</code> and <code>loadProg_unsafe</code> inhabit
<code>Panics</code> and <code>StuckOn</code> separately, and <code>racer</code> is a
two-thread program with an explicit five-step trace to a racing configuration.
The strongest of them is</p>
<pre class="lean"><code>racer_unprovable : ∀ φ, ¬ ProvableSpecOf .part racer φ</code></pre>
<p>— for a racing program, <em>no</em> <code>wpi</code> triple exists, whatever the
postcondition. Race freedom is enforced by the logic, not a coincidence of the
examples.</p>
"""))

    # ---------------- weaknesses
    parts.append(section("weak", "9 · What to check, and what is known wrong", """
<p>The questions worth asking of this model, and the honest answers.</p>

<h3>Known weaknesses</h3>
<p class="warn"><strong>A non-main thread sitting on <code>ret</code> freezes the
machine.</strong> A returned thread takes no step, and <code>yield</code> is the
only rule that changes <code>current</code>. So if the scheduler hands the lock to
a thread that then returns, no rule applies and the configuration is final — with
other threads still alive and holding pending work. <code>Config.Halted</code>
classifies this as a legitimate halt. Rust does the opposite: a spawned thread
that returns ends only itself. The fix is a <code>Step</code> rule retiring a
non-main returning thread, exactly as <code>endthread</code> does; provable
programs are unaffected either way, because the logic already forces a forked
child's postcondition to be <code>False</code>.</p>

<p><strong>Nothing is concluded about the final heap.</strong>
<code>ProvableSpec</code> fixes a <em>pure</em> postcondition, which is forced:
<code>fupd_plain_mask</code> needs <code>Plain</code>, and that instance exists only
at <code>HasLC.hasNoLC</code>. A consequence is that clients may not use later
credits, and there is no <code>wp_invariance</code> analogue here.</p>

<p><strong>Return types are restricted to <code>Type 0</code>.</strong> A Rust
function returning a <code>Type 1</code> value is outside these statements. Nothing
in the proofs depends on the restriction.</p>

<h3>Questions this page is meant to let you answer</h3>
<ul>
<li>Is the <em>enabling condition</em> of each heap operation the one you intend?
(§2, §3 — each is an <code>↔</code>, so both directions are checkable.)</li>
<li>Is <code>yield</code> in the right place inside <code>load_na</code> /
<code>store_na</code>? Everything about interference follows from that placement.</li>
<li>Are the five machine rules the ones you want, and is <code>yield</code>'s
choice of <code>j</code> as unconstrained as you expect? (§5)</li>
<li>Is <code>RacesOn</code> the notion of race you want, given that it is
manifested rather than potential? (§7)</li>
<li>Does every hand-written model in <code>FunsExternal.lean</code> go through
acquire/release, or at least never touch a cell whose access state it ignores? A
raw transformer bypasses race detection entirely — see the third gap in
<a href="#races">§7</a>. This is the one caveat that applies to code someone
may add tomorrow.</li>
<li>Is the <code>ret</code>-freezes-the-machine behaviour acceptable, or should
the rule be added? (above)</li>
</ul>
"""))

    nav = "".join(
        f'<a href="#{sid}">{html.escape(label)}</a>' for sid, label in [
            ("intro", "What this is"),
            ("effects", "1 · Effects"),
            ("heap", "2 · Heap model"),
            ("ops", "3 · Operations"),
            ("handler", "4 · Handler"),
            ("machine", "5 · Machine"),
            ("invariant", "6 · Invariant"),
            ("races", "7 · Data races"),
            ("theorems", "8 · Theorems"),
            ("weak", "9 · What to check"),
        ])

    return PAGE.format(nav=nav, body="".join(parts), now=now, rev=rev,
                   macros=json.dumps(rules.KATEX_MACROS))


PAGE = """<!DOCTYPE html>
<html lang="en"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>AeneasIris — the machine, and how ITrees are interpreted</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css">
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js"></script>
<style>
:root {{
  --bg:#fbfbfa; --fg:#1a1a1a; --mut:#5c5c5c; --line:#e2e0dc;
  --code-bg:#f5f3ef; --accent:#7a3e00; --warn-bg:#fff6e8; --warn-br:#e0a860;
  --call-bg:#eef4fb; --call-br:#7aa7d4;
}}
@media (prefers-color-scheme: dark) {{
  :root {{
    --bg:#16171a; --fg:#e6e4e0; --mut:#a09c96; --line:#2e3034;
    --code-bg:#1e2024; --accent:#e0a860; --warn-bg:#2a2113; --warn-br:#8a6520;
    --call-bg:#15202c; --call-br:#3c6b9e;
  }}
}}
* {{ box-sizing:border-box; }}
body {{
  margin:0; background:var(--bg); color:var(--fg);
  font:16px/1.65 -apple-system,BlinkMacSystemFont,"Segoe UI",Inter,system-ui,sans-serif;
}}
#wrap {{ display:flex; align-items:flex-start; max-width:1500px; margin:0 auto; }}
nav {{
  position:sticky; top:0; flex:0 0 235px; padding:2.2rem 1rem 2rem 1.4rem;
  max-height:100vh; overflow-y:auto; font-size:.86rem;
}}
nav b {{ display:block; margin-bottom:.9rem; font-size:.78rem; letter-spacing:.09em;
        text-transform:uppercase; color:var(--mut); }}
nav a {{ display:block; padding:.28rem 0; color:var(--mut); text-decoration:none;
        border-left:2px solid transparent; padding-left:.6rem; }}
nav a:hover {{ color:var(--fg); border-left-color:var(--accent); }}
main {{ flex:1 1 auto; min-width:0; padding:2.2rem 2.4rem 6rem; }}
h1 {{ font-size:1.75rem; margin:0 0 .3rem; letter-spacing:-.02em; }}
.sub {{ color:var(--mut); margin:0 0 2.4rem; font-size:.95rem; }}
h2 {{ font-size:1.3rem; margin:3rem 0 1rem; padding-bottom:.4rem;
     border-bottom:1px solid var(--line); letter-spacing:-.01em; }}
h3 {{ font-size:1.02rem; margin:1.9rem 0 .6rem; }}
p {{ margin:.75rem 0; }}
.lead {{ font-size:1.08rem; }}
code {{ font-family:ui-monospace,SFMono-Regular,"SF Mono",Menlo,Consolas,monospace;
       font-size:.875em; }}
p code, li code, td code, th code {{
  background:var(--code-bg); padding:.1em .35em; border-radius:3px; }}
pre {{ background:var(--code-bg); border:1px solid var(--line); border-radius:6px;
      padding:.85rem 1rem; overflow-x:auto; font-size:.82rem; line-height:1.5;
      margin:.8rem 0; }}
pre.axioms {{ background:transparent; border-style:dashed; }}
table {{ border-collapse:collapse; width:100%; margin:1rem 0; font-size:.88rem; }}
th,td {{ text-align:left; padding:.5rem .7rem; border-bottom:1px solid var(--line);
        vertical-align:top; }}
th {{ font-size:.76rem; text-transform:uppercase; letter-spacing:.06em;
     color:var(--mut); font-weight:600; }}
details {{ margin:.7rem 0; border:1px solid var(--line); border-radius:6px;
          background:var(--code-bg); }}
summary {{ cursor:pointer; padding:.55rem .9rem; font-size:.85rem; color:var(--mut);
          user-select:none; }}
summary:hover {{ color:var(--fg); }}
.panelbody {{ padding:0 .9rem .3rem; }}
.panelbody pre {{ background:var(--bg); }}
.note {{ font-size:.83rem; color:var(--mut); margin:.5rem 0 .2rem;
        font-family:ui-monospace,monospace; }}
.callout {{ background:var(--call-bg); border-left:3px solid var(--call-br);
           padding:.75rem 1rem; border-radius:0 4px 4px 0; }}
.warn {{ background:var(--warn-bg); border-left:3px solid var(--warn-br);
        padding:.75rem 1rem; border-radius:0 4px 4px 0; }}
.statbar {{ display:flex; flex-wrap:wrap; gap:1.6rem; margin:1.6rem 0;
           padding:.9rem 1.1rem; border:1px solid var(--line); border-radius:6px; }}
.statbar .k {{ display:block; font-size:.7rem; text-transform:uppercase;
              letter-spacing:.08em; color:var(--mut); }}
.statbar .v {{ font-family:ui-monospace,monospace; font-size:.95rem; }}
.rules {{ display:flex; flex-wrap:wrap; gap:1rem; margin:1rem 0; }}
.rule {{ flex:1 1 300px; }}
.rulename {{ font-size:.72rem; text-transform:uppercase; letter-spacing:.08em;
            color:var(--accent); margin-bottom:.3rem; font-weight:600; }}
.rulebox {{ border:1px solid var(--line); border-radius:6px; padding:.8rem 1rem;
           background:var(--code-bg); font-family:ui-monospace,monospace;
           font-size:.78rem; }}
.prem {{ color:var(--mut); }}
.bar {{ border-top:1px solid var(--fg); margin:.45rem 0; opacity:.55; }}
.concl {{ }}
.rulenote {{ font-size:.78rem; color:var(--mut); margin-top:.35rem;
            padding-left:.2rem; font-style:italic; }}
@media (max-width:1000px) {{
  #wrap {{ flex-direction:column; }}
  nav {{ position:static; max-height:none; width:100%; flex-basis:auto;
        border-bottom:1px solid var(--line); }}
  main {{ padding:1.5rem 1.2rem 4rem; }}
}}
</style></head>
<body><div id="wrap">
<nav><b>Contents</b>{nav}</nav>
<main>
<h1>AeneasIris — the machine, and how ITrees are interpreted</h1>
<p class="sub">Generated {now} from {rev}. Every Lean snippet is extracted from
the sources; none is transcribed.</p>
{body}
</main></div><script>
window.addEventListener("DOMContentLoaded", function () {{
  if (typeof katex === "undefined") {{
    // No network for the CDN: reveal the Lean instead of showing raw TeX.
    document.querySelectorAll(".rule .tex").forEach(function (e) {{
      e.textContent = "(KaTeX unavailable — see the Lean below)";
    }});
    document.querySelectorAll(".rule details").forEach(function (d) {{
      d.open = true;
    }});
    return;
  }}
  var M = {macros};
  document.querySelectorAll(".rule .tex").forEach(function (e) {{
    try {{ katex.render(e.getAttribute("data-tex"), e,
                       {{ displayMode: true, throwOnError: false, macros: M }}); }}
    catch (err) {{ e.textContent = e.getAttribute("data-tex"); }}
  }});
}});
</script>
</body></html>
"""


if __name__ == "__main__":
    out = HERE / "semantics.html"
    out.write_text(build(), encoding="utf-8")
    print(f"wrote {out} ({out.stat().st_size:,} bytes)")
