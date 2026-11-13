#!/usr/bin/env python3
"""Extract the help texts of wasm-tools 1.262.0 that the grammar does not hold.

python3 -I tools/cli-spec/gen-wasm-tools-doc.py CLI_SPEC WASM_TOOLS > Silmaril/Cli/Spec/WasmTools/Doc/Defs.lean

CLI_SPEC is the built `.lake/build/bin/cli-spec`, WASM_TOOLS the pinned binary (SHA-256
fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211). For every command path of
`Silmaril.Cli.Spec.WasmTools.grammar` (`cli-spec paths wasm-tools`) the script runs upstream's
`-h` and `--help` (COLUMNS unset, output to a pipe: clap's width is 100; and with COLUMNS=80, to
tell clap's line breaks from the source's in the texts after the options) and records, as Lean
data:

* the text after the option table of `-h` (clap's `after_help`), exactly;
* for `--help`: the long about, the long help of every argument (keyed by the grammar's
  `id`, through `cli-spec rows`) and the long text after the options, where they differ
  from the short ones.

Wrapped lines are joined back: a line break is clap's (a space in the source) exactly when the
next line starts with the indentation of the line it continues and its first word would not
have fit on that line (`Silmaril.Cli.Clap.Help.wrap`); every other line break is the source's. The notes `[default: …]` and `[possible values: …]` are dropped
(the grammar renders them). The extraction is checked, not trusted:
`tools/cli-spec/tests/wasm-tools-surface.sh` renders both help texts of every path from the
grammar and this data (`cli-spec text`) and compares them with upstream byte for byte.
"""

import os
import subprocess
import sys


def run(argv, columns=None):
    env = {k: v for k, v in os.environ.items() if k not in ("COLUMNS", "LINES")}
    if columns is not None:
        env["COLUMNS"] = str(columns)
    r = subprocess.run(argv, capture_output=True, env=env, cwd="/", stdin=subprocess.DEVNULL)
    return r.stdout.decode("utf-8")


def words(line):
    """clap's `find_words_ascii_space`: runs of non-spaces with the spaces after them; leading
    spaces are a word of their own."""
    out, start, in_ws = [], 0, False
    for i, ch in enumerate(line):
        if in_ws and ch != " ":
            out.append(line[start:i])
            start = i
        in_ws = ch == " "
    if start < len(line):
        out.append(line[start:])
    return out


def wrap(text, width):
    """clap 4.6's `StyledStr::wrap` (the Python twin of `Silmaril.Cli.Clap.Help.wrap`)."""
    res = []
    for line in text.splitlines(keepends=True):
        ws = words(line)
        ind = ws[0] if ws and ws[0].strip() == "" else ""
        lw, first, acc = 0, True, []
        for w in ws:
            t = w.rstrip()
            delta = len(w) - len(t)
            if first and len(t) > 0:
                first = False
            elif width < lw + len(t):
                if acc:
                    acc[-1] = acc[-1].rstrip()
                acc += ["\n", ind]
                lw = len(ind)
            lw += len(t) + delta
            acc.append(w)
        res.append("".join(acc))
    return "".join(res).rstrip()


def unwrap(lines, width, hard=frozenset()):
    """Join the lines clap broke when wrapping to `width` columns. clap repeats a line's
    indentation on the lines it breaks off, so a continuation starts with the indentation of
    the line it continues, and it can be one only when its first word would not have fit; the
    line indices in `hard` are kept as line breaks of the source."""
    out = []  # (text, indentation, length of the last physical line)
    for k, m in enumerate(lines):
        if out and k not in hard:
            text, ind, last = out[-1]
            rest = m[len(ind):]
            if last > 0 and m.startswith(ind) and rest and not rest.startswith(" "):
                if last + 1 + len(rest.split(" ")[0]) > width:
                    out[-1] = (text + " " + rest, ind, len(m))
                    continue
        ind = m[: len(m) - len(m.lstrip(" "))] if m.strip() else ""
        out.append((m, ind, len(m)))
    return "\n".join(t for t, _, _ in out)


def ambiguous(lines, width):
    """The indices of the lines `unwrap` joins to the line before."""
    a = unwrap(lines, width).split("\n")
    return [k for k in range(1, len(lines)) if len(unwrap(lines[: k + 1], width).split("\n")) ==
            len(unwrap(lines[:k], width).split("\n"))]


def unwrap_checked(lines, width, narrow, narrow_width):
    """`unwrap`, with the joins that are really line breaks of the source found by wrapping
    the result again to `narrow_width` and comparing with `narrow`, upstream's text at that
    width (every subset of the ambiguous joins, at most 2^12)."""
    amb = ambiguous(lines, width)
    if narrow is None or wrap(unwrap(lines, width), narrow_width) == narrow.rstrip():
        return unwrap(lines, width)
    import itertools
    for r in range(1, len(amb) + 1):
        if len(amb) > 12:
            break
        for hard in itertools.combinations(amb, r):
            cand = unwrap(lines, width, frozenset(hard))
            if wrap(cand, narrow_width) == narrow.rstrip():
                return cand
    sys.exit("cannot reconstruct a source text that wraps to upstream's at both widths:\n" +
             "\n".join(lines[:3]))


def is_row_start(line):
    return (len(line) > 2 and line[:2] == "  " and line[2] != " ") or \
        (line.startswith("      --") and len(line) > 8)


def long_rows(text):
    """The rows of the `Arguments:` and `Options:` sections of a long help, and the text after
    them (or None)."""
    lines = text.split("\n")
    rows = []
    i = 0
    after_start = None
    while i < len(lines):
        if lines[i] in ("Arguments:", "Options:"):
            i += 1
            while i < len(lines):
                line = lines[i]
                if is_row_start(line):
                    left = line[2:]
                    body = []
                    i += 1
                    while i < len(lines) and (lines[i].startswith(" " * 10) or
                                              lines[i] == " " * 10):
                        body.append(lines[i][10:])
                        i += 1
                    rows.append((left, body))
                elif line == "":
                    i += 1
                else:
                    break
            if i < len(lines) and lines[i] not in ("Arguments:", "Options:"):
                after_start = i
                break
            continue
        i += 1
    after = None
    if after_start is not None:
        # the blank lines before the text beyond clap's one blank line belong to it
        j = after_start
        while j > 0 and lines[j - 1] == "":
            j -= 1
        blank = after_start - j
        after = (blank - 1, "\n".join(lines[after_start:]).rstrip("\n").split("\n"))
    return rows, after


def short_after(text):
    """The text after the last section of a short help: the blank lines it starts with
    (beyond clap's one) and its lines."""
    lines = text.rstrip("\n").split("\n")
    last = max((k for k, l in enumerate(lines) if l in ("Arguments:", "Options:", "Commands:")),
               default=None)
    if last is None:
        return None
    k = last + 1
    while k < len(lines) and lines[k] != "":
        k += 1
    if k >= len(lines):
        return None
    j = k
    while j < len(lines) and lines[j] == "":
        j += 1
    return (j - k - 1, lines[j:])


def source_after(found, narrow):
    """The source text of an after text found at 100 columns (`short_after`/`long_rows`),
    checked against the same text found at 80 columns."""
    if found is None:
        return None
    blank, lines = found
    return "\n" * blank + unwrap_checked(lines, 100, "\n".join(narrow[1]) if narrow else None, 80)


def strip_notes(text, notes):
    if notes and text.endswith(notes):
        text = text[: -len(notes)]
        if text.endswith("\n\n"):
            text = text[:-2]
    return text


def lean_str(s):
    out = ['"']
    for ch in s:
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\t":
            out.append("\\t")
        else:
            out.append(ch)
    out.append('"')
    return "".join(out)


def lean_path(p):
    return "[" + ", ".join(lean_str(x) for x in p) + "]"


def main():
    cs, wt = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
    paths = [l.split() for l in run([cs, "paths", "wasm-tools"]).splitlines()]
    afters = []
    longs = []
    for p in paths:
        short = run([wt] + p + ["-h"])
        long = run([wt] + p + ["--help"])
        a = source_after(short_after(short), short_after(run([wt] + p + ["-h"], 80)))
        if a:
            afters.append((p, a))
        if long == short:
            continue
        rows_ids = {}
        for l in run([cs, "rows", "wasm-tools"] + p).splitlines():
            ident, left = l.split("\t", 1)
            rows_ids[left] = ident
        about_long = long.split("\n\nUsage: ", 1)[0]
        about_short = short.split("\n\nUsage: ", 1)[0]
        entry = {}
        if about_long != about_short:
            entry["about"] = unwrap(about_long.split("\n"), 100)
        rows, after = long_rows(long)
        after = source_after(after, long_rows(run([wt] + p + ["--help"], 80))[1])
        args = []
        for left, body in rows:
            text = unwrap(body, 90)
            ident = rows_ids.get(left)
            if ident is None:
                sys.exit(f"no grammar row for '{left}' at {p}")
            notes = notes_of(text)
            args.append((ident, strip_notes(text, notes)))
        entry["args"] = args
        if after is not None and after != a:
            entry["after"] = after
        longs.append((p, entry))
    emit(afters, longs)


def notes_of(text):
    """The trailing `[default: …] [possible values: …]` paragraph of a long help, if any."""
    paras = text.split("\n\n")
    last = paras[-1]
    if last.startswith("[default: ") or last.startswith("[possible values: "):
        return last
    return ""


def emit(afters, longs):
    w = sys.stdout.write
    w("""module

public import Silmaril.Cli.Clap.Defs

/-!
# The help texts of `wasm-tools` 1.262.0 beyond the grammar

The text after the option table of every `-h` (clap's `after_help`), and the long texts of
`--help` (the long about, the long help of every argument, the long text after the options):
upstream's documentation (Apache-2.0 WITH LLVM-exception OR MIT), extracted from the pinned
binary (SHA-256 `fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211`) by
`tools/cli-spec/gen-wasm-tools-doc.py` (generated; do not edit). Rendered by
`Silmaril.Cli.Clap.Help`; `tools/cli-spec/tests/wasm-tools-surface.sh` compares the rendering of
every command path with upstream byte for byte.
-/

@[expose] public section

namespace Silmaril.Cli.Spec.WasmTools.Doc

open Silmaril.Cli

/-- The text after the option table of `-h`, by command path (below the root). -/
def after : List (List String × String) := [
""")
    w(",\n".join(f"  ({lean_path(p)},\n    {lean_str(a)})" for p, a in afters))
    w("]\n\n")
    w("/-- The long texts of `--help`, by command path (below the root). -/\n")
    w("def long : List (List String × Clap.Long) := [\n")
    items = []
    for p, e in longs:
        fields = []
        if "about" in e:
            fields.append(f"about := some {lean_str(e['about'])}")
        if "after" in e:
            fields.append(f"after := some {lean_str(e['after'])}")
        args = ",\n      ".join(f"({lean_str(i)}, {lean_str(t)})" for i, t in e["args"])
        fields.append(f"args := [\n      {args}]")
        items.append(f"  ({lean_path(p)}, {{\n    " + ",\n    ".join(fields) + " })")
    w(",\n".join(items))
    w("]\n\nend Silmaril.Cli.Spec.WasmTools.Doc\n")


if __name__ == "__main__":
    main()
