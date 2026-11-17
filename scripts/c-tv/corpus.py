#!/usr/bin/env python3
"""Run the C translation-validation pipeline on the corpus (docs/projects/c-tv.md, stage 2).

For each C file of examples/c-programs/src it writes examples/c-programs/<name>/:

  source.c                 the source, byte for byte
  preprocessed.i           `gcc -E -P -std=c11` (the Cerberus-route input)
  clang-ast.json.gz        (SHA-256 of the uncompressed bytes) `clang -x c -std=c11 -Xclang -ast-dump=json -fsyntax-only` on preprocessed.i
  cerberus.tail.sexp       typed Ail from the Lean port of Cerberus's frontend (`cerb-lean parse --level tail`)
  clang.tail.sexp          typed Ail from Clang's AST (`cfront ail`)
  <route>.core.sexp.gz     Core from the Lean elaborator (`ctv-pipeline`); SHA-256 of the uncompressed bytes
  native-O0.out, -O2.out   stdout of the gcc builds (sanity runs, not validation)
  report.json              the pipeline's verdicts (`ctv-pipeline run`, evidence kind `compiled`)
  provenance.json          every artifact with SHA-256, size, producer and inputs; the edges and their evidence

A stage that fails leaves its artifact absent and records the failure; nothing is fabricated.

Usage: scripts/c-tv/corpus.py [--bin .lake/build/bin] [NAME...]
       scripts/c-tv/corpus.py --check [--bin .lake/build/bin]
         re-run `ctv-pipeline run` on the stored typed Ail and observations of every program and
         compare with the stored report and Core documents (needs neither gcc nor clang)
"""
import gzip, hashlib, json, os, re, shutil, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def _torture():
    import importlib.util
    spec = importlib.util.spec_from_file_location("ctv_torture", os.path.join(os.path.dirname(os.path.abspath(__file__)), "torture.py"))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


# Native runs share the torture runner's caps (time, CPU, memory, file size, stdout bytes).
run_native, NATIVE = _torture().run_native, _torture().NATIVE
CORPUS = os.path.join(ROOT, "examples", "c-programs")
RUNTIME = os.path.join(ROOT, "benchmarks", "cerberus-elaboration", "oracle", "constant-return", "core.sexp.gz")
TARGET = "x86_64-linux-gnu"


def sha256(data):
    return hashlib.sha256(data).hexdigest()


# Tool runs share the torture runner's launcher: a deadline over the whole lifecycle, the process
# group killed at the end, outputs capped, no stdin.
_tool_run = _torture().run


def run(cmd, cwd, timeout=600):
    return _tool_run(cmd, cwd, timeout)


def version(cmd):
    rc, out, _ = run(cmd, ROOT)
    return out.decode(errors="replace").splitlines()[0] if rc == 0 and out else "unknown"


def file_sha(path):
    with open(path, "rb") as f:
        return sha256(f.read())


def git_rev():
    rc, out, _ = run(["git", "rev-parse", "HEAD"], ROOT)
    rev = out.decode().strip() if rc == 0 else "unknown"
    rc, out, _ = run(["git", "status", "--porcelain", "--", "Silmaril", "tools", "lakefile.toml"], ROOT)
    return rev + ("-dirty" if out.strip() else "")


def max_symbol(texts):
    best = 0
    for t in texts:
        for m in re.finditer(r'\(Symbol \(\$str "[0-9a-f]*"\) (\d+)', t):
            best = max(best, int(m.group(1)))
    return best + 1


def one(name, binary, tools, rev):
    src = os.path.join(CORPUS, "src", name + ".c")
    out = os.path.join(CORPUS, name)
    if os.path.isdir(out):
        shutil.rmtree(out)
    os.makedirs(out)
    artifacts, edges, failures = {}, [], {}

    def art(stage, fname, data_path=None, producer=None, inputs=(), uncompressed=None):
        path = os.path.join(out, fname)
        data = uncompressed if uncompressed is not None else open(path, "rb").read()
        artifacts[fname] = {"stage": stage, "sha256": sha256(data), "bytes": len(data),
                            "file": fname, "producer": producer, "inputs": list(inputs)}
        return artifacts[fname]["sha256"]

    shutil.copyfile(src, os.path.join(out, "source.c"))
    s_src = art("source", "source.c")

    # Preprocessing (external).
    gcc_args = ["gcc", "-E", "-P", "-std=c11", "source.c", "-o", "preprocessed.i"]
    rc, _, err = run(gcc_args, out)
    if rc != 0:
        failures["preprocessed"] = err.decode(errors="replace")[-2000:]
        s_pre = None
    else:
        s_pre = art("preprocessed", "preprocessed.i",
                    producer={"tool": "gcc -E", "version": tools["gcc"], "args": gcc_args[1:], "target": TARGET},
                    inputs=[s_src])
        edges.append({"source": s_src, "target": s_pre, "relation": "produces", "evidence": {"external": "gcc -E"}})

    s_ctail = s_ktail = s_ast = None
    if s_pre:
        # Cerberus route: the Lean port of Cerberus's frontend.
        rc, so, se = run([os.path.join(binary, "cerb-lean"), "parse", "--level", "tail", "preprocessed.i"], out)
        if rc == 0:
            open(os.path.join(out, "cerberus.tail.sexp"), "wb").write(so)
            s_ctail = art("typedAil", "cerberus.tail.sexp",
                          producer={"tool": "cerb-lean parse --level tail", "version": rev, "args": ["preprocessed.i"], "target": TARGET},
                          inputs=[s_pre])
            edges.append({"source": s_pre, "target": s_ctail, "relation": "elaborates",
                          "evidence": {"compiled": "Silmaril.Cerberus.Frontend (cerb-lean)"}})
        else:
            failures["cerberus.tail"] = {"exit": rc, "output": (so + se).decode(errors="replace")[-2000:]}
        # Clang route: Clang's JSON AST (external, untrusted), then cfront.
        clang_args = ["clang", "-x", "c", "-std=c11", "-target", TARGET, "-Xclang", "-ast-dump=json", "-fsyntax-only", "preprocessed.i"]
        rc, so, se = run(clang_args, out)
        if rc == 0:
            with gzip.GzipFile(os.path.join(out, "clang-ast.json.gz"), "wb", mtime=0) as g:
                g.write(so)
            open(os.path.join(out, "clang-ast.json"), "wb").write(so)
            s_ast = art("clangAst", "clang-ast.json.gz",
                        producer={"tool": "clang -ast-dump=json", "version": tools["clang"], "args": clang_args[1:], "target": TARGET},
                        inputs=[s_pre], uncompressed=so)
            artifacts["clang-ast.json.gz"]["sha256Of"] = "uncompressed"
            edges.append({"source": s_pre, "target": s_ast, "relation": "produces", "evidence": {"external": "clang"}})
            rc, so2, se2 = run([os.path.join(binary, "cfront"), "ail", "clang-ast.json"], out)
            os.remove(os.path.join(out, "clang-ast.json"))
            if rc == 0:
                open(os.path.join(out, "clang.tail.sexp"), "wb").write(so2)
                s_ktail = art("typedAil", "clang.tail.sexp",
                              producer={"tool": "cfront ail", "version": rev, "args": ["clang-ast.json"], "target": TARGET},
                              inputs=[s_ast])
                edges.append({"source": s_ast, "target": s_ktail, "relation": "elaborates",
                              "evidence": {"compiled": "Silmaril.Clang.ToAil (cfront)"}})
            else:
                failures["clang.tail"] = {"exit": rc, "output": (so2 + se2).decode(errors="replace")[-2000:]}
        else:
            failures["clang-ast"] = {"exit": rc, "output": se.decode(errors="replace")[-2000:]}

    # Native sanity runs (not validation).
    observes = []
    for level in ["O0", "O2"]:
        exe = os.path.join(out, f"native-{level}")
        rc, _, err = run(["gcc", f"-{level}", "-std=c11", "-w", "source.c", "-o", exe], out)
        if rc != 0:
            failures[f"native-{level}"] = err.decode(errors="replace")[-1000:]
            continue
        res, so = run_native(exe, out)
        os.remove(exe)
        if res["ended"] not in ("exit", "signal"):
            failures[f"native-{level}"] = f"run ended by {res['ended']} (caps: {NATIVE})"
            continue
        term = (("abort" if res["code"] == 6 else f"signal:{res['code']}") if res["ended"] == "signal" else str(res["code"]))
        open(os.path.join(out, f"native-{level}.out"), "wb").write(so)
        observes += ["--observe", f"gcc-{level}", term, f"native-{level}.out"]

    # Elaboration, exploration and validation (compiled Lean).
    routes = []
    texts = []
    for route, s in [("cerberus", s_ctail), ("clang", s_ktail)]:
        if s:
            routes.append(f"{route}={route}.tail.sexp")
            texts.append(open(os.path.join(out, f"{route}.tail.sexp")).read())
    report = None
    if routes:
        fresh = max_symbol(texts)
        rc, so, se = run([os.path.join(binary, "ctv-pipeline"), "run", RUNTIME, str(fresh), "."] + observes + routes, out, timeout=1800)
        if rc == 0:
            report = json.loads(so)
            report["runtime"] = os.path.relpath(RUNTIME, ROOT)
            for route, s in [("cerberus", s_ctail), ("clang", s_ktail)]:
                r = report["routes"].get(route)
                if r and r.get("status") == "elaborated":
                    core_path = os.path.join(out, f"{route}.core.sexp")
                    data = open(core_path, "rb").read()
                    with gzip.GzipFile(core_path + ".gz", "wb", mtime=0) as g:
                        g.write(data)
                    os.remove(core_path)
                    s_core = art("core", f"{route}.core.sexp.gz",
                                 producer={"tool": "ctv-pipeline run", "version": rev, "args": [], "target": TARGET},
                                 inputs=[s], uncompressed=data)
                    artifacts[f"{route}.core.sexp.gz"]["sha256Of"] = "uncompressed"
                    r["core"] = f"{route}.core.sexp.gz"
                    edges.append({"source": s, "target": s_core, "relation": "elaborates",
                                  "evidence": {"compiled": "Silmaril.Cerberus.Elaboration.Functions.elaborate"}})
                    r["coreSha256"] = s_core
            cores = {k: v["coreSha256"] for k, v in report["routes"].items() if "coreSha256" in v}
            for p in report["pairs"]:
                if p["source"] in cores and p["target"] in cores:
                    # Two frontends' Cores: a frontend agreement (Core to Core), not a compiler relation.
                    rel = "frontendAgreement"
                    edges.append({"source": cores[p["source"]], "target": cores[p["target"]], "relation": rel,
                                  "verdict": p["verdict"], "coveredOnlyByUB": p["coveredOnlyByUB"],
                                  "validatedUBFree": p["validatedUBFree"],
                                  "evidence": {"compiled": "Silmaril.Cerberus.TV.validate"} if p["verdict"] in ("validated", "refuted") else "missing",
                                  "profile": "linuxX86_64"})
            json.dump(report, open(os.path.join(out, "report.json"), "w"), indent=1, sort_keys=True)
            open(os.path.join(out, "report.json"), "a").write("\n")
        else:
            failures["ctv-pipeline"] = {"exit": rc, "output": (so + se).decode(errors="replace")[-2000:]}
    for f in os.listdir(out):
        if f.endswith(".out") and f not in artifacts:
            art("observation", f, producer={"tool": "gcc " + f[7:9] + " && run", "version": tools["gcc"], "args": [], "target": TARGET}, inputs=[s_src])
    # Constructs a route accepted while dropping them (recorded, not hidden). A **blocking** loss
    # means the route's typed Ail (and every Core and verdict downstream of it) no longer
    # corresponds to the source: the C-to-Core edge of that route is not a translation of this C.
    losses = []
    pre_text = open(os.path.join(out, "preprocessed.i"), errors="replace").read() if s_pre else ""
    if s_ctail and re.search(r"\b(__asm__|__asm|asm)\s*(volatile|__volatile__)?\s*\(", pre_text):
        losses.append({"route": "cerberus", "construct": "asm label or register", "blocking": True,
                       "rule": "dropped by the parser, as upstream c_parser.mly does "
                               "(Silmaril/Raw/Cerberus/Frontend/Declarations.lean, initDeclaratorRest)",
                       "why": "the assembler name or register the declaration gives is lost: the route's "
                              "Core does not represent the source's linkage names"})
    attrs = sorted({a.strip("_") for a in re.findall(r"__attribute__\s*\(\(\s*([A-Za-z_][A-Za-z0-9_]*)", pre_text)})
    NEUTRAL = {"used", "unused", "deprecated", "noinline", "always_inline"}
    HANDLED_BY_CFRONT = {"aligned", "mode"}
    for route, typed in [("clang", s_ktail), ("cerberus", s_ctail)]:
        if not typed:
            continue
        for a in attrs:
            if route == "clang" and a in HANDLED_BY_CFRONT:
                continue
            neutral = route == "clang" and a in NEUTRAL
            losses.append({"route": route, "construct": f"attribute {a}", "blocking": not neutral,
                           "rule": ("dropped as neutral: it requests diagnostics or inlining only "
                                    "(Silmaril/Raw/Compiler/Clang/ToAil.lean, neutralAttr)") if neutral else
                                   ("accepted by the route, which does not show that it keeps it "
                                    "(calling convention, layout, linkage and section attributes change the program)"),
                           "why": "no observable whole-program behaviour depends on it" if neutral else
                                  "the route's Core may not represent what the attribute changes"})
    warnings = []
    if s_ktail:
        # The document's header is cfront's self-report; it is compared with the clang that ran, never trusted.
        head = open(os.path.join(out, "clang.tail.sexp"), errors="replace").read(300)
        m = re.search(r'^\(\$document_tail 1 \(\$str "([^"]*)"\)', head)
        actual = tools["clang"]
        if m and m.group(1) != actual:
            warnings.append(f"clang.tail.sexp names its producer '{m.group(1)}', but the AST was produced by '{actual}' "
                            "(the header is cfront's self-report; tools.clang is what ran)")
    prov = {"schema": "silmaril.c-tv.provenance.v1", "name": name, "language": "C11", "target": TARGET,
            "profile": "linuxX86_64", "repositoryRevision": rev, "tools": tools,
            "artifacts": artifacts, "edges": edges, "failures": failures,
            "losses": losses, "warnings": warnings,
            "blockedRoutes": sorted({l["route"] for l in losses if l["blocking"]})}
    for e in edges:
        # The typed Ail of a blocked route, and everything downstream, does not correspond to the source.
        for r in prov["blockedRoutes"]:
            if artifacts.get(f"{r}.tail.sexp", {}).get("sha256") in (e["source"], e["target"]):
                e["sourceCorrespondence"] = "blocked: " + "; ".join(l["construct"] for l in losses if l["blocking"] and l["route"] == r)
    json.dump(prov, open(os.path.join(out, "provenance.json"), "w"), indent=1, sort_keys=True)
    open(os.path.join(out, "provenance.json"), "a").write("\n")
    return name, report, failures


STATUSES = [
    ("frontend-rejected", "no route produced typed Ail"),
    ("elaborator-rejected", "typed Ail from some route, Core from none"),
    ("single-route", "Core from exactly one route (the other rejected at its frontend or elaborator)"),
    ("agreement-ub-free", "Core from both routes; each refines the other (TV.validate, compiled) with a UB-free source both ways (validateUBFree)"),
    ("agreement-ub-only", "Core from both routes; each refines the other, but some exploration reaches undefined behaviour"),
    ("other", "Core from both routes, any other verdict (refuted, unknown, unsupported)"),
]


def status_of(report, prov):
    """The program's one corpus status (disjoint; see STATUSES)."""
    typed = [r for r in ("cerberus", "clang") if f"{r}.tail.sexp" in prov["artifacts"]]
    if not typed:
        return "frontend-rejected"
    el = {k: v for k, v in (report or {}).get("routes", {}).items() if v.get("status") == "elaborated"}
    if not el:
        return "elaborator-rejected"
    if len(el) == 1:
        return "single-route"
    pairs = report["pairs"]
    if pairs and all(p["verdict"] == "validated" for p in pairs):
        clean = (all(p["validatedUBFree"] for p in pairs) if all("validatedUBFree" in p for p in pairs) else
                 all(not v["explore"]["ub"] and not v["explore"]["limited"] for v in el.values()))
        return "agreement-ub-free" if clean else "agreement-ub-only"
    return "other"


def readme_tables():
    """The generated part of examples/c-programs/README.md (after its `<!-- corpus tables -->` line)."""
    index = json.load(open(os.path.join(CORPUS, "index.json")))
    progs = index["programs"]
    n = len(progs)
    load = lambda name, f: json.load(open(os.path.join(CORPUS, name, f))) if os.path.exists(os.path.join(CORPUS, name, f)) else None
    L = [f"## The corpus ({n} programs)", "",
         "### One status per program", "",
         f"The statuses are disjoint: every program has exactly one, and the counts sum to {n}.", "",
         "| Status | Meaning | Count | Programs |", "| --- | --- | ---: | --- |"]
    for st, meaning in STATUSES:
        names = [p["name"] for p in progs if p["status"] == st]
        L.append(f"| `{st}` | {meaning} | {len(names)} | {', '.join(f'`{x}`' for x in names)} |")
    L.append(f"| **total** | | **{sum(1 for p in progs)}** | |")
    blocked = [p["name"] for p in progs if p["blockedRoutes"]]
    L += ["", f"Separately, {len(blocked)} program(s) have a route whose source correspondence is **blocked** by a "
          f"construct it dropped ({', '.join(f'`{x}`' for x in blocked) or 'none'}): that route's typed Ail, Core and "
          "verdicts are not about this C program (see `losses` in `provenance.json`).", "",
          "### Stage reached, per route", "",
          f"Each column counts every program once, so each sums to {n}.", "",
          "| Stage reached | Cerberus route | Clang route |", "| --- | ---: | ---: |"]
    def stage(p, r):
        prov = load(p["name"], "provenance.json")
        rep = load(p["name"], "report.json")
        if f"{r}.tail.sexp" not in prov["artifacts"]:
            return "rejected by the frontend (no typed Ail)"
        v = (rep or {}).get("routes", {}).get(r)
        if not v or v.get("status") != "elaborated":
            return "typed Ail, rejected by the elaborator"
        return "Core, source correspondence blocked" if r in p["blockedRoutes"] else "Core"
    for st in ["rejected by the frontend (no typed Ail)", "typed Ail, rejected by the elaborator", "Core", "Core, source correspondence blocked"]:
        L.append(f"| {st} | {sum(1 for p in progs if stage(p, 'cerberus') == st)} | {sum(1 for p in progs if stage(p, 'clang') == st)} |")
    L.append(f"| **total** | **{n}** | **{n}** |")
    L += ["", "### Programs", "",
          "| Program | Status | Cerberus route | Clang route | Route agreement (compiled) | Native runs (sanity) | Dropped by a route |",
          "| --- | --- | --- | --- | --- | --- | --- |"]
    for p in progs:
        prov = load(p["name"], "provenance.json")
        rep = load(p["name"], "report.json")
        def cell(r):
            st = stage(p, r)
            if not st.startswith("Core"):
                return st
            v = rep["routes"][r]
            e = v["explore"]
            o = (e["sample"][0] if e["sample"] else {}).get("outcome", {})
            c = f"Core: {o.get('kind', '?')}{(' ' + str(o['exit'])) if 'exit' in o else ''}"
            a = v.get("applicability")
            if a is not None and not a["applies"]:
                c += " (per-type check fails)"
            if r in p["blockedRoutes"]:
                c += " — **source correspondence blocked**"
            return c
        v = p["verdicts"]
        agree = "; ".join(f"{k}: {x}" for k, x in v.items()) or "—"
        obs = "—"
        if rep and rep["observations"]:
            obs = "; ".join(f"{o['name']} {o['termination']}" + (": " + ", ".join(f"{k} {w}" for k, w in o["check"].items()) if o["check"] else "")
                            for o in rep["observations"])
        loss = "; ".join(f"{l['route']} drops {l['construct']} ({'**blocking**' if l['blocking'] else 'not blocking'})" for l in prov["losses"])
        L.append(f"| `{p['name']}` | `{p['status']}` | {cell('cerberus')} | {cell('clang')} | {agree} | {obs} | {loss} |")
    return "\n".join(L) + "\n"


def check(binary):
    bad = reproduced = total = 0
    index = json.load(open(os.path.join(CORPUS, "index.json")))
    for row in index["programs"]:
        name = row["name"]
        out = os.path.join(CORPUS, name)
        rp = os.path.join(out, "report.json")
        if not os.path.exists(rp):
            continue
        stored = json.load(open(rp))
        total += 1
        observes = []
        for o in stored["observations"]:
            t = o["termination"]
            term = t.split()[1] if t.startswith("exit") else ("abort" if t == "abort" else "signal:" + t.split()[1])
            observes += ["--observe", o["name"], term, o["name"].replace("gcc-", "native-") + ".out"]
        routes = [f"{r}={r}.tail.sexp" for r in sorted(stored["routes"])]
        tmp = os.path.join(out, ".check")
        os.makedirs(tmp, exist_ok=True)
        rc, so, se = run([os.path.join(binary, "ctv-pipeline"), "run", RUNTIME, str(stored["fresh"]), ".check"] + observes + routes, out, timeout=1800)
        if rc != 0:
            print(f"{name}: ctv-pipeline failed: {se.decode(errors='replace')[-500:]}"); bad = 1; continue
        fresh = json.loads(so)
        fresh["runtime"] = stored["runtime"]
        for k, v in stored["routes"].items():
            if "coreSha256" in v:
                fresh["routes"][k]["coreSha256"] = file_sha(os.path.join(tmp, f"{k}.core.sexp"))
                fresh["routes"][k]["core"] = v["core"]
        if fresh != stored:
            print(f"{name}: report differs from the stored one"); bad = 1
        else:
            print(f"{name}: stored report and Core documents reproduced")
            reproduced += 1
        shutil.rmtree(tmp)
    print(f"reproduced {reproduced} of {total} stored reports (a reproducibility check of ctv-pipeline on "
          "the stored typed Ail; it validates nothing new)")
    return bad


def main(argv):
    if argv == ["--readme"]:
        write_readme()
        return
    if argv == ["--register"]:
        register()
        return
    if argv and argv[0] == "--check":
        binary = os.path.join(ROOT, ".lake", "build", "bin")
        if len(argv) > 2 and argv[1] == "--bin":
            binary = os.path.abspath(argv[2])
        sys.exit(check(binary))
    binary = os.path.join(ROOT, ".lake", "build", "bin")
    if len(argv) > 1 and argv[0] == "--bin":
        binary, argv = os.path.abspath(argv[1]), argv[2:]
    names = argv or sorted(f[:-2] for f in os.listdir(os.path.join(CORPUS, "src")) if f.endswith(".c"))
    tools = {"gcc": version(["gcc", "--version"]), "clang": version(["clang", "--version"]),
             "cerb-lean": file_sha(os.path.join(binary, "cerb-lean")),
             "cfront": file_sha(os.path.join(binary, "cfront")),
             "ctv-pipeline": file_sha(os.path.join(binary, "ctv-pipeline"))}
    rev = git_rev()
    rows = []
    for n in names:
        name, report, failures = one(n, binary, tools, rev)
        # A verdict that rests only on source undefined behaviour is reported as such, never as a
        # plain validation.
        verdicts = {f'{p["source"]}->{p["target"]}': (p["verdict"] + (" (UB-free source)" if p["validatedUBFree"] else
                    " (only through source UB)" if p["verdict"] == "validated" and p["coveredOnlyByUB"] else
                    " (source UB reached)" if p["verdict"] == "validated" else ""))
                    for p in (report or {}).get("pairs", [])}
        routes = {k: v.get("status") for k, v in (report or {}).get("routes", {}).items()}
        prov = json.load(open(os.path.join(CORPUS, name, "provenance.json")))
        rows.append({"name": name, "routes": routes, "verdicts": verdicts, "failures": sorted(failures),
                     "status": status_of(report, prov), "blockedRoutes": prov["blockedRoutes"]})
        print(f"{name}: routes={routes} verdicts={verdicts} failures={sorted(failures)}", flush=True)
    json.dump({"schema": "silmaril.c-tv.corpus.v1", "tools": tools, "programs": rows},
              open(os.path.join(CORPUS, "index.json"), "w"), indent=1, sort_keys=True)
    open(os.path.join(CORPUS, "index.json"), "a").write("\n")
    write_readme()
    register()


def register():
    """Register every program's source.c and provenance.json in silmaril/artifacts.toml (names
    silmaril.c_tv.corpus.<name>.{source,provenance}), so the project database carries them with
    their SHA-256 and the C tab can compare the bytes it serves with the database's record."""
    reg = os.path.join(ROOT, "silmaril", "artifacts.toml")
    # Drop the previous registrations: each [[artifact]] table up to the next table header.
    out, block = [], None
    for line in open(reg).read().split("\n"):
        if line.startswith("[["):
            if block is not None and not any(l.startswith('name = "silmaril.c_tv.corpus.') for l in block):
                out += block
            block = [line] if line == "[[artifact]]" else None
            if block is None:
                out.append(line)
            continue
        (block if block is not None else out).append(line)
    if block is not None and not any(l.startswith('name = "silmaril.c_tv.corpus.') for l in block):
        out += block
    open(reg, "w").write("\n".join(out).rstrip("\n") + "\n")
    sil = os.path.join(ROOT, "build", "bin", "silmaril-project")
    index = json.load(open(os.path.join(CORPUS, "index.json")))
    for p in index["programs"]:
        for f, kind in [("source.c", "source"), ("provenance.json", "provenance")]:
            rel = os.path.join("examples", "c-programs", p["name"], f)
            rc, so, se = run([sil, "artifacts", "add", rel, "--name", f"silmaril.c_tv.corpus.{p['name']}.{kind}"], ROOT)
            if rc != 0:
                raise SystemExit(f"artifacts add {rel}: {se.decode(errors='replace')}")


MARK = "<!-- corpus tables: generated by scripts/c-tv/corpus.py; edit above this line -->"


def write_readme():
    path = os.path.join(CORPUS, "README.md")
    text = open(path).read()
    head = text.split(MARK)[0]
    open(path, "w").write(head + MARK + "\n\n" + readme_tables())


if __name__ == "__main__":
    main(sys.argv[1:])
