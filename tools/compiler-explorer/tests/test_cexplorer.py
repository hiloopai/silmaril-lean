#!/usr/bin/env python3
"""Tests of the compiler explorer's database and API (python3 -I, standard library only).

The evidence files here are written by the tests in the exporter's format, to test what the
database accepts and how it computes statuses; tools/compiler-explorer/check.sh runs the real
exporter on the real Lean build.
"""

from __future__ import annotations

import copy
import http.client
import importlib.util
import json
import pathlib
import os
import subprocess
import shutil
import sqlite3
import struct
import tempfile
import threading
import unittest

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("cexplorer", HERE.parent / "cexplorer.py")
cx = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cx)

ROOT = cx.ROOT
MANIFESTS = ROOT / "examples" / "compiler-explorer" / "manifests"
STRAIGHT_O0 = MANIFESTS / "compiles-to--straight--O0--add3.json"
STRAIGHT_O2 = MANIFESTS / "compiles-to--straight--O2--add3.json"
BRANCH_O2 = MANIFESTS / "compiles-to--branch--O2--max2.json"
MSORT_O2 = MANIFESTS / "programs--msort--O2.json"
LOOP_O0 = MANIFESTS / "compiles-to--loop--O0--sum_to.json"


def evidence_for(manifest_path: pathlib.Path, status_of=lambda o: "kernel", edit=None) -> dict:
    """Evidence in the exporter's format: every obligation with a declaration gets `status_of`."""
    m = json.loads(manifest_path.read_bytes())
    obls = []
    for o in m["obligations"]:
        if o.get("statement") is None:
            continue
        if o.get("decl") is None:
            obls.append({"id": o["id"], "statement": o["statement"], "decl": None, "status": "open"})
        else:
            obls.append({"id": o["id"], "statement": o["statement"], "decl": o["decl"],
                         "status": status_of(o), "axioms": ["propext", "Classical.choice", "Quot.sound"],
                         "type": o["statement"]})
    ev = {"schema": cx.EVIDENCE_SCHEMA, "problem": m["id"],
          "manifest_sha256": cx.sha256(manifest_path.read_bytes()),
          "lean_version": "4.37.0-test", "git_commit": "0" * 40,
          "modules": m["lean"]["modules"], "obligations": obls}
    if edit:
        edit(ev)
    return ev


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = pathlib.Path(tempfile.mkdtemp())
        self.db = cx.connect(str(self.tmp / "t.sqlite"))

    def tearDown(self):
        self.db.close()
        shutil.rmtree(self.tmp)

    def write(self, name: str, obj) -> pathlib.Path:
        p = self.tmp / name
        p.write_text(json.dumps(obj, ensure_ascii=False))
        return p

    def trusted(self, path):
        """Record an evidence file as if this tool had run the exporter (`verify`)."""
        return cx.ingest_evidence(self.db, path, origin="exporter-run")

    def statuses(self, pid: str) -> dict:
        return {o["id"]: o["status"] for o in cx.problem_view(self.db, pid)["obligations"]}

    def rejections(self) -> list[str]:
        return [r["reason"] for r in self.db.execute("SELECT reason FROM rejections")]


class Ingest(Base):
    def test_optional_block_identity_and_exact_viewer_entry(self):
        cx.ingest_manifest(self.db, STRAIGHT_O2)
        pid = "compiles-to/straight/O2/add3"
        problem = cx.problem_view(self.db, pid)
        block, = problem["extra"]["blocks"]
        self.assertEqual(block["side"], "target")
        self.assertEqual(block["elf_sha256"], problem["artifacts"]["target"]["sha256"])
        self.assertEqual(block["section_range"], [0, 6])
        self.assertEqual(block["file_range"], [64, 70])
        self.assertEqual(block["parse_stage"]["output_sha256"], problem["artifacts"]["ail"]["sha256"])
        self.assertEqual(block["dependencies"], ["artifact", "decoding"])
        self.assertEqual(len(block["attribution"]), 3)
        self.assertNotIn("viewer", block)
        entry = {**block, "problem": pid}
        catalog = ("../", {block["elf_sha256"]: {"blocks": {block["id"]: entry}}})
        self.assertTrue(cx.problem_view(self.db, pid, catalog)["extra"]["blocks"][0]["viewer"].endswith(block["id"]))
        entry["model_base"] += 1
        self.assertNotIn("viewer", cx.problem_view(self.db, pid, catalog)["extra"]["blocks"][0])

    def test_block_does_not_make_a_semantic_attribution(self):
        manifest = json.loads(STRAIGHT_O2.read_bytes())
        manifest["blocks"][0]["attribution"] = ["seg/add3/0"]
        with self.assertRaisesRegex(cx.Rejected, "must be navigation"):
            cx.ingest_manifest(self.db, self.write("invalid-block.json", manifest))
        manifest = json.loads(STRAIGHT_O2.read_bytes())
        manifest["blocks"][0]["section_range"] = [0, 5]
        with self.assertRaisesRegex(cx.Rejected, "does not match the decoded listing"):
            cx.ingest_manifest(self.db, self.write("truncated-block.json", manifest))
        manifest = json.loads(STRAIGHT_O2.read_bytes())
        manifest["blocks"][0]["model_base"] += 1
        with self.assertRaisesRegex(cx.Rejected, "must refer to the bound listing and symbol"):
            cx.ingest_manifest(self.db, self.write("shifted-model-entry.json", manifest))

    def test_block_cannot_reuse_function_evidence_for_an_unbound_section_slice(self):
        manifest = json.loads(STRAIGHT_O2.read_bytes())
        blobs = {role: cx.read_artifact(ROOT, ref) for role, ref in manifest["artifacts"].items()}
        elf = bytearray(blobs["target"])
        section, _, size = cx.elf_text_location(elf)
        table, = struct.unpack_from("<Q", elf, 0x28)
        struct.pack_into("<Q", elf, table + 64 * section + 32, size + 1)
        blobs["target"] = bytes(elf)
        with self.assertRaisesRegex(ValueError, "smaller slices need a symbol-offset binding"):
            cx.block_endpoints(manifest, blobs)

    def test_block_can_be_on_the_left_without_semantics_or_a_parse(self):
        manifest = json.loads(STRAIGHT_O2.read_bytes())
        opposite = {"source": "target", "target": "source"}
        arts = manifest["artifacts"]
        arts["source"], arts["target"] = arts["target"], arts["source"]
        manifest["id"] = "test/reversed-block"
        manifest["direction"] = "imported"
        manifest["derivation"] = None
        manifest["context"] = {}
        manifest["relation"] = {"semantics": "none"}
        manifest["lean"] = {"family": None, "modules": []}
        manifest["obligations"] = []
        manifest["view"] = {"source": "listing", "target": "target"}
        for frag in manifest["fragments"]:
            frag["artifact"] = opposite[frag["artifact"]]
        manifest["edges"] = [e for e in manifest["edges"] if e["kind"] == "navigation"]
        for edge in manifest["edges"]:
            edge["source"], edge["target"] = edge["target"], edge["source"]
        arts.pop("listing_receipt")
        arts.pop("compact")
        arts.pop("compact_origins")
        for field in ("dwarf_extraction", "dwarf_facts", "include_env"):
            manifest.pop(field)
        block, = manifest["blocks"]
        block["side"] = "source"
        for field in ("object_obligation", "render", "parse"):
            block.pop(field)
        manifest["stages"] = [{"side": "source", "input": "source", "output": "decoded", "trust": "trusted"}]
        cx.ingest_manifest(self.db, self.write("reversed.json", manifest))
        problem = cx.problem_view(self.db, manifest["id"])
        block, = problem["extra"]["blocks"]
        self.assertEqual(block["side"], "source")
        self.assertFalse(block["dependencies"])
        self.assertIsNone(block["parse_stage"])
        self.assertFalse(problem["obligations"])

    def test_proved_only_with_evidence(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        before = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(before["translation"], "unchecked")  # a proof is named, nothing checked
        self.assertEqual(before["nonvacuity/universal"], "open")
        self.trusted(self.write("ev.json", evidence_for(STRAIGHT_O0)))
        after = self.statuses("compiles-to/straight/O0/add3")
        for k in ("translation", "mapping", "refinement", "abi", "edge/0", "edge/4", "point/2", "artifact"):
            self.assertEqual(after[k], "proved", k)
        self.assertEqual(after["nonvacuity/universal"], "open")

    def test_open_mapping_with_proved_refinement(self):
        cx.ingest_manifest(self.db, BRANCH_O2)
        self.trusted(self.write("ev.json", evidence_for(BRANCH_O2)))
        st = self.statuses("compiles-to/branch/O2/max2")
        for k in ("refinement", "abi", "nonvacuity"):
            self.assertEqual(st[k], "proved", k)
        for k in ("edge/0", "mapping", "translation"):
            self.assertEqual(st[k], "open", k)

    def test_exporter_mismatch_is_rejected_status(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        ev = evidence_for(STRAIGHT_O0, lambda o: "mismatch" if o["id"] == "edge/1" else "kernel")
        self.trusted(self.write("ev.json", ev))
        st = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(st["edge/1"], "rejected")
        self.assertEqual(st["edge/0"], "proved")

    def test_unsupported_and_tests_never_prove(self):
        cx.ingest_manifest(self.db, MSORT_O2)
        v = cx.problem_view(self.db, "programs/msort/O2")
        self.assertTrue(all(o["status"] == "unsupported" for o in v["obligations"]))
        self.assertEqual([t["status"] for t in v["tests"]], ["passed"])
        self.assertEqual({q["status"] for k, q in v["questions"].items() if q and k != "edges"}, {"unsupported"})
        self.assertEqual(v["questions"]["edges"]["proved"], 0)
        cx.ingest_manifest(self.db, LOOP_O0)
        self.assertEqual(set(self.statuses("compiles-to/loop/O0/sum_to").values()), {"unsupported"})

    def test_execution_test_compares_with_the_expected_output(self):
        m = json.loads(MSORT_O2.read_bytes())
        m["tests"][0]["expected_stdout"] = "8 7 6 5 4 3 2 1\n"
        cx.ingest_manifest(self.db, self.write("m.json", m))
        self.assertEqual([t["status"] for t in cx.problem_view(self.db, "programs/msort/O2")["tests"]], ["failed"])

    def test_reingest_is_idempotent_and_migrations_rerun(self):
        a = cx.ingest_manifest(self.db, STRAIGHT_O0)
        b = cx.ingest_manifest(self.db, STRAIGHT_O0)
        self.assertEqual(a, b)
        cx.migrate(self.db)
        self.assertEqual([r[0] for r in self.db.execute("SELECT version FROM schema_migrations")], [1, 2, 3, 4, 5, 6])

    def test_migration_keeps_existing_data(self):
        path = str(self.tmp / "old.sqlite")
        old = sqlite3.connect(path)
        old.execute("CREATE TABLE schema_migrations (version INTEGER PRIMARY KEY)")
        old.executescript("BEGIN;" + cx.MIGRATIONS[0] + "INSERT INTO schema_migrations VALUES (1); COMMIT;")
        old.close()
        db = cx.connect(path)  # migrates 2 and 3
        vid = cx.ingest_manifest(db, STRAIGHT_O0)
        self.assertEqual([r[0] for r in db.execute("SELECT version FROM schema_migrations")], [1, 2, 3, 4, 5, 6])
        self.assertTrue(db.execute("SELECT row FROM obligations WHERE version_id = ? AND id = 'translation'",
                                   (vid,)).fetchone()[0])
        db.close()

    def test_artifacts_are_immutable(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        with self.assertRaises(sqlite3.IntegrityError):
            with self.db:
                sha = self.db.execute("SELECT sha256 FROM artifacts LIMIT 1").fetchone()[0]
                self.db.execute("INSERT INTO artifacts VALUES (?, 1, x'00')", (sha,))


class ManyToMany(Base):
    def test_inlined_line_maps_to_several_ranges_and_functions(self):
        cx.ingest_manifest(self.db, MSORT_O2)
        v = cx.problem_view(self.db, "programs/msort/O2")
        src = v["texts"]["source"].split("\n")
        line8 = [e for e in v["edges"] if e["id"].endswith("/8")]
        # `merge` is inlined: its line 8 has code in `msort` (and possibly in `main`)
        self.assertTrue(any(e["function"] == "msort" for e in line8))
        self.assertIn("tmp[k++] = (a[i] <= a[j])", src[7])
        frag = v["fragments"][line8[0]["target"][0]]
        self.assertGreater(len(frag["ranges"]), 1, "a discontiguous target fragment")
        # the call `merge(a, tmp, lo, mid, hi);` (line 24) has no code of its own once inlined
        lines_with_edges = {int(e["id"].rsplit("/", 1)[1]) for e in v["edges"]}
        self.assertNotIn(24, lines_with_edges)

    def test_duplicated_line_in_several_functions(self):
        lisp = MANIFESTS / "programs--lisp--O2.json"
        cx.ingest_manifest(self.db, lisp)
        v = cx.problem_view(self.db, "programs/lisp/O2")
        by_src = {}
        for e in v["edges"]:
            for f in e["source"]:
                by_src.setdefault(f, set()).add(e["function"])
        # `cons` (and `mk`) are inlined into both `read` and `eval`: one source line, two copies
        self.assertTrue(any(len(fns) > 1 for fns in by_src.values()))
        self.assertIn("/usr/include/x86_64-linux-gnu/bits/stdio.h",
                      v["extra"]["navigation_stats"]["instructions_from_other_files"])

    def test_navigation_and_semantic_edges_are_distinct(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        v = cx.problem_view(self.db, "compiles-to/straight/O0/add3")
        kinds = {e["kind"] for e in v["edges"]}
        self.assertEqual(kinds, {"navigation", "semantic"})
        for o in v["obligations"]:
            if o["edge"]:
                self.assertTrue(o["edge"].startswith("seg/"), "obligations attach to semantic edges only")

    def test_fragment_ids_are_content_addresses(self):
        m = json.loads(STRAIGHT_O0.read_bytes())
        src = m["artifacts"]["source"]["sha256"]
        f = next(f for f in m["fragments"] if f["artifact"] == "source")
        self.assertEqual(f["id"], cx.fragment_id(src, f["space"], f["ranges"]))


class Rejections(Base):
    def manifest(self, edit) -> pathlib.Path:
        m = json.loads(STRAIGHT_O0.read_bytes())
        edit(m)
        return self.write("m.json", m)

    def assertRejected(self, path, fn=None):
        with self.assertRaises(cx.Rejected):
            (fn or cx.ingest_manifest)(self.db, path)
        self.assertTrue(self.rejections())

    def test_statement_must_be_the_template(self):
        def edit(m):
            o = next(o for o in m["obligations"] if o["id"] == "edge/1")
            o["statement"] = "True"
            o["decl"] = "trivial"
        self.assertRejected(self.manifest(edit))

    def test_edge_statement_about_another_point(self):
        def edit(m):
            a = next(o for o in m["obligations"] if o["id"] == "edge/1")
            b = next(o for o in m["obligations"] if o["id"] == "edge/2")
            a["statement"] = b["statement"]
        self.assertRejected(self.manifest(edit))

    def test_forged_fragment_id(self):
        def edit(m):
            m["fragments"][0]["ranges"][0][1] += 1
        self.assertRejected(self.manifest(edit))

    def test_receipt_about_other_bytes(self):
        def edit(m):
            m["artifacts"]["receipt"] = m["artifacts"]["listing_receipt"]
        self.assertRejected(self.manifest(edit))

    def test_registry_names_another_artifact(self):
        def edit(m):
            m["lean"]["registry"]["target"] = "silmaril.compiles_to.straight.o2.object"
        self.assertRejected(self.manifest(edit))

    def test_lean_names_must_be_identifiers(self):
        def edit(m):
            m["lean"]["vars"]["target_value"] = "True"
            for o in m["obligations"]:
                if o["kind"] == "artifact":
                    o["statement"] = "True"
        self.assertRejected(self.manifest(edit))
        self.assertRejected(self.manifest(lambda m: m["lean"]["vars"].update(fn="(fun _ => True) x")))

    def test_target_value_must_read_the_target(self):
        def edit(m):
            m["lean"]["vars"]["target_value"] = "silmaril.compiles_to.straight.o2.obj"
            for o in m["obligations"]:
                if o["kind"] == "artifact":
                    o["statement"] = o["statement"].replace(".o0.obj", ".o2.obj")
        self.assertRejected(self.manifest(edit))

    def test_statement_model_is_the_context_model(self):
        self.assertRejected(self.manifest(lambda m: m["lean"]["vars"].update(isa="Silmaril.X86.Open9.isa")))

    def test_view_names_artifacts(self):
        self.assertRejected(self.manifest(lambda m: m["view"].update(target="nope")))

    def test_duplicate_fragment(self):
        self.assertRejected(self.manifest(lambda m: m["fragments"].append(dict(m["fragments"][0]))))

    def test_symlink_out_of_the_repository(self):
        root = self.tmp / "root"
        root.mkdir()
        outside = self.tmp / "secret.txt"
        outside.write_text("secret")
        (root / "link.txt").symlink_to(outside)
        with self.assertRaises(ValueError):
            cx.read_artifact(root, {"path": "link.txt", "sha256": cx.sha256(b"secret"), "size": 6})

    def test_unknown_direction(self):
        self.assertRejected(self.manifest(lambda m: m.update(direction="guessed")))

    def test_artifact_path_escape(self):
        def edit(m):
            m["artifacts"]["source"]["path"] = "../etc/passwd"
        self.assertRejected(self.manifest(edit))

    def test_changed_source_bytes(self):
        root = self.tmp / "root"
        m = json.loads(STRAIGHT_O0.read_bytes())
        for ref in m["artifacts"].values():
            dst = root / ref["path"]
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(ROOT / ref["path"], dst)
        (root / "silmaril" / "compiles-to").mkdir(parents=True)
        shutil.copy(ROOT / "silmaril" / "artifacts.toml", root / "silmaril")
        shutil.copy(ROOT / "silmaril" / "compiles-to" / "straight.toml", root / "silmaril" / "compiles-to")
        cx.ingest_manifest(self.db, STRAIGHT_O0, root=root)  # the copies are the manifest's bytes
        src = root / m["artifacts"]["source"]["path"]
        src.write_text(src.read_text().replace("int t = s + c;", "int t = s - c;"))
        with self.assertRaises(cx.Rejected):
            cx.ingest_manifest(self.db, self.write("m2.json", dict(m, title="x")), root=root)


class Project(Base):
    """The adapter to a `sil project` database, on the real schema: the golden database of
    tools/silmaril-project/tests/project/ok, plus the rows of one build."""

    def project_db(self, edit=None) -> pathlib.Path:
        path = self.tmp / "project.sqlite"
        pdb = sqlite3.connect(path)
        pdb.executescript((ROOT / "tools" / "silmaril-project" / "tests" / "project" / "ok" /
                           "project.sql").read_text())
        m = json.loads(STRAIGHT_O0.read_bytes())
        fn = m["lean"]["vars"]["fn"]
        edges = {e["id"]: e for e in m["edges"]}
        shapes = {k: v[0] for k, v in cx.ROW_SHAPES["c-function-x86"].items()}
        for o in m["obligations"]:
            if not o.get("row"):
                continue
            row = o["row"]
            pdb.execute("INSERT INTO problems (sid, name, kind, decl, module, origin, detached) "
                        "VALUES (?, ?, 'prop', ?, 'CompilesToExamples.Explorer.Rows', 'local', 0)",
                        (cx.sha256(row.encode()), row, row))
            pdb.execute("INSERT INTO edges VALUES ('instance', ?, 0, ?, ?, 'instance', ?)",
                        (row, shapes[o["kind"]], row, row))
            point = edges[o["edge"]]["point"] if o.get("edge") else None
            args = cx.ROW_SHAPES["c-function-x86"][o["kind"]][1](m["lean"]["vars"], point)
            for i, a in enumerate(args):
                    pdb.execute("INSERT INTO instance_args VALUES (?, ?, ?, NULL, NULL)", (row, i, a))
            decl = row.replace("silmaril.", "Rows.")
            pdb.execute("INSERT INTO statuses VALUES (?, 'THM', 'solves', ?, 'kernel')", (row, decl))
            for ax in ("propext", "Classical.choice", "Quot.sound"):
                pdb.execute("INSERT INTO answer_axioms VALUES (?, ?)", (decl, ax))
        if edit:
            edit(pdb)
        pdb.commit()
        pdb.close()
        return path

    def test_static_pages_preserve_project_evidence_and_missing(self):
        spec = importlib.util.spec_from_file_location("compiler_pages", HERE.parent / "pages.py")
        pages = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(pages)
        output = self.tmp / "site"
        # This isolated fixture adapter DB has no corpus catalog. Production Pages
        # keeps include_corpus=True; actual corpus coverage has its own tests.
        pages.export(self.project_db(), output, include_corpus=False)
        listing = json.loads((output / "api/problems.json").read_text())
        self.assertEqual(len(listing), len(list(MANIFESTS.glob("*.json"))))
        views = {}
        for item in listing:
            self.assertRegex(item['static_path'], r'^api/problems/[0-9a-f]{64}\.json$')
            views[item['id']] = json.loads((output / item['static_path']).read_text())
            self.assertEqual(views[item['id']]['id'], item['id'])
        view = views['compiles-to/straight/O0/add3']
        translation = next(o for o in view['obligations'] if o['kind'] == 'translation')
        self.assertEqual(translation['status'], 'proved')
        self.assertEqual(view['manifest_sha256'], cx.sha256(STRAIGHT_O0.read_bytes()))
        other = views['compiles-to/straight/O2/add3']
        absent = next(o for o in other['obligations'] if o['kind'] == 'translation')
        self.assertEqual(absent['status'], 'unavailable')
        self.assertNotIn('evidence', absent)
        self.assertFalse(absent['links'])
        self.assertNotIn('rejected', [o['status'] for o in other['obligations']])
        missing = views['programs/msort/O2']
        self.assertNotIn('proved', [o['status'] for o in missing['obligations']])
        self.assertIn('not every corpus function', (output / 'index.html').read_text())
        # A repeated Pages build must refresh evidence rather than keep a prior proof.
        project = sqlite3.connect(self.tmp / 'project.sqlite')
        project.execute("DELETE FROM statuses WHERE problem LIKE 'silmaril.compiler_explorer.%'")
        project.commit()
        project.close()
        pages.export(self.tmp / 'project.sqlite', output, include_corpus=False)
        refreshed = json.loads((output / next(p['static_path'] for p in listing if p['id'] == view['id'])).read_text())
        self.assertNotIn('proved', [o['status'] for o in refreshed['obligations']])

    def test_rows_prove_with_artifact_binding(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        cx.ingest_project(self.db, self.project_db())
        st = self.statuses("compiles-to/straight/O0/add3")
        for k in ("artifact", "translation", "mapping", "refinement", "nonvacuity", "edge/3"):
            self.assertEqual(st[k], "proved", k)
        self.assertEqual(st["abi"], "unchecked")  # no row, no exporter result

    def test_without_the_code_row_everything_is_unbound(self):
        def edit(pdb):
            pdb.execute("DELETE FROM statuses WHERE problem LIKE '%.code'")
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        cx.ingest_project(self.db, self.project_db(edit))
        st = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(st["artifact"], "open")
        self.assertEqual(st["translation"], "unbound")

    def test_row_of_another_function_is_a_mismatch(self):
        def edit(pdb):
            pdb.execute("UPDATE instance_args SET term = 'CompilesToExamples.Branch.O0.max2' WHERE pos = 0")
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        cx.ingest_project(self.db, self.project_db(edit))
        st = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(st["translation"], "incompatible")

    def test_local_evidence_is_not_superseded_by_a_later_incompatible_project(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        self.trusted(self.write("ev.json", evidence_for(STRAIGHT_O0)))
        cx.ingest_project(self.db, self.project_db(lambda pdb: pdb.execute("DELETE FROM problems")))
        self.assertEqual(self.statuses("compiles-to/straight/O0/add3")["translation"], "proved")

    def test_open_row_and_other_axioms(self):
        def edit(pdb):
            pdb.execute("DELETE FROM statuses WHERE problem LIKE '%.mapping'")
            pdb.execute("INSERT INTO answer_axioms SELECT via, 'sorryAx' FROM statuses WHERE problem LIKE '%.translation'")
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        cx.ingest_project(self.db, self.project_db(edit))
        st = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(st["mapping"], "open")
        self.assertEqual(st["translation"], "rejected")

    def test_other_schema_is_refused(self):
        def edit(pdb):
            pdb.execute("UPDATE meta SET value = 'silmaril.project-db.v9' WHERE key = 'schema'")
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        with self.assertRaises(cx.Rejected):
            cx.ingest_project(self.db, self.project_db(edit))


class IncludeTrace(Base):
    def test_program_profiles_load_exact_distinct_trace_receipts(self):
        for opt in ("O0", "O2"):
            path = MANIFESTS / f"programs--msort--{opt}.json"
            cx.ingest_manifest(self.db, path)
            view = cx.problem_view(self.db, f"programs/msort/{opt}")
            env = view["extra"]["include_env"]
            self.assertEqual(env["dependencies"]["flags"].split()[0], f"-{opt}")
            implicit, direct, indirect, *_ = env["trace"]["occurrences"]
            self.assertEqual(implicit["directive"], "implicit")
            self.assertEqual((direct["operand"], direct["literal"], direct["parent"], direct["line"]),
                             ("<stdio.h>", True, None, 2))
            self.assertEqual(indirect["parent"], 1)
            self.assertEqual(indirect["operand"], "<bits/libc-header-start.h>")
            self.assertNotEqual(indirect["operand"].strip("<>"), indirect["resolved"].split("/")[-1])
            self.assertTrue(any(event["resolved"] is None for event in env["trace"]["occurrences"]))

    def test_trace_requires_active_parent_and_exact_dependency_paths(self):
        path = ROOT / "examples/compiler-explorer/env/msort-O2.includes.json"
        receipt = json.loads(path.read_bytes())
        files = {record["path"] for record in receipt["files"]}
        with self.assertRaisesRegex(ValueError, "dependency files"):
            cx.check_include_trace(receipt["trace"], "/src/msort.c", files | {"/elsewhere"})
        receipt["trace"]["occurrences"][2]["parent"] = 0
        with self.assertRaisesRegex(ValueError, "active header entry"):
            cx.check_include_trace(receipt["trace"], "/src/msort.c", files)

    def test_trace_is_tied_to_the_exact_source_and_optimization_profile(self):
        manifest = json.loads(MSORT_O2.read_bytes())
        arts = manifest["artifacts"]
        blobs = {role: cx.read_artifact(ROOT, ref) for role, ref in arts.items()}
        wrong = ROOT / "examples/compiler-explorer/env/msort-O0.includes.json"
        blobs["includes"] = wrong.read_bytes()
        env = manifest["include_env"]
        env["dependencies"]["flags"] = json.loads(blobs["includes"])["flags"]
        env["files"][1:] = [{"name": row["path"], "sha256": row["sha256"], "size": row["size"]}
                            for row in json.loads(blobs["includes"])["files"]]
        with self.assertRaisesRegex(ValueError, "build input and options"):
            cx.check_include_env(env, json.loads(blobs["receipt"]), arts, blobs)


class Directions(Base):
    DECOMPILED = MANIFESTS / "decompiled--scale.json"
    IMPORTED = MANIFESTS / "imported--sha256-compress.json"

    def test_decompiled_and_imported_are_ingested_without_claims(self):
        cx.ingest_manifest(self.db, self.DECOMPILED)
        cx.ingest_manifest(self.db, self.IMPORTED)
        v = cx.problem_view(self.db, "decompiled/scale")
        self.assertEqual(v["direction"], "decompiled")
        st = {o["id"]: o["status"] for o in v["obligations"]}
        self.assertEqual(st.pop("decompilation"), "unchecked")  # stated, not yet checked
        self.assertEqual(set(st.values()), {"unsupported"})
        v = cx.problem_view(self.db, "imported/sha256-compress")
        self.assertEqual({o["status"] for o in v["obligations"]}, {"unsupported"})

    def test_decompiled_block_must_be_the_objects_text(self):
        for edit in (lambda v: v.update(bytes=[0x48, 0x8d, 0x44, 0xfe, 0xfc]),
                     lambda v: v.update(inputs=[["rax", "a"], ["rsi", "b"]]),
                     lambda v: v.update(name="scale; int x")):
            m = json.loads(self.DECOMPILED.read_bytes())
            edit(m["lean"]["vars"])
            with self.assertRaises(cx.Rejected):
                cx.ingest_manifest(self.db, self.write("m.json", m))

    def test_decompiled_statement_is_about_the_source_text(self):
        m = json.loads(self.DECOMPILED.read_bytes())
        o = m["obligations"][0]
        o["statement"] = o["statement"].replace("8ULL", "9ULL")
        with self.assertRaises(cx.Rejected):
            cx.ingest_manifest(self.db, self.write("m.json", m))

    def test_lean_strings_are_escaped(self):
        self.assertEqual(cx.lean_str('a"b\\c\n'), '"a\\"b\\\\c\\n"')
        with self.assertRaises(ValueError):
            cx.lean_str("é")

    def test_decompiler_receipt_must_read_the_target(self):
        m = json.loads(self.DECOMPILED.read_bytes())
        m["artifacts"]["receipt"] = m["artifacts"]["compile_receipt"]
        with self.assertRaises(cx.Rejected):
            cx.ingest_manifest(self.db, self.write("m.json", m))

    def test_imported_cannot_claim_a_checked_derivation(self):
        m = json.loads(self.IMPORTED.read_bytes())
        m["derivation"] = {"kind": "compiler", "compiler": "clang", "version": "18.1.3"}
        with self.assertRaises(cx.Rejected):
            cx.ingest_manifest(self.db, self.write("m.json", m))

    def test_compiled_needs_a_receipt(self):
        m = json.loads(MSORT_O2.read_bytes())
        del m["derivation"]["receipt"]
        with self.assertRaises(cx.Rejected):
            cx.ingest_manifest(self.db, self.write("m.json", m))


class Polish(Base):
    C2C_DROP = MANIFESTS / "c2c--add3_drop.json"
    C2C_REASSOC = MANIFESTS / "c2c--add3_reassoc.json"
    TYPEERR = MANIFESTS / "typeerror--addp.json"

    def test_refuted_open_and_claimed_are_distinct(self):
        cx.ingest_manifest(self.db, self.C2C_DROP)
        cx.ingest_manifest(self.db, self.C2C_REASSOC)
        st = self.statuses("c2c/add3_drop")
        self.assertEqual(st["translation"], "unchecked")  # a refutation is named, not yet checked
        ev = evidence_for(self.C2C_DROP)
        ev["obligations"] = [{"id": "translation", "statement": o["statement"], "decl": None,
                              "refutation": o["refutation"], "status": "refuted",
                              "axioms": ["propext", "Classical.choice", "Quot.sound"],
                              "module": "CompilesToExamples.Explorer.C2C.Runs", "line": 91}
                             for o in json.loads(self.C2C_DROP.read_bytes())["obligations"] if o["id"] == "translation"]
        cx.ingest_evidence(self.db, self.write("file.json", ev))
        self.assertEqual(self.statuses("c2c/add3_drop")["translation"], "claimed")  # a file, not a run
        self.trusted(self.write("ev.json", ev))
        self.assertEqual(self.statuses("c2c/add3_drop")["translation"], "refuted")
        self.trusted(self.write("ev2.json", evidence_for(self.C2C_REASSOC)))
        st = self.statuses("c2c/add3_reassoc")
        self.assertEqual((st["translation"], st["equivalence"]), ("open", "open"))  # unknown, not refuted

    def test_refutation_cannot_prove_and_proof_cannot_refute(self):
        cx.ingest_manifest(self.db, self.C2C_DROP)
        m = json.loads(self.C2C_DROP.read_bytes())
        o = m["obligations"][0]
        bad = [{"id": o["id"], "statement": o["statement"], "decl": None, "refutation": o["refutation"],
                "status": "kernel", "axioms": []}]
        ev = evidence_for(self.C2C_DROP, edit=lambda e: e.update(obligations=bad))
        with self.assertRaises(cx.Rejected):
            self.trusted(self.write("ev.json", ev))
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        ev = evidence_for(STRAIGHT_O0, edit=lambda e: e["obligations"][0].update(status="refuted"))
        with self.assertRaises(cx.Rejected):
            self.trusted(self.write("ev2.json", ev))

    def test_type_error_certificate_is_a_restricted_refutation(self):
        cx.ingest_manifest(self.db, self.TYPEERR)
        v = cx.problem_view(self.db, "typeerror/addp")
        self.assertEqual(v["direction"], "none")
        self.assertEqual(v["extra"]["problem_form"], "judgment")
        typing = next(o for o in v["obligations"] if o["kind"] == "typing")
        self.assertIn("AdditionFragment.Accepts", typing["statement"])
        self.assertIn(cx.lean_str(v["texts"]["source"]), typing["statement"])
        self.assertTrue(typing["refutation"].endswith("addp_type_error"))
        link = next(o for o in v["obligations"] if o["kind"] == "operand_types")
        self.assertIn("AdditionFragment.operands", link["statement"])
        self.assertTrue(link["decl"].endswith("addp_parses"))

    def test_no_semantics_relation(self):
        cx.ingest_manifest(self.db, MSORT_O2)
        v = cx.problem_view(self.db, "programs/msort/O2")
        self.assertEqual(v["extra"]["problem_form"], "relation")
        self.assertEqual(v["extra"]["relation"]["semantics"], "none")
        self.assertTrue(all(o["status"] == "unsupported" for o in v["obligations"]))
        env = v["extra"]["include_env"]
        self.assertTrue(any(f["name"].endswith("stdio.h") and len(f["sha256"]) == 64 for f in env["files"]))
        self.assertTrue(env["search"])
        self.assertIn("macros", v["artifacts"])

    def test_alternative_views_and_stages(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        v = cx.problem_view(self.db, "compiles-to/straight/O0/add3")
        alts = {a["role"] for side in ("source", "target") for a in v["view"]["alternatives"][side]}
        self.assertEqual(alts, {"source", "ail", "core", "compact", "target", "listing", "decoded"})
        self.assertTrue(v["alt_texts"]["ail"].startswith("($tuple "))
        self.assertTrue(v["alt_texts"]["core"].startswith("($document "))
        self.assertNotEqual(v["artifacts"]["ail"]["sha256"], v["artifacts"]["core"]["sha256"])
        self.assertIn("decodesAs", v["alt_texts"]["decoded"])
        self.assertTrue(v["alt_texts"]["target"].startswith("00000000  7f 45 4c 46"))
        trusts = {s["name"]: s["trust"] for s in v["extra"]["stages"]}
        self.assertEqual(trusts["objdump -d (binutils 2.40)"], "trusted")
        self.assertIn("verified", trusts.values())
        stages = {stage["output"]: stage for stage in v["extra"]["stages"]}
        self.assertEqual((stages["ail"]["input"], stages["ail"]["trust"]), ("source", "evaluated"))
        self.assertNotIn("obligation", stages["ail"])
        self.assertEqual((stages["core"]["input"], stages["core"]["trust"]), ("ail", "verified"))
        equality = next(obl for obl in v["obligations"] if obl["id"] == stages["core"]["obligation"])
        self.assertEqual(equality["statement"], cx.core_equality("CompilesToExamples.Straight"))
        self.assertEqual((stages["compact"]["input"], stages["compact"]["origin_table"]), ("ail", "compact_origins"))
        projection = next(obl for obl in v["obligations"] if obl["id"] == "compact_projection")
        self.assertEqual(projection["status"], "unchecked")
        self.assertTrue(v["alt_texts"]["compact"].startswith("(compact-c-i32-v1 3 "))
        facts = v["extra"]["dwarf_facts"]
        self.assertTrue(any(f["kind"] == "frame_slot" and "refinement" in f["used_by"] for f in facts))

    def test_executed_rendering_must_match_every_named_artifact(self):
        manifest = json.loads(STRAIGHT_O0.read_bytes())
        bindings = {role: cx.read_artifact(ROOT, manifest["artifacts"][role]).decode()
                    for role, _ in manifest["lean"]["bindings"]}
        cx.check_rendered_artifacts(self.db, STRAIGHT_O0, manifest, {"artifacts": bindings})
        swapped = {**bindings, "ail": bindings["core"], "core": bindings["ail"]}
        with self.assertRaisesRegex(cx.Rejected, "ail: artifact bytes differ"):
            cx.check_rendered_artifacts(self.db, STRAIGHT_O0, manifest, {"artifacts": swapped})
        bindings["decoded"] += "\n"
        with self.assertRaisesRegex(cx.Rejected, "decoded: artifact bytes differ"):
            cx.check_rendered_artifacts(self.db, STRAIGHT_O0, manifest, {"artifacts": bindings})
        bindings["decoded"] = bindings["decoded"].removesuffix("\n")
        with self.assertRaisesRegex(cx.Rejected, "compact_origins: artifact bytes differ"):
            cx.check_rendered_artifacts(self.db, STRAIGHT_O0, manifest,
                                        {"artifacts": {**bindings, "compact_origins": bindings["compact"]}})
        with self.assertRaisesRegex(cx.Rejected, "exactly the named artifact bindings"):
            cx.check_rendered_artifacts(self.db, STRAIGHT_O0, manifest, {"artifacts": {}})

    def test_c2c_assigns_each_stage_its_own_values_and_equality(self):
        cx.ingest_manifest(self.db, self.C2C_DROP)
        problem = cx.problem_view(self.db, "c2c/add3_drop")
        for side, prefix, namespace in [("source", "", "CompilesToExamples.Straight"),
                                        ("target", "target_", "CompilesToExamples.Explorer.C2C")]:
            stages = [stage for stage in problem["extra"]["stages"] if stage["side"] == side]
            roles = [side, prefix + "ail", prefix + "core"]
            self.assertEqual([alt["role"] for alt in problem["view"]["alternatives"][side]], roles)
            self.assertEqual([(stage["input"], stage["output"]) for stage in stages], list(zip(roles, roles[1:])))
            self.assertEqual(stages[0]["output_decl"], namespace + ".ail")
            equality = next(obl for obl in problem["obligations"] if obl["id"] == stages[1]["obligation"])
            self.assertEqual(equality["statement"], cx.core_equality(namespace))
            self.assertEqual(equality["status"], "unchecked")
        self.assertEqual(len({artifact["sha256"] for artifact in problem["artifacts"].values()}), 6)

    def test_stage_and_dependency_metadata_cannot_reference_another_input(self):
        for path, change, reason in [
            (STRAIGHT_O0, lambda m: m["stages"][0].update(output="missing"), "not a manifest artifact"),
            (STRAIGHT_O0, lambda m: m["stages"][0].update(trust="verified", obligation="core_elaboration"), "scoped evidence"),
            (STRAIGHT_O0, lambda m: m["stages"][1].update(input="source"), "scoped evidence"),
            (STRAIGHT_O0, lambda m: m["stages"][1].update(obligation="elaboration"), "scoped evidence"),
            (STRAIGHT_O0, lambda m: m["stages"][2].update(origin_table="source"), "scoped evidence"),
            (self.C2C_DROP, lambda m: m["stages"][3].update(obligation="core_elaboration"), "scoped evidence"),
            (self.C2C_DROP, lambda m: m["view"]["alternatives"]["target"].append({"role": "ail"}), "only on its own side"),
            (STRAIGHT_O0, lambda m: m["dwarf_extraction"].update(profile="O2"), "target and profile"),
            (STRAIGHT_O0, lambda m: m["dwarf_facts"][0].update(used_by=["missing"]), "not an obligation"),
            (MSORT_O2, lambda m: m["include_env"]["files"][1].update(sha256="0" * 64), "dependency receipt"),
            (MSORT_O2, lambda m: m["include_env"].update(search=["/tmp"]), "search receipt"),
        ]:
            with self.subTest(reason=reason):
                manifest = json.loads(path.read_bytes())
                change(manifest)
                with self.assertRaisesRegex(cx.Rejected, reason):
                    cx.ingest_manifest(self.db, self.write("changed.json", manifest))

    def test_catalog_routes_are_for_published_exact_bytes(self):
        fixtures_spec = importlib.util.spec_from_file_location("fixtures", HERE.parent / "fixtures.py")
        fixtures = importlib.util.module_from_spec(fixtures_spec)
        fixtures_spec.loader.exec_module(fixtures)
        fixtures.viewer_assets(self.tmp)
        dest = self.tmp / "compiler-artifacts"
        catalog = json.loads((dest / "index.json").read_text())["artifacts"]
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        base = "http://localhost:8991/"
        pid = "compiles-to/straight/O0/add3"
        view = cx.problem_view(self.db, pid, (base, catalog))
        for role, tab in (("source", "c"), ("target", "elf")):
            ref = view["artifacts"][role]
            sha = ref["sha256"]
            self.assertEqual((dest / "bytes" / sha).read_bytes(), (ROOT / ref["path"]).read_bytes())
            self.assertEqual(view["artifact_links"][role][0]["url"], f"{base}#/{tab}-artifact/{sha}")
            catalog[sha]["size"] += 1
        view = cx.problem_view(self.db, pid, (base, catalog))
        self.assertFalse(any(link["kind"] == "viewer" for links in view["artifact_links"].values() for link in links))

    def test_links_only_to_existing_routes_and_clean_commits(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        ev = evidence_for(STRAIGHT_O0)
        for o in ev["obligations"]:
            o.update(module="CompilesToExamples.Explorer.Builds", line=62)
        ev["git_commit"] = "a" * 40
        self.trusted(self.write("ev.json", ev))
        v = cx.problem_view(self.db, "compiles-to/straight/O0/add3")
        tr = next(o for o in v["obligations"] if o["id"] == "translation")
        urls = [l["url"] for l in tr["links"]]
        self.assertIn("https://github.com/hiloopai/silmaril-lean/blob/" + "a" * 40 +
                      "/examples/compiles-to/CompilesToExamples/Explorer/Builds.lean#L62", urls)
        self.assertTrue(any(u.endswith("#/problem/silmaril.compiler_explorer.straight.o0.add3.translation")
                            for u in urls))
        src_links = [l["url"] for l in v["artifact_links"]["source"]]
        self.assertIn("https://github.com/hiloopai/silmaril-lean/blob/" + "a" * 40 +
                      "/examples/compiles-to/straight/straight.c", src_links)
        self.assertTrue(any(u.endswith("#/artifact/silmaril.compiles_to.straight.source") for u in src_links))
        self.assertFalse(any("#/c-program/" in u or "#/elf-file/" in u for u in src_links))
        # a dirty or unknown commit gives no Lean link
        ev["git_commit"] = "a" * 40 + "-dirty"
        self.trusted(self.write("ev2.json", ev))
        v = cx.problem_view(self.db, "compiles-to/straight/O0/add3")
        tr = next(o for o in v["obligations"] if o["id"] == "translation")
        self.assertFalse(any(l["kind"] == "lean" for l in tr["links"]))

    def test_lean_paths(self):
        self.assertEqual(cx.lean_path("Silmaril.Compiler.Explorer.Defs"), "Silmaril/Compiler/Explorer/Defs.lean")
        self.assertIsNone(cx.lean_path("Mathlib.Logic.Basic"))
        self.assertIsNone(cx.lean_path("../etc"))


class Binding(Base):
    def test_function_of_another_build_is_unbound(self):
        """The branch -O2 problem, its statements about straight.c's add3: theorems exist for
        them, but the add3 bytes are not branch.o's, so its machine obligations are unbound."""
        m = json.loads(BRANCH_O2.read_bytes())
        straight = json.loads(STRAIGHT_O0.read_bytes())
        m["lean"]["vars"]["fn"] = straight["lean"]["vars"]["fn"]
        m["lean"]["vars"]["cname"] = "add3"
        decls = {o["id"]: o["decl"] for o in straight["obligations"]}
        for o in m["obligations"]:
            e = next((e for e in m["edges"] if e["id"] == o.get("edge")), None)
            o["statement"] = cx.statement_for("c-function-x86", m["lean"]["vars"], o["kind"],
                                              e and e["point"], e and e.get("line"))
            if o["kind"] not in cx.ARTIFACT_STAGE_KINDS:
                o["decl"] = decls.get(o["id"])
        p = self.write("m.json", m)
        cx.ingest_manifest(self.db, p)
        # the exporter would find every theorem but the artifact one (add3 is not in branch.o)
        ev = evidence_for(p, lambda o: "mismatch" if o["kind"] == "artifact" else "kernel")
        self.trusted(self.write("ev.json", ev))
        st = self.statuses("compiles-to/branch/O2/max2")
        self.assertEqual(st["artifact"], "rejected")
        self.assertEqual(st["translation"], "unbound")
        self.assertEqual([key for key, status in st.items() if status == "proved"],
                         ["core_elaboration", "compact_projection"])


class Evidence(Base):
    def test_handed_in_file_is_only_a_claim(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        cx.ingest_evidence(self.db, self.write("ev.json", evidence_for(STRAIGHT_O0)))
        st = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(st["translation"], "claimed")
        self.assertNotIn("proved", st.values())

    def test_duplicate_obligation(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        ev = evidence_for(STRAIGHT_O0, edit=lambda e: e["obligations"].append(dict(e["obligations"][0])))
        with self.assertRaises(cx.Rejected):
            self.trusted(self.write("ev.json", ev))

    def test_unknown_manifest(self):
        p = self.write("ev.json", evidence_for(STRAIGHT_O0))
        with self.assertRaises(cx.Rejected):
            cx.ingest_evidence(self.db, p)  # the manifest was never ingested

    def test_statement_differs(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        ev = evidence_for(STRAIGHT_O0, edit=lambda e: e["obligations"][0].update(statement="True"))
        with self.assertRaises(cx.Rejected):
            self.trusted(self.write("ev.json", ev))

    def test_kernel_without_declaration(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)

        def edit(e):
            o = next(o for o in e["obligations"] if o["id"] == "nonvacuity/universal")
            o["status"] = "kernel"
        with self.assertRaises(cx.Rejected):
            self.trusted(self.write("ev.json", evidence_for(STRAIGHT_O0, edit=edit)))

    def test_non_standard_axiom(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)

        def edit(e):
            e["obligations"][0]["axioms"] = ["sorryAx"]
        with self.assertRaises(cx.Rejected):
            self.trusted(self.write("ev.json", evidence_for(STRAIGHT_O0, edit=edit)))

    def test_other_modules(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        ev = evidence_for(STRAIGHT_O0, edit=lambda e: e.update(modules=["Other"]))
        with self.assertRaises(cx.Rejected):
            self.trusted(self.write("ev.json", ev))

    def test_evidence_does_not_carry_to_a_new_version(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        self.trusted(self.write("ev.json", evidence_for(STRAIGHT_O0)))
        m = json.loads(STRAIGHT_O0.read_bytes())
        m["context"]["target_model"]["version"] = "another x86-64 model version"
        p2 = self.write("m2.json", m)
        cx.ingest_manifest(self.db, p2)
        st = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(st["translation"], "stale")
        self.assertEqual(st["nonvacuity/universal"], "open")
        v = cx.problem_view(self.db, "compiles-to/straight/O0/add3")
        self.assertEqual(len(v["versions"]), 2)
        # the old evidence file cannot be replayed against the new manifest
        with self.assertRaises(cx.Rejected):
            ev = evidence_for(STRAIGHT_O0)
            ev["manifest_sha256"] = cx.sha256(p2.read_bytes())
            ev["obligations"][0]["statement"] += " "
            self.trusted(self.write("ev2.json", ev))
        self.trusted(self.write("ev3.json", evidence_for(p2)))
        self.assertEqual(self.statuses("compiles-to/straight/O0/add3")["translation"], "proved")


class QuietHandler(cx.Handler):
    def log_message(self, fmt, *args):
        pass


class Server(Base):
    def test_read_only_api(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        self.db.commit()
        QuietHandler.db_path = str(self.tmp / "t.sqlite")
        srv = cx.http.server.ThreadingHTTPServer(("127.0.0.1", 0), QuietHandler)
        threading.Thread(target=srv.serve_forever, daemon=True).start()
        try:
            def req(method, path):
                c = http.client.HTTPConnection("127.0.0.1", srv.server_address[1])
                c.request(method, path)
                r = c.getresponse()
                out = r.status, r.getheader("Content-Security-Policy"), r.read()
                c.close()
                return out
            st, csp, body = req("GET", "/api/problems")
            self.assertEqual(st, 200)
            self.assertIn("default-src 'self'", csp)
            self.assertEqual(json.loads(body)[0]["id"], "compiles-to/straight/O0/add3")
            st, _, body = req("GET", "/api/problems/compiles-to%2Fstraight%2FO0%2Fadd3")
            self.assertEqual(json.loads(body)["questions"]["translation"]["status"], "unchecked")
            self.assertEqual(req("POST", "/api/problems")[0], 405)
            self.assertEqual(req("GET", "/../cexplorer.py")[0], 404)
            self.assertEqual(req("GET", "/api/compile")[0], 404)
            self.assertEqual(req("GET", "/api/problems/nope")[0], 404)
        finally:
            srv.shutdown()
            srv.server_close()

    def test_readonly_connection(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        self.db.commit()
        ro = cx.connect(str(self.tmp / "t.sqlite"), readonly=True)
        with self.assertRaises(sqlite3.OperationalError):
            ro.execute("DELETE FROM evidence")
        ro.close()


class ReplayTests(unittest.TestCase):
    """Exercise scheduling and failure propagation without substituting for kernel replay."""

    def run_replay(self, jobs="4", fail=""):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = pathlib.Path(tmp)
            lake = tmp / "lake"
            lake.write_text("""#!/usr/bin/env python3
import os, signal, sys, time
assert sys.argv[1:4] == ["env", "lean", "-DwarningAsError=true"]
if "SILMARIL_REPLAY_TARGETS" in os.environ:
    if os.environ["REPLAY_FAIL"] == "discovery": sys.exit(1)
    if os.environ["REPLAY_FAIL"] != "empty":
        print(os.environ["SILMARIL_REPLAY_TARGETS"].replace(" ", "\\n"))
    sys.exit(0)
module = os.environ["SILMARIL_REPLAY_MODULE"]
fd = os.open(os.environ["REPLAY_LOG"], os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
os.write(fd, ("start " + module + "\\n").encode())
time.sleep(0.05)
os.write(fd, ("stop " + module + "\\n").encode())
if os.environ["REPLAY_FAIL"] == "signal": os.kill(os.getpid(), signal.SIGTERM)
sys.exit(1 if module == os.environ["REPLAY_FAIL"] else 0)
""")
            lake.chmod(0o755)
            log = tmp / "log"
            result = subprocess.run(["bash", str(HERE.parent / "replay.sh")],
                                    env={**os.environ, "LAKE": str(lake),
                                         "LEAN_REPLAY_JOBS": jobs, "REPLAY_LOG": str(log),
                                         "REPLAY_FAIL": fail}, capture_output=True, text=True,
                                    timeout=15)
            lines = log.read_text().splitlines() if log.exists() else []
            return result, lines

    def test_replay_bound_and_serial_mode(self):
        for jobs in ("1", "4"):
            result, lines = self.run_replay(jobs)
            self.assertEqual(result.returncode, 0, result.stderr)
            active = peak = 0
            starts, stops = [], []
            for line in lines:
                kind, module = line.split()
                if kind == "start":
                    starts.append(module)
                    active += 1
                    peak = max(peak, active)
                else:
                    stops.append(module)
                    active -= 1
            self.assertEqual(len(set(starts)), 18)
            self.assertCountEqual(starts, stops)
            self.assertEqual(active, 0)
            self.assertLessEqual(peak, int(jobs))
            if jobs == "4":
                self.assertGreater(peak, 1)

    def test_replay_failure_is_not_hidden(self):
        failed = "Silmaril.Proofs.Compiler.Explorer.Basic"
        result, lines = self.run_replay(fail=failed)
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn("leanchecker " + failed + ": ok", result.stdout)
        self.assertEqual(sum(line.startswith("stop ") for line in lines), 18)

    def test_replay_rejects_invalid_concurrency(self):
        for jobs in ("0", "-1", "oops"):
            result, lines = self.run_replay(jobs)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(lines, [])

    def test_discovery_failure_or_empty_selection_starts_no_workers(self):
        for fail in ("discovery", "empty"):
            result, lines = self.run_replay(fail=fail)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(lines, [])

    def test_signalled_worker_fails_the_replay(self):
        result, _ = self.run_replay(fail="signal")
        self.assertNotEqual(result.returncode, 0)


if __name__ == "__main__":
    unittest.main(verbosity=1)
