"""The GCC torture manifest and stored TV report invariants (scripts/c-tv/check-torture.py), in the
CI helpers job: no GCC checkout, compiler or native run is needed."""
import os
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))


CHECK = os.path.join(HERE, "c-tv", "check-torture.py")
REPORT = os.path.join(os.path.dirname(HERE), "benchmarks", "gcc-torture", "tv-report.json.gz")


def forge(j, pairs, endings=True):
    """Turn an elaborator-rejected row into a cross-validated one, with the summary moved to match."""
    r = next(r for r in j["cases"] if r["status"] == "elaborator-rejected")
    part = r["case"].split("/")[0] + "/"
    r.update(status="cross-validated", pairs=pairs)
    if endings:
        r["endings"] = {"cerberus": ['{"exit": 0, "kind": "defined"}'], "clang": ['{"exit": 0, "kind": "defined"}']}
    for d in (j["summary"], j["summary"][part]):
        d["elaborator-rejected"] -= 1
        d["cross-validated"] += 1


def check(*args):
    return subprocess.run([sys.executable, "-I", CHECK, *args], capture_output=True, text=True)


class TortureInvariants(unittest.TestCase):
    """A structurally valid forged row (both pairs, both endings, summary moved) still passes: the
    checker keeps the stored report self-consistent and tied to the manifest, it does not
    authenticate it (scripts/c-tv/check-torture.py, "What it cannot do")."""
    def test_manifest_and_report(self):
        p = check()
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)

    def test_tampered_reports_are_rejected(self):
        import gzip, json, tempfile
        base = json.load(gzip.open(REPORT))
        tamper = {
            "drop a row": lambda j: j["cases"].pop(),
            "duplicate a case": lambda j: j["cases"].insert(1, j["cases"][0]),
            "fake cross-validation": lambda j: j["cases"][5].update(status="cross-validated"),
            "wrong source hash": lambda j: j["cases"][5].update(sha256="0" * 64),
            "inflated summary": lambda j: j["summary"].update({"cross-validated": j["summary"]["cross-validated"] + 1}),
            "unpinned profile": lambda j: j["options"].pop("pipeline"),
            "unknown status": lambda j: j["cases"][5].update(status="validated"),
            "unknown flag": lambda j: j["cases"][5].update(coverage=True),
            # From the review of #950 (00260e8f):
            "cross-validated-ub without UB": lambda j: next(r for r in j["cases"] if r["status"] == "cross-validated").update(status="cross-validated-ub"),
            "inflated ubReached": lambda j: j["summary"].update(ubReached=j["summary"]["ubReached"] + 100),
            "inflated blocked": lambda j: j["summary"].update(blocked=j["summary"]["blocked"] + 100),
            "inflated profileIncoherent": lambda j: j["summary"].update(profileIncoherent=j["summary"]["profileIncoherent"] + 100),
            "inflated coreAllowsPass": lambda j: j["summary"]["coreAllowsPass"].update(admitted=j["summary"]["coreAllowsPass"]["admitted"] + 1),
            "forged pair keys": lambda j: forge(j, {"a": "validated", "b": "validated"}),
            "forged row without endings": lambda j: forge(j, {"cerberus->clang": "validated", "clang->cerberus": "validated"}, endings=False),
            "flag of the wrong type": lambda j: j["cases"][5].update(compileOnly="yes"),
        }
        with tempfile.TemporaryDirectory() as d:
            for name, f in tamper.items():
                j = json.loads(json.dumps(base))
                f(j)
                path = os.path.join(d, "r.json.gz")
                with gzip.open(path, "wb") as out:
                    out.write(json.dumps(j).encode())
                self.assertNotEqual(check("--report", path).returncode, 0, name)


if __name__ == "__main__":
    unittest.main()
