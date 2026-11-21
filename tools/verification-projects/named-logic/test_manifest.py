import copy
import sys
import unittest
from pathlib import Path

import manifest as fixture


class FixtureTest(unittest.TestCase):
    def setUp(self):
        self.manifest = fixture.build(PLAN)

    def test_deterministic_and_both_cid_profiles(self):
        fixture.verify(PLAN, self.manifest)
        self.assertEqual(self.manifest, fixture.build(PLAN))
        self.assertEqual(len(self.manifest["rows"]), 7)
        self.assertEqual(fixture.encode(["ctx"]).hex(), "8163637478")
        self.assertEqual(fixture.digest("blake3", b"").hex(),
                         "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262")

    def test_reject_noncanonical_or_unsupported_wire(self):
        for wire in ("780161", "9f6161ff", "61616162", "61ff", "d82a4100", "82106161"):
            with self.subTest(wire=wire), self.assertRaises(ValueError):
                fixture.decode(bytes.fromhex(wire))
        example = ["x" * 256, ["α"] * 30]
        self.assertEqual(fixture.decode(fixture.encode(example)), example)

    def test_digest_failure_and_missing_root(self):
        for profile, blocks in self.manifest["blocks"].items():
            cid = next(iter(blocks))
            with self.subTest(profile=profile):
                altered = copy.deepcopy(self.manifest)
                altered["blocks"][profile][cid]["hex"] += "61"
                with self.assertRaisesRegex(ValueError, "digest mismatch"):
                    fixture.verify(PLAN, altered)
                missing = copy.deepcopy(self.manifest)
                del missing["blocks"][profile][cid]
                with self.assertRaisesRegex(ValueError, "missing root block"):
                    fixture.verify(PLAN, missing)

    def test_valid_digest_is_not_the_right_row_or_proof(self):
        first, second = self.manifest["rows"][:2]
        original = first["roots"]["conclusion"]
        first["roots"]["conclusion"] = second["roots"]["conclusion"]
        with self.assertRaisesRegex(ValueError, "different coordinate"):
            fixture.verify(PLAN, self.manifest)
        first["roots"]["conclusion"] = original
        first["evidence"]["declaration"] = "forged"
        with self.assertRaisesRegex(ValueError, "evidence or scope"):
            fixture.verify(PLAN, self.manifest)

    def test_never_cross_profiles(self):
        first = self.manifest["rows"][0]["roots"]["conclusion"]
        alternate = first["alternates"]["bdasl-inline-blake3"]
        block = self.manifest["blocks"]["bdasl-inline-blake3"][alternate]
        self.manifest["blocks"]["bdasl-inline-sha256"][alternate] = block
        with self.assertRaisesRegex(ValueError, "envelope does not match profile"):
            fixture.verify(PLAN, self.manifest)


if __name__ == "__main__":
    PLAN = fixture.load(Path(sys.argv.pop(1)))
    unittest.main()
