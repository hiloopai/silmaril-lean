"""Real Lake builds and HTTPS S3 transfers; no cloud account or credentials needed."""

import contextlib
import hashlib
import json
import os
import shutil
import ssl
import subprocess
import sys
import tempfile
import threading
import unittest
import xml.etree.ElementTree as ET
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from unittest import mock
from urllib.parse import parse_qs, urlsplit

import lake_cache as cache
from storage import S3

TOOLCHAIN = "leanprover/lean4:nightly-2026-10-30"
REPOSITORY = "example/proofs"


class Bucket(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def reply(self, code, body=b""):
        self.send_response(code)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_PUT(self):
        data = self.rfile.read(int(self.headers["Content-Length"]))
        if self.server.fail_upload and "/a/" in self.path:
            self.reply(503)
            return
        self.server.objects[self.path] = data
        self.server.writes.append((self.path, len(data)))
        self.reply(200)

    def do_GET(self):
        url = urlsplit(self.path)
        query = parse_qs(url.query)
        if query.get("list-type") == ["2"]:
            prefix = query["prefix"][0]
            names = sorted(
                name[8:]
                for name in self.server.objects
                if name.startswith("/bucket/" + prefix)
            )
            start = int(query.get("continuation-token", ["0"])[0])
            page = names[start : start + 2]
            end = start + len(page)
            root = ET.Element(
                "ListBucketResult", xmlns="http://s3.amazonaws.com/doc/2006-03-01/"
            )
            ET.SubElement(root, "Prefix").text = prefix
            ET.SubElement(root, "IsTruncated").text = (
                "true" if end < len(names) else "false"
            )
            if end < len(names) and not self.server.break_pagination:
                ET.SubElement(root, "NextContinuationToken").text = str(end)
            for name in page:
                item = ET.SubElement(root, "Contents")
                ET.SubElement(item, "Key").text = name
                ET.SubElement(item, "Size").text = str(
                    len(self.server.objects["/bucket/" + name])
                )
            self.reply(200, ET.tostring(root))
        elif url.path in self.server.objects:
            self.reply(200, self.server.objects[url.path])
        else:
            self.reply(404)


@contextlib.contextmanager
def bucket(directory):
    cert, key = directory / "cert.pem", directory / "key.pem"
    subprocess.run(
        [
            "openssl",
            "req",
            "-x509",
            "-newkey",
            "rsa:2048",
            "-nodes",
            "-keyout",
            str(key),
            "-out",
            str(cert),
            "-days",
            "1",
            "-subj",
            "/CN=localhost",
            "-addext",
            "subjectAltName=DNS:localhost",
        ],
        check=True,
        capture_output=True,
    )
    server = ThreadingHTTPServer(("localhost", 0), Bucket)
    server.objects, server.writes = {}, []
    server.fail_upload = server.break_pagination = False
    tls = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    tls.minimum_version = ssl.TLSVersion.TLSv1_2
    tls.load_cert_chain(cert, key)
    server.socket = tls.wrap_socket(server.socket, server_side=True)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        with mock.patch.dict(os.environ, {"CURL_CA_BUNDLE": str(cert)}):
            yield (
                server,
                S3(
                    f"https://localhost:{server.server_port}",
                    "bucket",
                    "proofs/v2",
                    "test:secret",
                ),
            )
    finally:
        server.shutdown()
        server.server_close()
        thread.join()


def fixture(root):
    root.mkdir()
    (root / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    (root / "lakefile.toml").write_text(
        'name = "demo"\ndefaultTargets = ["Demo"]\n[[lean_lib]]\nname = "Demo"\n'
    )
    (root / ".gitignore").write_text(".lake/\nbuild/\n")
    (root / "Demo").mkdir()
    (root / "Demo/A.lean").write_text(
        "module\npublic theorem a (n : Nat) : n + 0 = n := by simp\n"
    )
    (root / "Demo/B.lean").write_text(
        "module\npublic theorem b (n : Nat) : 0 + n = n := by simp\n"
    )
    (root / "Demo.lean").write_text(
        "module\npublic import Demo.A\npublic import Demo.B\n"
    )
    subprocess.run(["git", "init", "-q", str(root)], check=True)
    subprocess.run(cache.lake("env", "true"), cwd=root, check=True)
    commit(root)


def commit(root):
    subprocess.run(["git", "add", "."], cwd=root, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=Cache Test",
            "-c",
            "user.email=cache@example.invalid",
            "commit",
            "-qm",
            "test fixture",
        ],
        cwd=root,
        check=True,
    )


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="lake-cache-test-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.root = self.directory / "project"
        self.env = mock.patch.dict(
            os.environ,
            {
                "LAKE_CACHE_DIR": str(self.directory / "cache"),
                "LAKE_ARTIFACT_CACHE": "true",
                "ELAN_TOOLCHAIN": TOOLCHAIN,
            },
        )
        self.env.start()
        self.addCleanup(self.env.stop)
        fixture(self.root)
        self.record = self.root / "build/record"

    def build(self):
        cache.record_build(self.root, REPOSITORY, self.record, ["Demo"])

    def test_incremental_publication_and_real_restore(self):
        self.build()
        with bucket(self.directory) as (server, store):
            first = cache.publish(self.root, REPOSITORY, self.record, store)
            self.assertGreater(first["uploaded"], 2)
            unchanged = cache.publish(self.root, REPOSITORY, self.record, store)
            self.assertEqual(unchanged["uploaded"], 0)
            self.assertEqual(unchanged["artifact_bytes"], 0)
            with (self.root / "Demo/A.lean").open("a") as stream:
                stream.write("public theorem another (n : Nat) : n = n := rfl\n")
            commit(self.root)
            self.build()
            changed = cache.publish(self.root, REPOSITORY, self.record, store)
            self.assertGreater(changed["uploaded"], 0)
            self.assertGreater(changed["reused"], 0)
            self.assertLess(changed["uploaded"], first["uploaded"])
            names = cache.artifact_names(self.record / "outputs.jsonl")
            scope = cache.identity(self.root, REPOSITORY, "")["scope"]
            missing = f"/bucket/proofs/v2/a/{scope}/{next(iter(names))}"
            del server.objects[missing]
            repaired = cache.publish(self.root, REPOSITORY, self.record, store)
            self.assertEqual(repaired["uploaded"], 1)
            self.assertIn(missing, server.objects)
            expected = {
                p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                for p in (self.root / ".lake/build/lib/lean/Demo").glob("*.olean")
            }
            shutil.rmtree(self.root / ".lake/build")
            shutil.rmtree(self.directory / "cache")
            with mock.patch.dict(
                os.environ,
                {
                    "LAKE_CI_ENDPOINT": store.endpoint,
                    "LAKE_CI_BUCKET": store.bucket,
                    "LAKE_CI_PREFIX": store.prefix,
                    "LAKE_CI_KEY": store.key,
                },
            ):
                cache.restore(self.root, REPOSITORY, store)
            restored = subprocess.run(
                cache.lake("build", "--wfail", "Demo"),
                cwd=self.root,
                text=True,
                capture_output=True,
                check=True,
            )
            self.assertNotIn("Built Demo", restored.stdout)
            actual = {
                p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                for p in (self.root / ".lake/build/lib/lean/Demo").glob("*.olean")
            }
            self.assertEqual(actual, expected)

    def test_failed_build_and_changed_mapping_cannot_publish(self):
        self.build()
        with (self.root / "Demo/A.lean").open("a") as stream:
            stream.write("public theorem false_claim : False := by trivial\n")
        commit(self.root)
        with self.assertRaises(subprocess.CalledProcessError):
            self.build()
        self.assertFalse((self.record / "success.json").exists())
        with bucket(self.directory) as (server, store):
            with self.assertRaises(FileNotFoundError):
                cache.publish(self.root, REPOSITORY, self.record, store)
            self.assertEqual(server.writes, [])

    def test_incomplete_inventory_or_failed_upload_never_moves_pointer(self):
        self.build()
        with bucket(self.directory) as (server, store):
            server.fail_upload = True
            with self.assertRaisesRegex(RuntimeError, "503"):
                cache.publish(self.root, REPOSITORY, self.record, store)
            self.assertFalse(any("/r/" in name for name in server.objects))
            server.fail_upload = False
            cache.publish(self.root, REPOSITORY, self.record, store)
            before = list(server.writes)
            server.break_pagination = True
            with self.assertRaisesRegex(ValueError, "continuation"):
                cache.publish(self.root, REPOSITORY, self.record, store)
            self.assertEqual(server.writes, before)

    def test_stale_run_or_mapping_is_rejected(self):
        self.build()
        with bucket(self.directory) as (server, store):
            with (
                mock.patch.dict(os.environ, {"GITHUB_RUN_ID": "new-run"}),
                self.assertRaisesRegex(ValueError, "receipt"),
            ):
                cache.publish(self.root, REPOSITORY, self.record, store)
            with (self.record / "outputs.jsonl").open("a") as stream:
                stream.write('["0000000000000000", null]\n')
            with self.assertRaisesRegex(ValueError, "mapping changed"):
                cache.publish(self.root, REPOSITORY, self.record, store)
            self.assertEqual(server.writes, [])

    def test_vendor_package_has_its_own_mapping_and_scope(self):
        vendor = self.root / "vendor"
        vendor.mkdir()
        (vendor / "lakefile.toml").write_text(
            'name = "vendor"\ndefaultTargets = ["Vendor"]\n[[lean_lib]]\nname = "Vendor"\n'
        )
        (vendor / "Vendor.lean").write_text(
            "module\npublic theorem vendor_fact : 1 = 1 := rfl\n"
        )
        with (self.root / "lakefile.toml").open("a") as stream:
            stream.write('\n[[require]]\nname = "vendor"\npath = "vendor"\n')
        with (self.root / "Demo.lean").open("a") as stream:
            stream.write("public import Vendor\n")
        subprocess.run(cache.lake("update"), cwd=self.root, check=True)
        commit(self.root)
        self.build()
        record = self.root / "build/vendor-record"
        cache.record_build(self.root, REPOSITORY, record, [], "vendor")
        root_names = cache.artifact_names(self.record / "outputs.jsonl")
        vendor_names = cache.artifact_names(record / "outputs.jsonl")
        self.assertTrue(vendor_names)
        self.assertTrue(set(root_names).isdisjoint(vendor_names))
        with bucket(self.directory) as (_, store):
            cache.publish(self.root, REPOSITORY, record, store, "vendor")
            with self.assertRaisesRegex(ValueError, "receipt"):
                cache.publish(self.root, REPOSITORY, record, store)
            with (
                mock.patch.object(
                    cache.platform, "machine", return_value="different-arch"
                ),
                self.assertRaisesRegex(ValueError, "receipt"),
            ):
                cache.publish(self.root, REPOSITORY, record, store, "vendor")


class ValidationTests(unittest.TestCase):
    def test_credentials_are_only_passed_on_stdin(self):
        store = S3(
            "https://example.test",
            "bucket",
            "prefix",
            "id:secret",
            session_token="temporary-token",
        )
        url = store.object_url("a/scope/0000000000000000.art")
        report = {
            "url_effective": url,
            "exitcode": 0,
            "http_code": 200,
            "size_upload": 10,
        }
        result = subprocess.CompletedProcess([], 0, json.dumps(report) + "\n", "")
        with (
            mock.patch.dict(os.environ, {"LAKE_CI_KEY": "id:secret"}),
            mock.patch.object(subprocess, "run", return_value=result) as run,
        ):
            store.upload([("a/scope/0000000000000000.art", Path("/tmp/artifact"))])
        args, kwargs = run.call_args
        self.assertNotIn("id:secret", " ".join(args[0]))
        self.assertIn("id:secret", kwargs["input"])
        self.assertNotIn("LAKE_CI_KEY", kwargs["env"])
        self.assertIn("x-amz-security-token: temporary-token", kwargs["input"])
        self.assertNotIn("temporary-token", repr(store))
        self.assertIn("--disable", args[0])

    def test_download_cannot_send_credentials_to_another_namespace(self):
        env = {
            "LAKE_CI_ENDPOINT": "https://example.test",
            "LAKE_CI_BUCKET": "bucket",
            "LAKE_CI_PREFIX": "prefix",
            "LAKE_CI_KEY": "id:secret",
            "LAKE_CI_CURL_BASE": "https://example.test/bucket/prefix",
        }
        urls = [
            "https://evil.test/bucket/prefix/file",
            "https://example.test/bucket/prefix-other/file",
            "https://example.test/bucket/prefix/../other/file",
            "https://example.test/bucket/prefix/%2e%2e/file",
            "https://example.test/bucket/prefix/file?token=other",
        ]
        with (
            mock.patch.dict(os.environ, env),
            mock.patch.object(subprocess, "run") as run,
        ):
            for url in urls:
                with self.subTest(url=url), self.assertRaises(ValueError):
                    cache.curl_shim(["-L", url])
        run.assert_not_called()

    def test_cli_rejects_untrusted_writers(self):
        for event, ref, repo in [
            ("pull_request", "refs/pull/1/merge", REPOSITORY),
            ("push", "refs/heads/topic", REPOSITORY),
            ("push", "refs/heads/main", "fork/proofs"),
        ]:
            with (
                mock.patch.dict(
                    os.environ,
                    {
                        "GITHUB_ACTIONS": "true",
                        "GITHUB_EVENT_NAME": event,
                        "GITHUB_REF": ref,
                        "GITHUB_REPOSITORY": repo,
                    },
                ),
                mock.patch.object(
                    sys, "argv", ["lake_cache.py", "put", "--repository", REPOSITORY]
                ),
                self.assertRaisesRegex(ValueError, "trusted main"),
            ):
                cache.main()

    def test_nested_artifacts_and_unsafe_paths(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "outputs.jsonl"

            def mapping(value):
                path.write_text(
                    json.dumps(cache.SCHEMA)
                    + "\n"
                    + json.dumps(["0" * 16, value])
                    + "\n"
                )

            mapping({"tree": [False, None, 5, {"module": "abcdef0123456789.ltar"}]})
            self.assertEqual(
                cache.artifact_names(path),
                {
                    "0000000000000005.art": "0000000000000005.art",
                    "abcdef0123456789.art": "abcdef0123456789.ltar",
                },
            )
            for value in ["../../secret", "0" * 16 + ".art/../secret", -1, 2**64, 1.5]:
                mapping(value)
                with self.subTest(value=value), self.assertRaises(ValueError):
                    cache.artifact_names(path)

    def test_endpoint_namespace_and_credentials(self):
        for endpoint in [
            "http://example.test",
            "https://id:secret@example.test",
            "https://example.test/?x=y",
        ]:
            with self.assertRaises(ValueError):
                S3(endpoint, "bucket", "prefix", "id:secret")
        store = S3("https://example.test", "bucket", "prefix", "id:secret")
        self.assertNotIn("id:secret", repr(store))
        for name in ["../other", "x/%2e%2e", "x//y", "/x", "x\\y"]:
            with self.assertRaises(ValueError):
                store.object_url(name)


if __name__ == "__main__":
    unittest.main()
