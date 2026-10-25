"""Offline checks for cache trust, credentials, namespaces and Lake invocation."""

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


MODULE_PATH = Path(__file__).with_name("lake-cache.py")
SPEC = importlib.util.spec_from_file_location("lake_cache", MODULE_PATH)
cache = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = cache
SPEC.loader.exec_module(cache)

BASE = "https://cache.example/bucket/silmaril-lean/v1"
KEY = "offline-id:offline-secret"
REVISION = "a" * 40
SCOPE = "hiloopai/silmaril-lean/linux-x86_64/pins"
MAIN_ENV = {
    "GITHUB_ACTIONS": "true",
    "GITHUB_EVENT_NAME": "push",
    "GITHUB_REF": "refs/heads/main",
    "GITHUB_REPOSITORY": "hiloopai/silmaril-lean",
    "SILMARIL_CACHE_ENDPOINT": "https://cache.example",
    "SILMARIL_CACHE_KEY": KEY,
}


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.env = mock.patch.dict(os.environ, {}, clear=True)
        self.env.start()
        self.addCleanup(self.env.stop)

    def test_get_without_configuration_does_not_start_process_or_network(self):
        with mock.patch.object(cache, "output") as output, \
                mock.patch.object(cache, "request") as request, \
                contextlib.redirect_stdout(io.StringIO()) as stdout:
            self.assertEqual(cache.run_cache(self.root, "get"), 0)
        output.assert_not_called()
        request.assert_not_called()
        self.assertIn("not configured", stdout.getvalue())

    def test_write_requires_exact_trusted_main_context(self):
        self.assertTrue(cache.trusted_main(MAIN_ENV))
        for name, other in [
            ("GITHUB_ACTIONS", "false"),
            ("GITHUB_EVENT_NAME", "pull_request"),
            ("GITHUB_EVENT_NAME", "pull_request_target"),
            ("GITHUB_EVENT_NAME", "workflow_dispatch"),
            ("GITHUB_REF", "refs/heads/feature"),
            ("GITHUB_REPOSITORY", "contributor/silmaril-lean"),
        ]:
            env = dict(MAIN_ENV, **{name: other})
            with self.subTest(name=name, value=other), mock.patch.dict(os.environ, env, clear=True), \
                    mock.patch.object(cache, "request") as request, \
                    self.assertRaisesRegex(ValueError, "trusted push"):
                cache.run_cache(self.root, "put")
            request.assert_not_called()

    def test_pr_never_uses_writer_key_for_restore(self):
        env = dict(MAIN_ENV, GITHUB_EVENT_NAME="pull_request", GITHUB_REF="refs/pull/1/merge")
        with mock.patch.dict(os.environ, env, clear=True):
            self.assertIsNone(cache.Config.from_env("get"))
            os.environ["SILMARIL_CACHE_READ_KEY"] = "reader:read-secret"
            self.assertEqual(cache.Config.from_env("get").key, "reader:read-secret")

    def test_unsigned_public_restore_needs_no_secret(self):
        with mock.patch.dict(os.environ, {"SILMARIL_CACHE_PUBLIC_URL": "https://public.example"}):
            config = cache.Config.from_env("get")
        self.assertEqual(config.base, "https://public.example/silmaril-lean/v1")
        self.assertEqual(config.key, "")

    def test_configuration_is_namespaced_and_credentials_do_not_appear_in_repr(self):
        with mock.patch.dict(os.environ, MAIN_ENV):
            config = cache.Config.from_env("put")
            self.assertIn("/silmaril-lean/", config.base)
            self.assertNotIn(KEY, repr(config))
            os.environ["SILMARIL_CACHE_PREFIX"] = "lake/internal"
            with self.assertRaisesRegex(ValueError, "prefix"):
                cache.Config.from_env("put")

    def test_invalid_endpoint_and_key_are_rejected(self):
        for url in ["http://cache.example", "https://id:secret@cache.example",
                    "https://cache.example/?token=value", "https://cache.example/#fragment"]:
            with self.subTest(url=url), self.assertRaises(ValueError):
                cache.checked_url(url)
        for key in ["missing-separator", ":secret", "id:", "id:secret\nurl=other"]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                cache.checked_key(key)

    def test_scope_changes_with_pins_lean_build_and_native_platform(self):
        names = ["lean-toolchain", "lake-manifest.json", "lakefile.toml"]
        for name in names:
            (self.root / name).write_text("original " + name)
        with mock.patch.object(cache, "output", return_value="Lean build 1") as output, \
                mock.patch.object(cache.platform, "system", return_value="Linux"), \
                mock.patch.object(cache.platform, "machine", return_value="x86_64"):
            scope = cache.cache_scope(self.root)
            self.assertTrue(scope.startswith("hiloopai/silmaril-lean/linux-x86_64/"))
            for name in names:
                path = self.root / name
                original = path.read_text()
                path.write_text(original + " changed")
                self.assertNotEqual(scope, cache.cache_scope(self.root))
                path.write_text(original)
            output.return_value = "Lean build 2"
            self.assertNotEqual(scope, cache.cache_scope(self.root))
            output.return_value = "Lean build 1"
            with mock.patch.object(cache.platform, "machine", return_value="aarch64"):
                self.assertNotEqual(scope, cache.cache_scope(self.root))

    def test_targets_cover_library_eight_executables_and_all_inventory_proofs(self):
        root = MODULE_PATH.resolve().parents[1]
        inventory = json.loads((root / "tools/binaryen-lean/release-manifest.json").read_text())
        targets = cache.build_targets(root)
        self.assertIn("Silmaril", targets)
        self.assertTrue(set(cache.TOOLS).issubset(targets))
        self.assertEqual(len(cache.TOOLS), 8)
        for item in [*inventory["tools"], *inventory["cli_compatibility"]["executables"]]:
            for proof in item.get("proof_roots", []):
                self.assertIn(proof["module"], targets)

    def test_lake_receives_only_dummy_key_and_secret_free_configuration(self):
        config = cache.Config(BASE, KEY, "eu-west-1")
        env = cache.cache_environment(self.root, config)
        self.assertEqual(env["LAKE_CACHE_KEY"], "configured-by-curl-shim")
        self.assertEqual(env[cache.SHIM_KEY], KEY)
        self.assertNotIn(KEY, Path(env["LAKE_CONFIG"]).read_text())
        self.assertEqual(env["LAKE_ARTIFACT_CACHE"], "true")

    def test_direct_curl_arguments_remove_lake_key_and_redirects(self):
        args = cache.curl_arguments([
            "-X", "PUT", "-L", "--user", "configured-by-curl-shim",
            "--aws-sigv4", "aws:amz:auto:s3", BASE + "/a/scope/hash.art",
        ], BASE, "eu-west-1")
        self.assertNotIn("configured-by-curl-shim", args)
        self.assertNotIn("--user", args)
        self.assertNotIn("-L", args)
        self.assertEqual(args[-2:], ["--aws-sigv4", "aws:amz:eu-west-1:s3"])

    def test_bulk_transfer_accepts_real_lake_url_and_file_options(self):
        config = self.root / "curl.cfg"
        config.write_text('url = ' + json.dumps(BASE + '/a/scope/hash.art') + '\n-o "/tmp/artifact.tmp"\n')
        got = cache.curl_arguments(["-Z", "-X", "GET", "--config", str(config)], BASE, "auto")
        self.assertIn("-Z", got)
        self.assertIn(str(config), got)

    def test_direct_and_bulk_urls_cannot_escape_namespace(self):
        urls = [
            "https://evil.example/bucket/silmaril-lean/v1/a/file.art",
            BASE + "-sibling/a/file.art",
            BASE + "/../internal/a/file.art",
            BASE + "/%2e%2e/internal/a/file.art",
            BASE + "/a/../../internal/file.art",
            BASE + "/a/%2f..%2f../internal/file.art",
            BASE + "/a/file.art?token=unexpected",
            BASE + "/a/file.art#fragment",
        ]
        for url in urls:
            with self.subTest(url=url), self.assertRaises(ValueError):
                cache.curl_arguments([url], BASE, "auto")
            config = self.root / "bad-curl.cfg"
            config.write_text('url = ' + json.dumps(url) + '\n-T "/tmp/artifact"\n')
            with self.subTest(bulk_url=url), self.assertRaises(ValueError):
                cache.curl_arguments(["--config", str(config)], BASE, "auto")

    def test_bulk_configuration_cannot_inject_other_curl_options(self):
        config = self.root / "curl.cfg"
        config.write_text('url = ' + json.dumps(BASE + '/a/file.art') + '\nproxy = "evil.example"\n')
        with self.assertRaisesRegex(ValueError, "unexpected option"):
            cache.curl_arguments(["--config", str(config)], BASE, "auto")

    def test_actual_key_is_only_in_curl_stdin_and_removed_from_child_environment(self):
        env = {cache.SHIM_BASE: BASE, cache.SHIM_KEY: KEY, cache.SHIM_REGION: "auto",
               cache.SHIM_MARKER: "1", "SILMARIL_CACHE_KEY": KEY,
               "SILMARIL_CACHE_READ_KEY": "reader:read-secret", "LAKE_CACHE_KEY": "dummy", "CURL": "helper"}
        with mock.patch.dict(os.environ, env), \
                mock.patch.object(cache.subprocess, "run", return_value=subprocess.CompletedProcess([], 0)) as run:
            self.assertEqual(cache.curl_shim([BASE + "/a/hash.art"]), 0)
        args, kwargs = run.call_args
        self.assertNotIn(KEY, " ".join(args[0]))
        self.assertIn(KEY, kwargs["input"])
        for key in [cache.SHIM_KEY, cache.SHIM_MARKER, "SILMARIL_CACHE_KEY",
                    "SILMARIL_CACHE_READ_KEY", "LAKE_CACHE_KEY", "CURL"]:
            self.assertNotIn(key, kwargs["env"])

    def test_get_uses_current_revision_before_main_pointer(self):
        config = cache.Config(BASE, KEY, "auto")
        with mock.patch.object(cache.Config, "from_env", return_value=config), \
                mock.patch.object(cache, "cache_scope", return_value=SCOPE), \
                mock.patch.object(cache, "output", return_value=REVISION), \
                mock.patch.object(cache, "request", return_value=200) as request, \
                mock.patch.object(cache.subprocess, "run") as run, \
                contextlib.redirect_stdout(io.StringIO()):
            cache.run_cache(self.root, "get")
        self.assertEqual(request.call_count, 1)
        self.assertTrue(request.call_args.args[3].endswith(REVISION + ".jsonl"))
        self.assertIn(REVISION, run.call_args.args[0])
        self.assertIn(SCOPE, run.call_args.args[0])

    def test_get_uses_validated_pointer_when_history_has_no_mapping(self):
        def request(root, config, method, url, destination=None, source=None):
            if method == "HEAD":
                return 404
            destination.write_text(REVISION + "\n")
            return 200
        with mock.patch.object(cache.Config, "from_env", return_value=cache.Config(BASE, KEY, "auto")), \
                mock.patch.object(cache, "cache_scope", return_value=SCOPE), \
                mock.patch.object(cache, "output", return_value="b" * 40), \
                mock.patch.object(cache, "request", side_effect=request), \
                mock.patch.object(cache.subprocess, "run") as run, \
                contextlib.redirect_stdout(io.StringIO()):
            cache.run_cache(self.root, "get")
        self.assertIn(REVISION, run.call_args.args[0])

    def test_malformed_pointer_is_rejected_without_starting_lake(self):
        def request(root, config, method, url, destination=None, source=None):
            if method == "HEAD":
                return 404
            destination.write_text("not-a-revision\n")
            return 200
        with mock.patch.object(cache.Config, "from_env", return_value=cache.Config(BASE, KEY, "auto")), \
                mock.patch.object(cache, "cache_scope", return_value=SCOPE), \
                mock.patch.object(cache, "output", return_value="b" * 40), \
                mock.patch.object(cache, "request", side_effect=request), \
                mock.patch.object(cache.subprocess, "run") as run, \
                self.assertRaisesRegex(ValueError, "main pointer"):
            cache.run_cache(self.root, "get")
        run.assert_not_called()

    def test_failed_upload_does_not_move_main_pointer(self):
        def lake(args, **kwargs):
            if args[:2] == ["lake", "build"]:
                Path(args[args.index("-o") + 1]).write_text('{"artifact":"test"}\n')
                return subprocess.CompletedProcess(args, 0)
            raise subprocess.CalledProcessError(1, args)
        with mock.patch.dict(os.environ, MAIN_ENV), \
                mock.patch.object(cache.Config, "from_env", return_value=cache.Config(BASE, KEY, "auto")), \
                mock.patch.object(cache, "cache_scope", return_value=SCOPE), \
                mock.patch.object(cache, "output", return_value=""), \
                mock.patch.object(cache, "build_targets", return_value=["Silmaril"]), \
                mock.patch.object(cache.subprocess, "run", side_effect=lake), \
                mock.patch.object(cache, "request") as request, \
                self.assertRaises(subprocess.CalledProcessError):
            cache.run_cache(self.root, "put")
        request.assert_not_called()

    def test_dirty_source_cannot_publish(self):
        with mock.patch.dict(os.environ, MAIN_ENV), \
                mock.patch.object(cache.Config, "from_env", return_value=cache.Config(BASE, KEY, "auto")), \
                mock.patch.object(cache, "cache_scope", return_value=SCOPE), \
                mock.patch.object(cache, "output", return_value=" M source.lean"), \
                mock.patch.object(cache.subprocess, "run") as run, \
                self.assertRaisesRegex(ValueError, "clean source"):
            cache.run_cache(self.root, "put")
        run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
