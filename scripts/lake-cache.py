#!/usr/bin/env python3
"""Fetch or publish this repository's optional S3-compatible Lake artifact cache."""

import argparse
import hashlib
import json
import os
import platform
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import urlparse


REPOSITORY = "hiloopai/silmaril-lean"
SERVICE = "silmaril-release"
SHIM_MARKER = "SILMARIL_CACHE_CURL_SHIM"
SHIM_BASE = "SILMARIL_CACHE_CURL_BASE"
SHIM_KEY = "SILMARIL_CACHE_CURL_KEY"
SHIM_REGION = "SILMARIL_CACHE_CURL_REGION"
TOOLS = ["wasm-as", "wasm-dis", "wasm-opt", "wasm-merge", "wasm-shell",
         "wasm-ctor-eval", "wasm-metadce", "wasm-shell-lean"]


def trusted_main(env=None):
    env = os.environ if env is None else env
    return (env.get("GITHUB_ACTIONS") == "true"
            and env.get("GITHUB_EVENT_NAME") == "push"
            and env.get("GITHUB_REF") == "refs/heads/main"
            and env.get("GITHUB_REPOSITORY") == REPOSITORY)


def checked_key(value):
    if not value:
        return ""
    if ":" not in value or not all(value.split(":", 1)) or any(c in value for c in "\r\n"):
        raise ValueError("cache key must contain a nonempty access ID and secret separated by ':'")
    return value


def checked_url(value):
    parsed = urlparse(value)
    if parsed.scheme != "https" or not parsed.netloc or parsed.username or parsed.password:
        raise ValueError("cache endpoint must be an HTTPS URL without embedded credentials")
    if (parsed.query or parsed.fragment or "%" in parsed.path or "\\" in parsed.path
            or any(part in [".", ".."] for part in parsed.path.split("/"))):
        raise ValueError("cache endpoint must not contain traversal, encoded paths, a query or fragment")
    return value.rstrip("/")


@dataclass
class Config:
    base: str
    key: str = field(repr=False)
    region: str

    @classmethod
    def from_env(cls, action):
        endpoint = os.environ.get("SILMARIL_CACHE_ENDPOINT", "").strip()
        bucket = os.environ.get("SILMARIL_CACHE_BUCKET", "lean-cache").strip("/")
        prefix = os.environ.get("SILMARIL_CACHE_PREFIX", "silmaril-lean/v1").strip("/")
        # Require an isolated release namespace even when sharing a bucket.
        if not prefix.startswith("silmaril-lean/") or ".." in prefix.split("/"):
            raise ValueError("cache prefix must be beneath silmaril-lean/")
        key = os.environ.get("SILMARIL_CACHE_READ_KEY", "") if action == "get" else ""
        if action == "put" or trusted_main() or os.environ.get("GITHUB_ACTIONS") != "true":
            key = key or os.environ.get("SILMARIL_CACHE_KEY", "")
        public = os.environ.get("SILMARIL_CACHE_PUBLIC_URL", "").strip() if action == "get" else ""
        if public and not key:
            base = checked_url(public) + "/" + prefix
        elif endpoint and key:
            base = checked_url(endpoint) + "/" + bucket + "/" + prefix
        else:
            return None
        return cls(base, checked_key(key), os.environ.get("SILMARIL_CACHE_REGION", "auto"))


def output(root, *args):
    return subprocess.check_output(args, cwd=root, text=True).strip()


def cache_scope(root):
    digest = hashlib.sha256()
    for name in ["lean-toolchain", "lake-manifest.json", "lakefile.toml"]:
        digest.update(name.encode() + b"\0" + (root / name).read_bytes() + b"\0")
    lean_version = output(root, "lean", "--version")
    digest.update(lean_version.encode())
    native = platform.system().lower() + "-" + platform.machine().lower()
    return REPOSITORY + "/" + native + "/" + digest.hexdigest()


def build_targets(root):
    manifest = json.loads((root / "tools/binaryen-lean/release-manifest.json").read_text())
    proofs = sorted({proof["module"] for item in
                     [*manifest["tools"], *manifest["cli_compatibility"]["executables"]]
                     for proof in item.get("proof_roots", [])})
    return ["Silmaril", *TOOLS, *proofs]


def cache_environment(root, config):
    directory = root / "build/lake-cache"
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / "config.toml"
    path.write_text("\n".join([
        'cache.defaultService = "' + SERVICE + '"',
        'cache.defaultUploadService = "' + SERVICE + '"',
        "[[cache.service]]", 'name = "' + SERVICE + '"', 'kind = "s3"',
        "artifactEndpoint = " + json.dumps(config.base + "/a"),
        "revisionEndpoint = " + json.dumps(config.base + "/r"), ""]))
    env = os.environ.copy()
    env.update(LAKE_CONFIG=str(path), CURL=str(Path(__file__).resolve()),
               LAKE_ARTIFACT_CACHE="true", LAKE_CACHE_KEY="configured-by-curl-shim")
    env.update({SHIM_MARKER: "1", SHIM_BASE: config.base, SHIM_KEY: config.key,
                SHIM_REGION: config.region})
    return env


def scoped_url(url, base):
    parsed, expected = urlparse(url), urlparse(base)
    return (parsed.scheme == expected.scheme and parsed.netloc == expected.netloc
            and not parsed.username and not parsed.password and not parsed.query and not parsed.fragment
            and "%" not in parsed.path and "\\" not in parsed.path
            and not any(part in [".", ".."] for part in parsed.path.split("/"))
            and (parsed.path == expected.path or parsed.path.startswith(expected.path + "/")))


def curl_arguments(args, base, region):
    """Validate Lake's direct/bulk URLs and remove its placeholder credentials."""
    cleaned, urls, i = [], [], 0
    while i < len(args):
        arg = args[i]
        if arg in ["--user", "-u"]:
            i += 2
            continue
        if arg.startswith("--user="):
            i += 1
            continue
        if arg == "--aws-sigv4":
            i += 2
            continue
        if arg in ["--config", "-K"]:
            if i + 1 >= len(args) or args[i + 1] == "-":
                raise ValueError("cache curl configuration must be a Lake-generated file")
            text = Path(args[i + 1]).read_text()
            for line in text.splitlines():
                if re.match(r"^\s*url\s*=", line):
                    value = line.split("=", 1)[1].strip()
                    urls.append(json.loads(value))
                elif not re.fullmatch(r'\s*-(?:o|T)\s+"(?:[^"\\]|\\.)*"\s*', line):
                    raise ValueError("unexpected option in Lake's cache transfer configuration")
            cleaned.extend(args[i:i + 2])
            i += 2
            continue
        if arg.startswith(("https://", "http://")):
            urls.append(arg)
        cleaned.append(arg)
        i += 1
    if not urls or not all(scoped_url(url, base) for url in urls):
        raise ValueError("refusing to send cache credentials outside the configured namespace")
    # Signed redirects could send credentials to an unexpected origin or namespace.
    cleaned = [arg for arg in cleaned if arg not in ["-L", "--location", "--location-trusted"]]
    return [*cleaned, "--aws-sigv4", "aws:amz:" + region + ":s3"]


def curl_shim(args):
    key = checked_key(os.environ.get(SHIM_KEY, ""))
    base = checked_url(os.environ[SHIM_BASE])
    region = os.environ.get(SHIM_REGION, "auto")
    cleaned = curl_arguments(args, base, region)
    if key:
        cleaned.extend(["--config", "-"])
        feed = "user = " + json.dumps(key) + "\n"
    else:
        # Public-read endpoints need no request signature.
        cleaned = cleaned[:-2]
        feed = None
    env = os.environ.copy()
    for name in [SHIM_MARKER, SHIM_KEY, "CURL", "LAKE_CACHE_KEY",
                 "SILMARIL_CACHE_KEY", "SILMARIL_CACHE_READ_KEY"]:
        env.pop(name, None)
    return subprocess.run(["curl", *cleaned], input=feed, text=True, env=env).returncode


def request(root, config, method, url, destination=None, source=None):
    env = cache_environment(root, config)
    args = [str(Path(__file__).resolve()), "-sS", "--connect-timeout", "10",
            "--max-time", "60", "-o", str(destination or os.devnull), "-w", "%{http_code}"]
    args += ["-I"] if method == "HEAD" else ["-X", method]
    if source:
        args += ["-T", str(source)]
    result = subprocess.run([*args, url], cwd=root, env=env, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError("cache HTTP request failed (curl exit " + str(result.returncode) + ")")
    try:
        return int(result.stdout)
    except ValueError:
        raise RuntimeError("cache HTTP request returned an invalid status") from None


def run_cache(root, action):
    if action == "put" and not trusted_main():
        raise ValueError("cache uploads require a trusted push to hiloopai/silmaril-lean main in CI")
    config = Config.from_env(action)
    if config is None:
        print("S3 cache: not configured for this job; using normal Lake builds")
        return 0
    scope = cache_scope(root)
    env = cache_environment(root, config)
    revision_base = config.base + "/r/" + scope
    if action == "get":
        candidates = output(root, "git", "rev-list", "--first-parent", "-n", "60", "HEAD").splitlines()
        for rev in candidates:
            if request(root, config, "HEAD", revision_base + "/" + rev + ".jsonl") == 200:
                break
        else:
            pointer = root / "build/lake-cache/main-latest"
            if request(root, config, "GET", revision_base + "/main-latest", pointer) != 200:
                print("S3 cache: no published build for these pins and platform")
                return 0
            rev = pointer.read_text().strip()
            if not re.fullmatch(r"[0-9a-f]{40}", rev):
                raise ValueError("invalid cache main pointer")
        subprocess.run(["lake", "cache", "get", "--service", SERVICE,
                        "--scope", scope, "--rev", rev], cwd=root, env=env, check=True)
        print("S3 cache: fetched trusted build artifacts; Lake restores matching outputs during builds")
    else:
        if output(root, "git", "status", "--porcelain"):
            raise ValueError("cache publication requires a clean source tree")
        mappings = root / "build/lake-cache/mappings.jsonl"
        subprocess.run(["lake", "build", "--wfail", "-o", str(mappings), *build_targets(root)],
                       cwd=root, env=env, check=True)
        if not mappings.is_file() or not mappings.stat().st_size:
            raise RuntimeError("Lake did not produce artifact mappings")
        subprocess.run(["lake", "cache", "put", str(mappings), "--service", SERVICE,
                        "--scope", scope], cwd=root, env=env, check=True)
        pointer = root / "build/lake-cache/main-pointer-upload"
        pointer.write_text(output(root, "git", "rev-parse", "HEAD") + "\n")
        if request(root, config, "PUT", revision_base + "/main-latest", source=pointer) not in [200, 201, 204]:
            raise RuntimeError("could not update the published cache main pointer")
        print("S3 cache: published library, proof and native executable artifacts")
    return 0


def main(argv=None):
    if os.environ.get(SHIM_MARKER) == "1":
        try:
            return curl_shim(sys.argv[1:] if argv is None else argv)
        except (ValueError, OSError) as error:
            print("cache curl shim: " + str(error), file=sys.stderr)
            return 1
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["get", "put"])
    args = parser.parse_args(argv)
    try:
        return run_cache(Path(__file__).resolve().parents[1], args.action)
    except (ValueError, RuntimeError, OSError, subprocess.CalledProcessError) as error:
        print("S3 cache: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
