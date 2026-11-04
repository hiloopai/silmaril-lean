#!/usr/bin/env python3
"""Record successful Lake builds and publish only missing S3 artifacts."""

import argparse
import hashlib
import json
import os
import platform
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from urllib.parse import urlsplit

from storage import S3, segment_path

SCHEMA = "2026-03-17"
SERVICE = "shared-lake-cache"


def output(root, *args):
    return subprocess.check_output(args, cwd=root, text=True).strip()


def lake(*args):
    return [os.environ.get("LAKE", "lake"), *args]


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def identity(root, repository, package):
    segment_path(repository)
    segment_path(package or "root")
    digest = hashlib.sha256()
    for name in [
        "lean-toolchain",
        "lake-manifest.json",
        "lakefile.toml",
        "lakefile.lean",
    ]:
        path = root / name
        if path.is_file():
            digest.update(name.encode() + b"\0" + path.read_bytes() + b"\0")
    digest.update(output(root, "lean", "--version").encode())
    scope = "/".join(
        [
            repository,
            platform.system().lower() + "-" + platform.machine().lower(),
            digest.hexdigest(),
            package or "root",
        ]
    )
    return {
        "scope": scope,
        "revision": output(root, "git", "rev-parse", "HEAD"),
        "run": [
            os.environ.get("GITHUB_RUN_ID", "local"),
            os.environ.get("GITHUB_RUN_ATTEMPT", "local"),
        ],
    }


def artifact_names(path):
    """Read Lake's native JSONL, including nested and numeric artifact descriptions."""
    files = {}

    def collect(value):
        if value is None or isinstance(value, bool):
            return
        if isinstance(value, int) and 0 <= value < 2**64:
            name = f"{value:016x}.art"
        elif isinstance(value, str) and re.fullmatch(
            r"[0-9a-f]{16}(?:\.[A-Za-z0-9_.-]+)?", value
        ):
            name = value
        elif isinstance(value, list):
            for child in value:
                collect(child)
            return
        elif isinstance(value, dict):
            for child in value.values():
                collect(child)
            return
        else:
            raise ValueError(f"unsupported Lake artifact description: {value!r}")
        files.setdefault(name[:16] + ".art", name)

    with path.open() as stream:
        if json.loads(next(stream, "null")) != SCHEMA:
            raise ValueError("unsupported Lake mapping schema")
        seen = set()
        for line in stream:
            entry = json.loads(line)
            if (
                not isinstance(entry, list)
                or len(entry) != 2
                or not isinstance(entry[0], str)
                or not re.fullmatch(r"[0-9a-f]{16}", entry[0])
                or entry[0] in seen
            ):
                raise ValueError("invalid or duplicate Lake input mapping")
            seen.add(entry[0])
            collect(entry[1])
    if not seen:
        raise ValueError("Lake produced no input mappings")
    return files


def artifacts(path, directory):
    files = {
        remote: directory / local for remote, local in artifact_names(path).items()
    }
    for file in files.values():
        if not file.is_file():
            raise ValueError(f"artifact missing from local cache: {file}")
    return files


def record_build(root, repository, record, targets, package=""):
    record.mkdir(parents=True, exist_ok=True)
    receipt = record / "success.json"
    receipt.unlink(missing_ok=True)
    mapping = record / "outputs.jsonl"
    mapping.unlink(missing_ok=True)
    before = identity(root, repository, package)
    env = dict(os.environ, LAKE_ARTIFACT_CACHE="true")
    command = lake("build", "--wfail", "-o", str(mapping))
    if package:
        command += ["--package", package]
    subprocess.run([*command, *targets], cwd=root, env=env, check=True)
    if identity(root, repository, package) != before:
        raise ValueError("build identity changed while checking")
    directory = (
        Path(output(root, *lake("env", "printenv", "LAKE_CACHE_DIR"))) / "artifacts"
    )
    artifacts(mapping, directory)
    receipt.write_text(
        json.dumps(
            {
                **before,
                "mapping_sha256": sha256(mapping),
                "artifacts": str(directory.resolve()),
            }
        )
        + "\n"
    )


def publish(root, repository, record, store, package=""):
    """The caller runs its remaining tests before this; this function never builds."""
    started = time.monotonic()
    if output(root, "git", "status", "--porcelain"):
        raise ValueError("cache publication requires a clean source tree")
    expected = identity(root, repository, package)
    receipt = json.loads((record / "success.json").read_text())
    if any(receipt.get(k) != v for k, v in expected.items()):
        raise ValueError(
            "cache receipt does not match this revision, platform, pins and run"
        )
    mapping = record / "outputs.jsonl"
    if receipt.get("mapping_sha256") != sha256(mapping):
        raise ValueError("cache mapping changed after successful build")
    files = artifacts(mapping, Path(receipt["artifacts"]))
    scope = expected["scope"]
    inventory_started = time.monotonic()
    inventory = store.inventory(scope)
    inventory_seconds = time.monotonic() - inventory_started
    missing = [
        (f"a/{scope}/{name}", path)
        for name, path in files.items()
        if inventory.get(name) != path.stat().st_size
    ]
    transfer = store.upload(missing)
    # Remote blob presence, not an old mapping, decides reuse. A deleted blob
    # is repaired before the complete revision mapping becomes visible.
    metadata = store.upload([(f"r/{scope}/{expected['revision']}.jsonl", mapping)])
    pointer = record / "main-latest"
    pointer.write_text(expected["revision"] + "\n")
    pointer_transfer = store.upload([(f"r/{scope}/main-latest", pointer)])
    result = {
        "artifacts": len(files),
        "reused": len(files) - len(missing),
        "uploaded": transfer["objects"],
        "artifact_bytes": transfer["bytes"],
        "metadata_bytes": metadata["bytes"] + pointer_transfer["bytes"],
        "inventory_seconds": inventory_seconds,
        "transfer_seconds": transfer["seconds"],
        "seconds": time.monotonic() - started,
    }
    print("Lake cache publication: " + json.dumps(result, sort_keys=True))
    (record / "publication.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def config(action):
    endpoint = os.environ.get("LAKE_CI_ENDPOINT", "")
    key = os.environ.get("LAKE_CI_KEY", "")
    if not endpoint:
        return None
    if action == "put" and not key:
        raise ValueError("cache publication needs LAKE_CI_KEY")
    return S3(
        endpoint,
        os.environ.get("LAKE_CI_BUCKET", "lean-cache"),
        os.environ["LAKE_CI_PREFIX"],
        key,
        os.environ.get("LAKE_CI_REGION", "auto"),
        os.environ.get("LAKE_CI_SESSION_TOKEN", ""),
    )


def restore(root, repository, store, package=""):
    scope = identity(root, repository, package)["scope"]
    with tempfile.TemporaryDirectory(prefix="lake-restore-") as temporary:
        directory = Path(temporary)
        pointer = directory / "main-latest"
        status = store.request("GET", f"r/{scope}/main-latest", pointer)
        if status == 404:
            print("Lake cache: no published build for these pins and platform")
            return
        if status != 200:
            raise RuntimeError(f"cache pointer lookup failed: HTTP {status}")
        revision = pointer.read_text().strip()
        if not re.fullmatch(r"[0-9a-f]{40}", revision):
            raise ValueError("invalid cache main pointer")
        path = directory / "config.toml"
        path.write_text(
            "\n".join(
                [
                    "[[cache.service]]",
                    'name = "' + SERVICE + '"',
                    'kind = "s3"',
                    "artifactEndpoint = " + json.dumps(store.base + "/a"),
                    "revisionEndpoint = " + json.dumps(store.base + "/r"),
                    "",
                ]
            )
        )
        env = dict(
            os.environ,
            LAKE_CONFIG=str(path),
            CURL=str(Path(__file__).resolve()),
            LAKE_CI_CURL_BASE=store.base,
        )
        args = lake(
            "cache", "get", "--service", SERVICE, "--scope", scope, "--rev", revision
        )
        if package:
            args += ["--package", package]
        subprocess.run(args, cwd=root, env=env, check=True)


def curl_shim(args):
    """Native Lake owns download validation; constrain its URLs before signing."""
    store = config("get")
    if store is None or store.base != os.environ["LAKE_CI_CURL_BASE"]:
        raise ValueError("cache download configuration changed")
    cleaned, urls, i = [], [], 0
    while i < len(args):
        arg = args[i]
        if arg in {"--user", "-u", "--aws-sigv4"}:
            i += 2
            continue
        if arg in {"--config", "-K"}:
            path = Path(args[i + 1])
            for line in path.read_text().splitlines():
                if re.match(r"^\s*url\s*=", line):
                    urls.append(json.loads(line.split("=", 1)[1].strip()))
                elif not re.fullmatch(r'\s*-o\s+"(?:[^"\\]|\\.)*"\s*', line):
                    raise ValueError("unexpected option in Lake download configuration")
            cleaned += args[i : i + 2]
            i += 2
            continue
        if arg.startswith(("https://", "http://")):
            urls.append(arg)
        if arg not in {"-L", "--location", "--location-trusted"}:
            cleaned.append(arg)
        i += 1
    if not urls:
        raise ValueError("cache download has no URLs")
    for url in urls:
        parsed = urlsplit(url)
        if (
            not url.startswith(store.base + "/")
            or parsed.query
            or parsed.fragment
            or parsed.username
            or parsed.password
        ):
            raise ValueError(
                "refusing cache credentials outside the configured namespace"
            )
        segment_path(url[len(store.base) + 1 :])
    feed = ""
    if store.key:
        cleaned += ["--aws-sigv4", f"aws:amz:{store.region}:s3", "--config", "-"]
        feed = "user = " + json.dumps(store.key) + "\n"
        if store.session_token:
            feed += (
                "header = "
                + json.dumps("x-amz-security-token: " + store.session_token)
                + "\n"
            )
    env = {
        k: v
        for k, v in os.environ.items()
        if not k.startswith("LAKE_CI_") and k != "CURL"
    }
    return subprocess.run(
        ["curl", "--disable", *cleaned], input=feed, text=True, env=env, check=False
    ).returncode


def dependencies(root, targets):
    subprocess.run(lake("env", "true"), cwd=root, check=True)
    packages = root / ".lake/packages"
    snapshot = output(root, "git", "-C", str(packages / "mathlib"), "rev-parse", "HEAD")
    toolchain = (root / "lean-toolchain").read_text().strip()
    env = dict(os.environ, LAKE_CONFIG=str(packages / "mathlib/.meta/lake-config.toml"))
    for name, scope in [
        ("mathlib", "mathlib4"),
        ("cslib", "cslib"),
        ("batteries", "batteries"),
        ("Qq", "quote4"),
        ("aesop", "aesop"),
        ("proofwidgets", "ProofWidgets4"),
        ("plausible", "plausible"),
        ("LeanSearchClient", "LeanSearchClient"),
        ("importGraph", "import-graph"),
        ("Cli", "lean4-cli"),
    ]:
        revision = (
            output(root, "git", "-C", str(packages / name), "rev-parse", "HEAD")
            if name == "cslib"
            else snapshot
        )
        args = lake(
            "cache",
            "get",
            "--package=" + name,
            "--rev=" + revision,
            "--scope=" + toolchain + "/" + scope,
        )
        if targets:
            args.append("--mappings-only")
        subprocess.run(args, cwd=root, env=env, check=True)
    if targets:
        subprocess.run(
            lake("build", "--wfail", *targets), cwd=root, env=env, check=True
        )


def main():
    if os.environ.get("LAKE_CI_CURL_BASE"):
        return curl_shim(sys.argv[1:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["build", "put", "get", "dependencies"])
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY", ""))
    parser.add_argument("--package", default="")
    parser.add_argument("--record", type=Path)
    # Split explicitly so build targets can include Lake flags after '--'.
    argv = sys.argv[1:]
    index = argv.index("--") if "--" in argv else len(argv)
    args = parser.parse_args(argv[:index])
    targets = argv[index + 1 :]
    root = args.root.resolve()
    record = (
        args.record.resolve()
        if args.record
        else root / "build/lake-cache" / (args.package or "root")
    )
    if args.action == "dependencies":
        dependencies(root, targets)
    elif args.action == "build":
        record_build(root, args.repository, record, targets, args.package)
    else:
        if targets:
            parser.error("only builds and dependency fetching accept targets")
        if args.action == "put" and not (
            os.environ.get("GITHUB_ACTIONS") == "true"
            and os.environ.get("GITHUB_REPOSITORY") == args.repository
            and os.environ.get("GITHUB_REF") == "refs/heads/main"
            and os.environ.get("GITHUB_EVENT_NAME") in {"push", "workflow_dispatch"}
        ):
            raise ValueError("publication requires a trusted main CI run")
        store = config(args.action)
        if store is None:
            print("Lake cache: no endpoint configured; using normal Lake builds")
        elif args.action == "put":
            publish(root, args.repository, record, store, args.package)
        else:
            restore(root, args.repository, store, args.package)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, RuntimeError, OSError, subprocess.CalledProcessError) as error:
        print("Lake cache: " + str(error), file=sys.stderr)
        raise SystemExit(1) from error
