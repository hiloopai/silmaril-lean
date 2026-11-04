"""S3 transfers through curl: bounded parallelism, SigV4, no keys in argv."""

import json
import os
import re
import subprocess
import tempfile
import time
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import urlencode, urlsplit


def segment_path(value):
    if not value or any(
        not re.fullmatch(r"[A-Za-z0-9_.-]+", s) or s in {".", ".."}
        for s in value.split("/")
    ):
        raise ValueError(f"invalid cache path: {value!r}")
    return value


def endpoint_url(value):
    url = urlsplit(value)
    if (
        url.scheme != "https"
        or not url.hostname
        or url.username
        or url.password
        or url.query
        or url.fragment
        or url.path not in {"", "/"}
        or any(c.isspace() for c in value)
    ):
        raise ValueError("cache endpoint must be an HTTPS origin without credentials")
    return value.rstrip("/")


@dataclass
class S3:
    endpoint: str
    bucket: str
    prefix: str
    key: str = field(repr=False)
    region: str = "auto"
    session_token: str = field(default="", repr=False)

    def __post_init__(self):
        self.endpoint = endpoint_url(self.endpoint)
        if "/" in segment_path(self.bucket):
            raise ValueError("bucket must be one path segment")
        segment_path(self.prefix)
        if not re.fullmatch(r"[A-Za-z0-9-]+", self.region):
            raise ValueError("invalid signing region")
        if any(c in self.session_token for c in "\r\n\0"):
            raise ValueError("invalid S3 session token")
        if self.key and (
            ":" not in self.key
            or not all(self.key.split(":", 1))
            or any(c in self.key for c in "\r\n\0")
        ):
            raise ValueError(
                "cache key must contain an access ID and secret separated by ':'"
            )

    @property
    def base(self):
        return f"{self.endpoint}/{self.bucket}/{self.prefix}"

    def object_url(self, name):
        return self.base + "/" + segment_path(name)

    def transfer(self, requests):
        """Transfer (method, URL, file) tuples; return curl's per-object measurements."""
        if not requests:
            return []
        config = []
        for method, url, path in requests:
            if config:
                config.append("next")
            config += [
                "silent",
                "show-error",
                "connect-timeout = 10",
                "max-time = 120",
                'proto = "=https"',
                'write-out = "%{json}\\n"',
                "url = " + json.dumps(url),
            ]
            if self.key:
                config += [
                    "aws-sigv4 = " + json.dumps(f"aws:amz:{self.region}:s3"),
                    "user = " + json.dumps(self.key),
                ]
                if self.session_token:
                    config.append(
                        "header = "
                        + json.dumps("x-amz-security-token: " + self.session_token)
                    )
            if method == "PUT":
                config += [
                    "upload-file = " + json.dumps(str(path)),
                    'output = "/dev/null"',
                ]
            elif method == "HEAD":
                config += ["head", 'output = "/dev/null"']
            elif method == "GET":
                config += ["output = " + json.dumps(str(path))]
            else:
                raise ValueError("unsupported cache request method")
        env = {k: v for k, v in os.environ.items() if not k.startswith("LAKE_CI_")}
        # --disable prevents ~/.curlrc from enabling redirects or logging secrets.
        result = subprocess.run(
            [
                "curl",
                "--disable",
                "--parallel",
                "--parallel-max",
                "16",
                "--config",
                "-",
            ],
            input="\n".join(config) + "\n",
            text=True,
            capture_output=True,
            env=env,
            check=False,
        )
        try:
            records = [json.loads(line) for line in result.stdout.splitlines()]
            by_url = {row["url_effective"]: row for row in records}
            if len(records) != len(requests) or len(by_url) != len(requests):
                raise ValueError("missing or duplicate transfer result")
            ordered = [by_url[url] for _, url, _ in requests]
            if result.returncode or any(row["exitcode"] for row in ordered):
                raise RuntimeError(
                    f"cache transfer failed (curl exit {result.returncode}): "
                    + "; ".join(
                        str(row.get("errormsg")) for row in ordered if row["exitcode"]
                    )
                )
            return ordered
        except (ValueError, KeyError, TypeError) as error:
            raise RuntimeError("invalid or incomplete curl transfer report") from error

    def request(self, method, name, path=None):
        (row,) = self.transfer(
            [(method, self.object_url(name), path or Path(os.devnull))]
        )
        return row["http_code"]

    def inventory(self, scope):
        """List one artifact namespace. An incomplete list must never authorize a skip."""
        prefix = f"{self.prefix}/a/{segment_path(scope)}/"
        found, tokens, token = {}, set(), None
        with tempfile.TemporaryDirectory(prefix="lake-inventory-") as temporary:
            path = Path(temporary) / "page.xml"
            while True:
                query = {"list-type": "2", "prefix": prefix, "max-keys": "1000"}
                if token:
                    query["continuation-token"] = token
                url = f"{self.endpoint}/{self.bucket}?{urlencode(query)}"
                (row,) = self.transfer([("GET", url, path)])
                if row["http_code"] != 200:
                    raise RuntimeError(
                        f"cache inventory failed: HTTP {row['http_code']}"
                    )
                page = ET.parse(path).getroot()
                ns = "{http://s3.amazonaws.com/doc/2006-03-01/}"
                if (
                    page.tag != ns + "ListBucketResult"
                    or page.findtext(ns + "Prefix") != prefix
                ):
                    raise ValueError("unexpected cache inventory namespace")
                for entry in page.findall(ns + "Contents"):
                    name = entry.findtext(ns + "Key", "")
                    size = int(entry.findtext(ns + "Size", "-1"))
                    if not name.startswith(prefix) or size < 0 or name in found:
                        raise ValueError("invalid cache inventory object")
                    found[name] = size
                truncated = page.findtext(ns + "IsTruncated")
                if truncated == "false":
                    return {name[len(prefix) :]: size for name, size in found.items()}
                if truncated != "true":
                    raise ValueError("cache inventory lacks completion status")
                token = page.findtext(ns + "NextContinuationToken")
                if not token or token in tokens:
                    raise ValueError("cache inventory has invalid continuation token")
                tokens.add(token)

    def upload(self, files):
        started = time.monotonic()
        rows = self.transfer(
            [("PUT", self.object_url(name), path) for name, path in files]
        )
        failed = [row for row in rows if row["http_code"] not in {200, 201, 204}]
        if failed:
            raise RuntimeError(
                "cache upload failed: HTTP "
                + ", ".join(str(row["http_code"]) for row in failed)
            )
        size = sum(int(row["size_upload"]) for row in rows)
        return {
            "objects": len(rows),
            "bytes": size,
            "seconds": time.monotonic() - started,
        }
