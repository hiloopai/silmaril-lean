"""Build and verify the inline, text/list DRISL fixture subset (no Lean hashing)."""

import argparse
import base64
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


FORMAT = "silmaril.named-logic.v1"
PLAN_FORMAT = "silmaril.named-logic.plan.v1"
PROFILE = {"layout": "silmaril.dasl-syntax.v1", "atomCodec": "bare-string",
           "placement": "inline-all", "wire": "bdasl", "codec": "drisl"}
ALGORITHMS = {"bdasl-inline-sha256": ("sha256", 0x12), "bdasl-inline-blake3": ("blake3", 0x1e)}


def header(major, size):
    if size < 24:
        return bytes([major * 32 + size])
    width = next(width for width in (1, 2, 4, 8) if size < 256 ** width)
    return bytes([major * 32 + 23 + width.bit_length()]) + size.to_bytes(width, "big")


def encode(tree):
    if isinstance(tree, str):
        payload = tree.encode("utf-8")
        return header(3, len(payload)) + payload
    if isinstance(tree, list):
        return header(4, len(tree)) + b"".join(map(encode, tree))
    raise ValueError("inline profile supports only strings and lists")


def decode(payload):
    def read_at(start, depth):
        if start >= len(payload) or depth >= 64:
            raise ValueError("truncated or too deep")
        major, size = divmod(payload[start], 32)
        pos = start + 1
        if major not in (3, 4) or size > 27:
            raise ValueError("unsupported tag, indefinite item, or non-text/list object")
        if size >= 24:
            width = 1 << (size - 24)
            if pos + width > len(payload):
                raise ValueError("truncated length")
            size = int.from_bytes(payload[pos:pos + width], "big")
            pos += width
            if header(major, size) != payload[start:pos]:
                raise ValueError("noncanonical length")
        if size > len(payload) - pos:
            raise ValueError("truncated object")
        if major == 3:
            return payload[pos:pos + size].decode("utf-8"), pos + size
        children = []
        for _ in range(size):
            child, pos = read_at(pos, depth + 1)
            children.append(child)
        return children, pos

    tree, end = read_at(0, 0)
    if end != len(payload):
        raise ValueError("trailing bytes")
    return tree


def digest(algorithm, payload):
    if algorithm == "sha256":
        return hashlib.sha256(payload).digest()
    if algorithm != "blake3":
        raise ValueError(f"unsupported algorithm: {algorithm}")
    output = subprocess.run(["b3sum", "--no-names"], input=payload, capture_output=True, check=True).stdout
    result = bytes.fromhex(output.decode("ascii").strip())
    if len(result) != 32:
        raise ValueError("b3sum did not return a 32-byte digest")
    return result


def text_cid(wire):
    return "b" + base64.b32encode(wire).decode("ascii").lower().rstrip("=")


def read_cid(cid, code):
    if not re.fullmatch(r"b[a-z2-7]{58}", cid):
        raise ValueError("invalid canonical CID text")
    wire = base64.b32decode(cid[1:].upper() + "=" * 6)
    if len(wire) != 36 or wire[:4] != bytes([1, 0x71, code, 32]) or text_cid(wire) != cid:
        raise ValueError("CID envelope does not match profile")
    return wire[4:]


def plan_source(plan):
    source = plan["source"]
    if (plan["format"] != PLAN_FORMAT or source["repo"] != "hiloopai/silmaril-lean"
            or not re.fullmatch(r"[a-f0-9]{40}", source["revision"])):
        raise ValueError("invalid plan format or source revision")
    return source


def profile_table():
    return {profile: {**PROFILE, "multihash": algorithm} for profile, (algorithm, _) in ALGORITHMS.items()}


def rows_with_refs(plan, ref):
    rows = []
    seen = set()
    for row in plan["rows"]:
        if row["id"] in seen:
            raise ValueError("duplicate row id")
        seen.add(row["id"])
        steps = set()
        for step in row["evidence"]["steps"]:
            if step["id"] in steps or not set(step["premises"]) <= steps:
                raise ValueError("step IDs must be unique and premises must precede their conclusion")
            steps.add(step["id"])
        rows.append({**row, "roots": {role: ref(block) for role, block in row["roots"].items()},
                     "assumptions": [ref(block) for block in row["assumptions"]]})
    return rows


def build(plan):
    plan = deepcopy(plan)
    source = plan_source(plan)
    blocks = {profile: {} for profile in ALGORITHMS}
    refs = {}
    for key, tree in plan["blocks"].items():
        payload = encode(tree)
        choices = {}
        for profile, (algorithm, code) in ALGORITHMS.items():
            cid = text_cid(bytes([1, 0x71, code, 32]) + digest(algorithm, payload))
            block = {"hex": payload.hex(), "decoded": tree}
            previous = blocks[profile].setdefault(cid, block)
            if previous != block:
                raise ValueError(f"conflicting bytes for {cid}")
            choices[profile] = cid
        primary = "bdasl-inline-sha256"
        refs[key] = {"profile": primary, "cid": choices.pop(primary), "alternates": choices}
    return {"format": FORMAT, "source": source, "profiles": profile_table(), "blocks": blocks,
            "rows": rows_with_refs(plan, refs.__getitem__)}


def verify(plan, manifest):
    if manifest["format"] != FORMAT or manifest["source"] != plan_source(plan):
        raise ValueError("manifest format/source mismatch")
    if manifest["profiles"] != profile_table() or set(manifest["blocks"]) != set(ALGORITHMS):
        raise ValueError("profile mismatch")
    decoded = {}
    for profile, (algorithm, code) in ALGORITHMS.items():
        for cid, block in manifest["blocks"][profile].items():
            expected = read_cid(cid, code)
            if not re.fullmatch(r"(?:[0-9a-f]{2})+", block["hex"]):
                raise ValueError("noncanonical payload hex")
            payload = bytes.fromhex(block["hex"])
            if digest(algorithm, payload) != expected:
                raise ValueError(f"digest mismatch: {profile}/{cid}")
            try:
                actual = decode(payload)
            except ValueError as error:
                raise ValueError(f"invalid wire: {profile}/{cid}: {error}") from error
            if block["decoded"] != actual:
                raise ValueError("decoded tree does not match wire")
            decoded[profile, cid] = actual

    original_rows = plan["rows"]
    if len(manifest["rows"]) != len(original_rows):
        raise ValueError("row count mismatch")

    def recover_ref(ref):
        primary = ref["profile"]
        choices = ref["alternates"]
        if primary != "bdasl-inline-sha256" or set(choices) != {"bdasl-inline-blake3"}:
            raise ValueError("row reference profile mismatch")
        tree = decoded.get((primary, ref["cid"]))
        alternate = decoded.get(("bdasl-inline-blake3", choices["bdasl-inline-blake3"]))
        if tree is None or alternate is None:
            raise ValueError("missing root block")
        if tree != alternate:
            raise ValueError("alternate profile decoded different syntax")
        return tree

    for wanted, actual in zip(original_rows, manifest["rows"], strict=True):
        wanted_roots, actual_roots = wanted["roots"], actual["roots"]
        if set(wanted_roots) != set(actual_roots) or len(wanted["assumptions"]) != len(actual["assumptions"]):
            raise ValueError("row coordinates differ from checked fixture plan")
        if any(recover_ref(actual_roots[role]) != plan["blocks"][key] for role, key in wanted_roots.items()):
            raise ValueError("row root decodes to a different coordinate")
        if any(recover_ref(ref) != plan["blocks"][key]
               for key, ref in zip(wanted["assumptions"], actual["assumptions"], strict=True)):
            raise ValueError("row assumption decodes to a different coordinate")
        if {**actual, "roots": wanted_roots, "assumptions": wanted["assumptions"]} != wanted:
            raise ValueError("row evidence or scope differs from checked fixture plan")


def load(path):
    def unique(items):
        result = dict(items)
        if len(result) != len(items):
            raise ValueError("duplicate JSON object key")
        return result

    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("build", "verify"))
    parser.add_argument("plan", type=Path)
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    try:
        plan = load(args.plan)
        if args.command == "build":
            manifest = build(plan)
            args.manifest.write_text(json.dumps(manifest, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
                                     encoding="utf-8")
        else:
            manifest = load(args.manifest)
        verify(plan, manifest)
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"fixture error: {error}\n")
    print(f"Verified {len(manifest['rows'])} rows against plan and "
          f"{sum(map(len, manifest['blocks'].values()))} blocks (SHA-256 and BLAKE3). "
          "No Lean proof replay or hash assumptions.", file=sys.stderr)


if __name__ == "__main__":
    main()
