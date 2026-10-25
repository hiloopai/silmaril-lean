#!/usr/bin/env python3
"""Run the documented seven-tool pipeline and check its observable behavior."""

import argparse
import shutil
import subprocess
import tempfile
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--bin-dir", type=Path, default=Path(".lake/build/bin"))
args = parser.parse_args()
bin_dir = args.bin_dir.resolve()
examples = Path(__file__).resolve().parent / "examples" / "release"
node = shutil.which("node")
if not node:
    parser.error("Node.js is required for independent execution")


def run(tool, *arguments):
    result = subprocess.run([str(bin_dir / tool), *map(str, arguments)],
                            capture_output=True, text=True, timeout=90)
    assert result.returncode == 0, (tool, result.returncode, result.stdout, result.stderr)
    return result


with tempfile.TemporaryDirectory(prefix="wasm-release-demo-") as directory:
    work = Path(directory)
    provider, consumer, optimized, linked, public, text, rebuilt = [
        work / name for name in ["provider.wasm", "consumer.wasm", "optimized.wasm",
                                "linked.wasm", "public.wasm", "public.wat", "rebuilt.wasm"]]
    run("wasm-as", examples / "provider.wat", "-o", provider)
    run("wasm-as", examples / "consumer.wat", "-o", consumer)
    run("wasm-opt", provider, "--dce", "-o", optimized)
    assert optimized.stat().st_size < provider.stat().st_size, "DCE did not remove the dead suffix"
    run("wasm-merge", optimized, "Provider", consumer, "Consumer", "-o", linked)
    result = run("wasm-metadce", linked, "--graph-file", examples / "roots.json", "-o", public)
    assert "applied" in result.stderr, result.stderr
    run("wasm-dis", public, "-o", text)
    run("wasm-as", text, "-o", rebuilt)
    assert run("wasm-shell", rebuilt, "--fuel", "100", "--invoke", "run").stdout.strip() == \
        "return [i32:42]"
    observed = subprocess.run([node, "-e", """
const fs = require('fs');
for (const path of process.argv.slice(1)) {
  const instance = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(path)));
  if (instance.exports.run() !== 42) throw Error('wrong linked result');
  if (Object.keys(instance.exports).join(',') !== 'run') throw Error('wrong public interface');
}
""", str(public), str(rebuilt)], capture_output=True, text=True, timeout=30)
    assert observed.returncode == 0, observed.stderr

    constructor, initialized = work / "constructor.wasm", work / "initialized.wasm"
    run("wasm-as", examples / "constructor.wat", "-o", constructor)
    result = run("wasm-ctor-eval", constructor, "-o", initialized)
    assert "transformed" in result.stderr, result.stderr
    assert initialized.read_bytes() != constructor.read_bytes()
    assert run("wasm-shell", initialized, "--fuel", "100", "--invoke", "get").stdout.strip() == \
        "return [i32:9]"
    observed = subprocess.run([node, "-e", """
const fs = require('fs');
for (const path of process.argv.slice(1)) {
  const instance = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(path)));
  if (instance.exports.get() !== 9 || instance.exports.state.value !== 9)
    throw Error('wrong constructor state');
}
""", str(constructor), str(initialized)], capture_output=True, text=True, timeout=30)
    assert observed.returncode == 0, observed.stderr

print("Seven-tool release demo passed: real DCE, linking, graph DCE, text round trip, execution and constructor serialization")
