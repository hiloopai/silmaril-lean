#!/usr/bin/env python3
"""Build, run and pin tiny static x86-64 Linux ELF probes for the LPS model.

A probe is a hand-written GNU as file under PROBES (`<name>.s`) with a
declaration and expectation file (`<name>.json`). This tool

* builds it deterministically (`build.sh`: as + ld, one R+X PT_LOAD, no libc, no
  build-id) and pins the ELF bytes in SHA256SUMS;
* runs it in a fresh temporary work directory that holds only the declared input
  files, with the declared stdin, a cleared environment and resource limits,
  under one of several execution backends (see BACKENDS below), recording the raw
  syscall trace (numbers, raw arguments, raw returns), the bytes written to
  stdout/stderr, and the exit status or the killing signal;
* writes the expectation JSON (`record`), generates the Lean data module that the
  Lean theorems quote (`gen-lean`), and checks (`--check`) that
  sources -> bytes -> sha256 -> Lean module -> JSON -> live runs all agree, on every
  available backend, failing on any disagreement between backends.

Backends (recorded in the JSON as `recorded.backend` with the host kernel and the
tool versions):

* container: podman or docker with `--network none --read-only`, a tmpfs, only the
  work directory bound, `--platform linux/amd64`, all capabilities dropped. This is
  the preferred isolation and works from macOS too. The default image runs the
  probe without a tracer (outcome and output only); set LPS_PROBES_CONTAINER_IMAGE
  to an image with strace at /usr/bin/strace to also record the trace.
* bwrap: bubblewrap with every namespace unshared and a read-only /usr. Detection
  runs a trivial sandbox first: hosts that restrict unprivileged user namespaces
  (for example Ubuntu 24.04 with kernel.apparmor_restrict_unprivileged_userns=1)
  report it unavailable, and the tool falls back.
* native: strace on the host, used only with guards: a fresh mkdtemp work
  directory as cwd, an empty environment, rlimits (CPU seconds, address space,
  file size, open files, NPROC=0 so the probe cannot fork, no core dumps), a
  static check that every declared path and every string in the source is
  relative and cannot escape (no '/' and no '..'), and strace fault injection that
  denies every syscall outside the probe's declared allowlist with EPERM. An
  injected denial makes the run fail loudly. The probe is stopped before execve,
  its limits are applied, and strace attaches to it, so the tracer itself is not
  constrained by NPROC=0.
* qemu-user: `qemu-x86_64 -d strace`, for non-x86 hosts and as an independent
  CPU emulation to cross-check against. qemu-user forwards syscalls to the host
  kernel: it is NOT isolation by itself. The same work-directory, environment and
  rlimit guards are applied, except NPROC (qemu starts a helper thread). Path: --qemu or LPS_PROBES_QEMU (default:
  qemu-x86_64-static or qemu-x86_64 on PATH).
* qemu-system: not implemented; the README gives a recipe for a full-VM backend.

Stdlib only. Nothing outside the temporary directories is written by a run.
"""
from __future__ import annotations

import argparse
import ctypes
import errno as errno_module
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import resource
import select
import shutil
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
PROBES = "examples/verification-projects/theorem-dev/lps-probes"
LEAN_DATA = "Silmaril/Process/LPS/Probes/Data"
LEAN_NAMESPACE = "Silmaril.Process.LPS.Probes.Data"
SHA_FILE = "SHA256SUMS"
BASE_ADDRESS = 0x400000
ADDR_NO_RANDOMIZE = 0x0040000
MASK64 = (1 << 64) - 1
WALL_TIMEOUT = 20.0

# Native x86-64 numbers (arch/x86/entry/syscalls/syscall_64.tbl) of the calls a
# probe may declare. qemu-user prints names; strace -X raw prints numbers.
SYSCALLS = {
    "read": 0, "write": 1, "open": 2, "close": 3, "stat": 4, "fstat": 5, "lseek": 8,
    "mmap": 9, "mprotect": 10, "munmap": 11, "brk": 12, "rt_sigaction": 13,
    "rt_sigprocmask": 14, "ioctl": 16, "pread64": 17, "pwrite64": 18, "readv": 19,
    "writev": 20, "sched_yield": 24, "mremap": 25, "madvise": 28, "dup": 32, "dup2": 33,
    "nanosleep": 35, "getpid": 39, "socket": 41, "clone": 56, "fork": 57, "vfork": 58,
    "execve": 59, "exit": 60, "wait4": 61, "kill": 62, "uname": 63, "fcntl": 72,
    "flock": 73, "fsync": 74, "fdatasync": 75, "ftruncate": 77, "getcwd": 79,
    "getuid": 102, "getgid": 104, "setuid": 105, "setgid": 106, "geteuid": 107,
    "getegid": 108, "getgroups": 115, "sigaltstack": 131, "prctl": 157,
    "arch_prctl": 158, "gettid": 186, "tkill": 200, "futex": 202,
    "sched_getaffinity": 204, "getdents64": 217, "set_tid_address": 218,
    "clock_gettime": 228, "exit_group": 231, "tgkill": 234, "openat": 257,
    "newfstatat": 262, "unlinkat": 263, "readlinkat": 267, "faccessat": 269,
    "pselect6": 270, "ppoll": 271, "pipe2": 293, "dup3": 292, "prlimit64": 302,
    "getrandom": 318, "clone3": 435, "faccessat2": 439,
}
NUMBERS = {number: name for name, number in SYSCALLS.items()}
# A probe may also declare a bare number in this range: no x86-64 kernel
# implements one (native calls end below 512 and x32 below 600), so the call can
# only fail with -ENOSYS. It exercises LPS's unknown-syscall (fail-closed) path.
UNIMPLEMENTED = range(600, 1024)


def unimplemented_number(call: str) -> int | None:
    """The number of an allowlist entry that names an unimplemented call."""
    if call.isdigit() and int(call) in UNIMPLEMENTED:
        return int(call)
    return None
SAFE_NAME = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_.-]*$")
PROBE_NAME = re.compile(r"^[a-z][a-z0-9_]*$")


class ProbeError(Exception):
    """A probe failed a build, pin, static, backend or agreement check."""


# ---------------------------------------------------------------------------
# Declarations and static checks


def probe_dir(root: Path) -> Path:
    return root / PROBES / "probes"


def load_declaration(root: Path, name: str) -> dict:
    path = probe_dir(root) / f"{name}.json"
    declaration = json.loads(path.read_text())
    if declaration.get("probe") != name:
        raise ProbeError(f"{path}: 'probe' must be {name!r}")
    return declaration


def probe_names(root: Path) -> list[str]:
    return sorted(path.stem for path in probe_dir(root).glob("*.json"))


def checked_relative(path: str) -> str:
    """A declared path must be a plain file name inside the work directory."""
    if not SAFE_NAME.match(path) or path in (".", "..") or "/" in path or ".." in path:
        raise ProbeError(f"unsafe probe path {path!r}: only relative names without '/' or '..'")
    return path


STRING_DIRECTIVE = re.compile(r'\.(?:ascii|asciz|string)\s+"((?:[^"\\]|\\.)*)"')


def static_check(declaration: dict, source: str) -> None:
    """Reject probes that could name anything outside their work directory."""
    name = declaration["probe"]
    if not PROBE_NAME.match(name):
        raise ProbeError(f"bad probe name {name!r}")
    inputs = declaration.get("inputs", {})
    for path in inputs.get("files", {}):
        checked_relative(path)
    for path in declaration.get("paths", []):
        checked_relative(path)
    for literal in STRING_DIRECTIVE.findall(source):
        if "/" in literal or ".." in literal:
            raise ProbeError(f"{name}: string literal {literal!r} could name a path outside the work directory")
    host_dependent(declaration)
    allow = declaration.get("allow")
    if not isinstance(allow, list) or not allow:
        raise ProbeError(f"{name}: declare a nonempty syscall allowlist 'allow'")
    for call in allow:
        if call not in SYSCALLS and unimplemented_number(call) is None:
            raise ProbeError(f"{name}: unknown syscall {call!r} in allowlist")
        if call in ("fork", "vfork", "clone", "clone3", "execve", "kill", "tkill", "tgkill"):
            raise ProbeError(f"{name}: {call} is never allowed in a probe")


# ---------------------------------------------------------------------------
# Build and ELF facts


IMAGE_FLAGS = {"rx": 5, "rwx": 7}


def image_kind(declaration: dict) -> str:
    """The PT_LOAD permissions: "rx" (default, probes/probe.ld) or "rwx"
    (probes/probe-rwx.ld, for probes that read into a buffer of their image)."""
    kind = declaration.get("image", "rx")
    if kind not in IMAGE_FLAGS:
        raise ProbeError(f"{declaration.get('probe')}: image must be one of {sorted(IMAGE_FLAGS)}")
    return kind


def build(root: Path, name: str, output: Path, image: str = "rx") -> bytes:
    source = probe_dir(root) / f"{name}.s"
    script = root / PROBES / "build.sh"
    result = subprocess.run(["sh", str(script), str(source), str(output), image], capture_output=True, text=True)
    if result.returncode != 0:
        raise ProbeError(f"{name}: build failed: {result.stderr.strip()}")
    return output.read_bytes()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_pins(root: Path) -> dict[str, str]:
    pins = {}
    path = root / PROBES / SHA_FILE
    if path.exists():
        for line in path.read_text().splitlines():
            if line.strip():
                digest, file_name = line.split()
                pins[file_name] = digest
    return pins


def write_pins(root: Path, pins: dict[str, str]) -> None:
    lines = [f"{pins[key]}  {key}\n" for key in sorted(pins)]
    (root / PROBES / SHA_FILE).write_text("".join(lines))


def le(data: bytes, offset: int, size: int) -> int:
    return int.from_bytes(data[offset:offset + size], "little")


def elf_facts(data: bytes, image: str = "rx") -> dict:
    """The ELF64 header and its single PT_LOAD, checked against the probe layout."""
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1 or data[6] != 1:
        raise ProbeError("not a little-endian ELF64 file")
    header = {
        "osABI": data[7], "abiVersion": data[8], "fileType": le(data, 16, 2),
        "machine": le(data, 18, 2), "version": le(data, 20, 4), "entry": le(data, 24, 8),
        "programOffset": le(data, 32, 8), "sectionOffset": le(data, 40, 8),
        "flags": le(data, 48, 4), "headerSize": le(data, 52, 2),
        "programEntrySize": le(data, 54, 2), "programCount": le(data, 56, 2),
        "sectionEntrySize": le(data, 58, 2), "sectionCount": le(data, 60, 2),
        "sectionNameIndex": le(data, 62, 2),
    }
    if header["programCount"] != 1 or header["programOffset"] != 64:
        raise ProbeError("a probe has exactly one program header right after the ELF header")
    offset = header["programOffset"]
    program = {
        "kind": le(data, offset, 4), "flags": le(data, offset + 4, 4),
        "offset": le(data, offset + 8, 8), "virtualAddress": le(data, offset + 16, 8),
        "physicalAddress": le(data, offset + 24, 8), "fileSize": le(data, offset + 32, 8),
        "memorySize": le(data, offset + 40, 8), "alignment": le(data, offset + 48, 8),
    }
    flags = IMAGE_FLAGS[image]
    if (program["kind"], program["flags"], program["offset"], program["virtualAddress"]) != (1, flags, 0, BASE_ADDRESS):
        raise ProbeError(f"the PT_LOAD must be {image.upper()} at file offset 0 and address {BASE_ADDRESS:#x}")
    if program["fileSize"] != program["memorySize"] or program["fileSize"] > len(data):
        raise ProbeError("the PT_LOAD must be fully file-backed (no .bss)")
    if not BASE_ADDRESS + 120 <= header["entry"] < BASE_ADDRESS + program["fileSize"]:
        raise ProbeError("the entry point must lie in the loaded code")
    return {"header": header, "program": program}


# ---------------------------------------------------------------------------
# Trace parsing


def parse_return(text: str) -> int | None:
    text = text.strip()
    if text.startswith("?"):
        return None
    match = re.match(r"^(-?(?:0x[0-9a-fA-F]+|\d+))(.*)$", text)
    if not match:
        raise ProbeError(f"unparsed syscall return {text!r}")
    value = int(match.group(1), 0)
    rest = match.group(2)
    if value == -1:
        name = re.search(r"\b(E[A-Z0-9]+)\b", rest)
        number = re.search(r"errno[= ](\d+)", rest)
        if name and hasattr(errno_module, name.group(1)):
            return -getattr(errno_module, name.group(1))
        if number:
            return -int(number.group(1))
    return value


def parse_args(text: str) -> list[int]:
    args = []
    for part in [piece.strip() for piece in text.split(",") if piece.strip()]:
        try:
            # Raw register values: qemu-user prints some arguments signed (exit(-6)),
            # strace prints them unsigned; both mean the same 64-bit register.
            args.append(int(part, 0) % 2 ** 64)
        except ValueError as error:
            raise ProbeError(f"non-raw syscall argument {part!r}") from error
    return args


STRACE_LINE = re.compile(r"^(\d+)\s+\[\s*(\d+)\]\s+(\w+)\((.*)\)\s*=\s*(.*)$")
STRACE_EXIT = re.compile(r"^(\d+)\s+\[\s*(\d+)\]\s+(exit|exit_group)\((.*)\)\s*=\s*\?$")


def parse_strace(text: str) -> list[dict]:
    """Raw syscalls after the probe's own successful execve.

    Each entry is {nr, name, args, ret}; ret is None for calls that do not return.
    Injected denials, unfinished/resumed (multi-thread) records and other tracee
    pids are rejected rather than silently dropped."""
    calls: list[dict] = []
    started = False
    pids = set()
    for line in text.splitlines():
        if "(INJECTED)" in line:
            raise ProbeError(f"denied a syscall outside the allowlist: {line.strip()}")
        if "<unfinished" in line or "resumed>" in line:
            raise ProbeError(f"interleaved tracee records: {line.strip()}")
        match = STRACE_LINE.match(line)
        if not match:
            continue
        pid, number, name, args, ret = match.groups()
        if not started:
            if name == "execve" and ret.strip().startswith("0"):
                started = True
            continue
        pids.add(pid)
        calls.append({"nr": int(number), "name": name, "args": parse_args(args), "ret": parse_return(ret)})
    if not started:
        raise ProbeError("no successful execve of the probe in the trace")
    if len(pids) > 1:
        raise ProbeError(f"more than one tracee: {sorted(pids)}")
    return calls


QEMU_LINE = re.compile(r"^(\d+)\s+(\w+)\((.*?)\)(?:\s*=\s*(.*))?$")


QEMU_UNKNOWN = re.compile(r"^(\d+)\s+Unknown syscall (\d+)$")
# qemu-user prints all six argument registers for these calls; strace prints the
# arguments the call takes. Only that many are compared.
QEMU_ARITY = {"arch_prctl": 2}
# qemu-user prints these arguments as a C int: only their low 32 bits are known.
QEMU_INT_ARGS = {"exit": [0], "exit_group": [0]}


def parse_qemu(text: str) -> list[dict]:
    """qemu-user's `-d strace` log. Arguments are normalized to strace's raw form
    (unsigned 64-bit, `(nil)` is 0). qemu reports an unimplemented number only as
    `Unknown syscall N`, without arguments or return, and decodes some arguments
    symbolically (`openat` prints `-100,"in.txt",O_RDONLY`): such fields are marked
    `unreported` and not compared."""
    calls = []
    for line in text.splitlines():
        unknown = QEMU_UNKNOWN.match(line.strip())
        if unknown:
            number = int(unknown.group(2))
            if number not in UNIMPLEMENTED:
                raise ProbeError(f"qemu-user does not know syscall {number}")
            calls.append({"nr": number, "name": f"syscall_{number:#x}", "args": [], "ret": None,
                          "unreported": ["args", "ret"]})
            continue
        match = QEMU_LINE.match(line.strip())
        if not match:
            continue
        _, name, args, ret = match.groups()
        if name not in SYSCALLS:
            raise ProbeError(f"qemu-user reported an undeclared syscall name {name!r}")
        try:
            values = [value & MASK64 for value in parse_args(args.replace("(nil)", "0"))]
        except ProbeError:
            values = None
        if values is not None and name in QEMU_ARITY:
            values = values[:QEMU_ARITY[name]]
        call = {"nr": SYSCALLS[name], "name": name, "args": values if values is not None else [],
                "ret": None if ret is None else parse_return(ret)}
        if values is None:
            call["unreported"] = ["args"]
        if name in QEMU_INT_ARGS:
            call["low32"] = QEMU_INT_ARGS[name]
        calls.append(call)
    return calls


# ---------------------------------------------------------------------------
# Work directories and guards


def prepare(declaration: dict, elf: bytes) -> tuple[Path, Path]:
    """A fresh work directory (probe + declared inputs) and a capture directory."""
    work = Path(tempfile.mkdtemp(prefix="lps-probe-work-"))
    capture = Path(tempfile.mkdtemp(prefix="lps-probe-capture-"))
    inputs = declaration.get("inputs", {})
    for path, contents in inputs.get("files", {}).items():
        (work / checked_relative(path)).write_bytes(bytes.fromhex(contents))
    probe = work / "probe"
    probe.write_bytes(elf)
    probe.chmod(0o500)
    (capture / "stdin").write_bytes(bytes.fromhex(inputs.get("stdinHex", "")))
    return work, capture


def limits(address_space: int | None, nproc: bool = True) -> list[tuple[int, int]]:
    chosen = [(resource.RLIMIT_CPU, 2), (resource.RLIMIT_FSIZE, 1 << 20),
              (resource.RLIMIT_NOFILE, 16), (resource.RLIMIT_CORE, 0)]
    if address_space is not None:
        chosen.append((resource.RLIMIT_AS, address_space))
    if nproc:
        chosen.append((resource.RLIMIT_NPROC, 0))
    return chosen


def apply_limits(chosen: list[tuple[int, int]]) -> None:
    for kind, value in chosen:
        resource.setrlimit(kind, (value, value))



def outcome_of(status: int) -> dict:
    if os.WIFEXITED(status):
        return {"exit": os.WEXITSTATUS(status)}
    if os.WIFSIGNALED(status):
        return {"signal": os.WTERMSIG(status)}
    raise ProbeError(f"unexpected wait status {status:#x}")


def outcome_of_returncode(code: int) -> dict:
    return {"signal": -code} if code < 0 else {"exit": code}


def final_files(work: Path) -> dict[str, str]:
    """The file system the probe leaves behind: every regular file of the work
    directory except the probe binary itself (the model loads the image separately
    and its launch file system does not contain it), name -> hex contents, sorted
    by name. Anything else (a directory, a symlink, an unsafe name) fails loudly."""
    files = {}
    for entry in sorted(work.iterdir(), key=lambda item: item.name.encode()):
        if entry.name == "probe":
            continue
        checked_relative(entry.name)
        if entry.is_symlink() or not entry.is_file():
            raise ProbeError(f"the probe left a non-regular entry {entry.name!r}")
        entry.chmod(0o600)  # a probe may create a file with mode 0
        files[entry.name] = entry.read_bytes().hex()
    return files


def observation(capture: Path, trace: list[dict] | None, outcome: dict, work: Path) -> dict:
    return {"syscalls": trace, "stdoutHex": (capture / "stdout").read_bytes().hex(),
            "stderrHex": (capture / "stderr").read_bytes().hex(), "outcome": outcome,
            "files": final_files(work)}


def inject_set(declaration: dict) -> str:
    # The probe's own execve is traced first; it must succeed for anything to run.
    # strace has no name for an unimplemented number; it is not in strace's table,
    # so the inverted set does not cover it and the kernel's -ENOSYS is observed.
    named = [call for call in declaration["allow"] if unimplemented_number(call) is None]
    return "!" + ",".join(["execve", *named])


def which(name: str) -> str | None:
    return shutil.which(name)


def version_of(command: list[str]) -> str:
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=10)
    except (OSError, subprocess.TimeoutExpired):
        return "unavailable"
    text = (result.stdout or result.stderr).strip().splitlines()
    return text[0] if text else "unknown"


# ---------------------------------------------------------------------------
# Backends


class Backend:
    name = ""
    traces = True
    isolation = ""

    def available(self) -> tuple[bool, str]:
        raise NotImplementedError

    def run(self, declaration: dict, elf: bytes) -> dict:
        raise NotImplementedError

    def tools(self) -> dict[str, str]:
        return {}


class NativeBackend(Backend):
    name = "native"
    isolation = "guarded host run: temp cwd, empty env, rlimits incl. NPROC=0, path check, strace EPERM allowlist"

    def available(self):
        if platform.machine() not in ("x86_64", "AMD64"):
            return False, "host is not x86-64"
        if sys.platform != "linux":
            return False, "host is not Linux"
        if not which("strace"):
            return False, "strace not found"
        return True, "strace on an x86-64 Linux host"

    def tools(self):
        return {"strace": version_of(["strace", "-V"])}

    def run(self, declaration, elf):
        work, capture = prepare(declaration, elf)
        try:
            return self._run(declaration, work, capture)
        finally:
            shutil.rmtree(work, ignore_errors=True)
            shutil.rmtree(capture, ignore_errors=True)

    def _run(self, declaration, work, capture):
        chosen = limits(64 << 20)
        stdin = os.open(capture / "stdin", os.O_RDONLY)
        stdout = os.open(capture / "stdout", os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        stderr = os.open(capture / "stderr", os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        libc = ctypes.CDLL(None, use_errno=True)
        pid = os.fork()
        if pid == 0:  # child: guards, stop, then exec the probe once strace is attached
            try:
                os.dup2(stdin, 0)
                os.dup2(stdout, 1)
                os.dup2(stderr, 2)
                os.closerange(3, 1 << 16)
                os.chdir(work)
                libc.prctl(0x59616D61, ctypes.c_ulong(-1 & 0xFFFFFFFFFFFFFFFF), 0, 0, 0)  # PR_SET_PTRACER_ANY
                # ADDR_NO_RANDOMIZE (as `setarch -R`): a deterministic stack, so a
                # stack address a probe passes to a call is reproducible and lies in
                # the LPS launch envelope (its stack window is 2 GiB below TASK_SIZE,
                # Linux's stack randomization spans 16 GiB).
                libc.personality(ADDR_NO_RANDOMIZE)
                apply_limits(chosen)
                os.kill(os.getpid(), signal.SIGSTOP)
                os.execve("./probe", ["./probe"], {})
            finally:
                os._exit(127)
        for descriptor in (stdin, stdout, stderr):
            os.close(descriptor)
        _, status = os.waitpid(pid, os.WUNTRACED)
        if not os.WIFSTOPPED(status):
            raise ProbeError(f"guarded child did not stop before exec (status {status:#x})")
        trace_path = capture / "trace"
        command = ["strace", "-f", "-n", "-X", "raw", "-e", "raw=all", "-e", "trace=all",
                   "-e", f"inject={inject_set(declaration)}:error=EPERM",
                   "-o", str(trace_path), "-p", str(pid)]
        tracer = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                  stderr=subprocess.PIPE, env={"PATH": os.environ.get("PATH", "/usr/bin:/bin")})
        messages = b""
        try:
            deadline = time.monotonic() + WALL_TIMEOUT
            while b"attached" not in messages:
                remaining = deadline - time.monotonic()
                ready, _, _ = select.select([tracer.stderr], [], [], max(remaining, 0))
                if not ready:
                    raise ProbeError("strace did not attach in time")
                chunk = os.read(tracer.stderr.fileno(), 4096)
                if not chunk:
                    raise ProbeError(f"strace exited before attaching: {messages.decode(errors='replace')}")
                messages += chunk
            os.kill(pid, signal.SIGCONT)
            status = self._wait(pid, deadline)
            tracer.wait(timeout=WALL_TIMEOUT)
        except BaseException:
            try:
                os.kill(pid, signal.SIGKILL)
                os.waitpid(pid, 0)
            except (ProcessLookupError, ChildProcessError):
                pass
            tracer.kill()
            tracer.wait()
            raise
        finally:
            tracer.stderr.close()
        trace = parse_strace(trace_path.read_text())
        return observation(capture, trace, outcome_of(status), work)

    @staticmethod
    def _wait(pid: int, deadline: float) -> int:
        while True:
            done, status = os.waitpid(pid, os.WNOHANG)
            if done:
                return status
            if time.monotonic() > deadline:
                raise ProbeError("probe exceeded the wall-clock limit")
            time.sleep(0.005)


def default_qemu() -> str | None:
    configured = os.environ.get("LPS_PROBES_QEMU")
    if configured:
        return configured
    return which("qemu-x86_64-static") or which("qemu-x86_64")


class QemuUserBackend(Backend):
    name = "qemu-user"
    isolation = "CPU emulation only: syscalls go to the host kernel (not isolation); temp cwd, empty env, rlimits"

    def __init__(self, path: str | None = None):
        self.path = path or default_qemu()

    def available(self):
        if not self.path or not Path(self.path).is_file() or not os.access(self.path, os.X_OK):
            return False, "qemu-x86_64 not found (set LPS_PROBES_QEMU or --qemu)"
        return True, self.path

    def tools(self):
        return {"qemu-user": version_of([self.path, "--version"])}

    def run(self, declaration, elf):
        work, capture = prepare(declaration, elf)
        try:
            log = capture / "qemu.log"
            # qemu-user starts a helper (RCU) thread, which RLIMIT_NPROC=0 forbids.
            chosen = limits(None, nproc=False)
            with open(capture / "stdin", "rb") as stdin, open(capture / "stdout", "wb") as stdout, \
                    open(capture / "stderr", "wb") as stderr:
                result = subprocess.run([self.path, "-d", "strace", "-D", str(log), "./probe"], cwd=work,
                                        env={}, stdin=stdin, stdout=stdout, stderr=stderr,
                                        preexec_fn=lambda: apply_limits(chosen), timeout=WALL_TIMEOUT)
            trace = parse_qemu(log.read_text() if log.exists() else "")
            return observation(capture, trace, outcome_of_returncode(result.returncode), work)
        finally:
            shutil.rmtree(work, ignore_errors=True)
            shutil.rmtree(capture, ignore_errors=True)


class BwrapBackend(Backend):
    name = "bwrap"
    isolation = "bubblewrap: all namespaces unshared, read-only /usr, only the work dir writable, strace EPERM allowlist"

    def available(self):
        path = which("bwrap")
        if not path:
            return False, "bwrap not found"
        if not which("strace"):
            return False, "strace not found"
        probe = subprocess.run([path, "--unshare-all", "--ro-bind", "/", "/", "true"], capture_output=True, text=True)
        if probe.returncode != 0:
            return False, "bwrap cannot create namespaces here: " + (probe.stderr.strip() or "unknown error")
        return True, path

    def tools(self):
        return {"bwrap": version_of(["bwrap", "--version"]), "strace": version_of(["strace", "-V"])}

    def command(self, declaration, work: Path, capture: Path) -> list[str]:
        strace = os.path.realpath(which("strace") or "/usr/bin/strace")
        command = ["bwrap", "--unshare-all", "--die-with-parent", "--new-session", "--clearenv",
                   "--ro-bind", "/usr", "/usr"]
        for link in ("lib", "lib64", "bin"):
            if Path("/usr", link).exists():
                command += ["--symlink", f"usr/{link}", f"/{link}"]
        command += ["--proc", "/proc", "--dev", "/dev", "--bind", str(work), "/work",
                    "--bind", str(capture), "/capture", "--chdir", "/work"]
        # ADDR_NO_RANDOMIZE inside the sandbox (entering the user namespace clears
        # a personality set outside it): a deterministic stack, as on native.
        setarch = which("setarch")
        if setarch:
            command += [os.path.realpath(setarch), platform.machine(), "-R"]
        command += [strace, "-f", "-n", "-X", "raw", "-e", "raw=all", "-e", "trace=all",
                    "-e", f"inject={inject_set(declaration)}:error=EPERM", "-o", "/capture/trace", "./probe"]
        return command

    def run(self, declaration, elf):
        work, capture = prepare(declaration, elf)
        try:
            chosen = limits(None, nproc=False)  # bwrap and strace fork; the namespace and EPERM set stop the probe
            with open(capture / "stdin", "rb") as stdin, open(capture / "stdout", "wb") as stdout, \
                    open(capture / "stderr", "wb") as stderr:
                result = subprocess.run(self.command(declaration, work, capture), stdin=stdin, stdout=stdout,
                                        stderr=stderr, preexec_fn=lambda: apply_limits(chosen), timeout=WALL_TIMEOUT)
            trace_text = (capture / "trace").read_text()
            trace = parse_strace(trace_text)
            return observation(capture, trace, strace_outcome(trace_text, result.returncode), work)
        finally:
            shutil.rmtree(work, ignore_errors=True)
            shutil.rmtree(capture, ignore_errors=True)


SIGNALS = {member.name: int(member) for member in signal.Signals}


def strace_outcome(text: str, returncode: int) -> dict:
    """strace's own record of the tracee's end (strace exits with the tracee's status)."""
    exited = re.search(r"\+\+\+ exited with (\d+) \+\+\+", text)
    if exited:
        return {"exit": int(exited.group(1))}
    killed = re.search(r"\+\+\+ killed by (SIG[A-Z0-9]+)", text)
    if killed:
        return {"signal": SIGNALS[killed.group(1)]}
    return outcome_of_returncode(returncode)


BUSYBOX = "docker.io/library/busybox:1.36"


class ContainerBackend(Backend):
    name = "container"
    isolation = "podman/docker: --network none --read-only, tmpfs, only the work dir bound, caps dropped, pids limit"

    def __init__(self):
        self.engine = None
        self.image = os.environ.get("LPS_PROBES_CONTAINER_IMAGE")
        self.traces = bool(self.image)

    def available(self):
        for engine in ("podman", "docker"):
            path = which(engine)
            if path and subprocess.run([path, "info"], capture_output=True).returncode == 0:
                self.engine = path
                return True, path
        return False, "neither podman nor docker is usable"

    def tools(self):
        return {"container": version_of([self.engine or "docker", "--version"]),
                "image": self.image or f"{BUSYBOX} (no tracer)"}

    def ensure_image(self) -> None:
        """Pull the image once, outside any capture: a pull inside `run` prints
        its progress into the probe's captured stderr."""
        image = self.image or BUSYBOX
        engine = self.engine or "docker"
        if subprocess.run([engine, "image", "inspect", image], capture_output=True).returncode != 0:
            pulled = subprocess.run([engine, "pull", "-q", image], capture_output=True, timeout=600)
            if pulled.returncode != 0:
                raise ProbeError(f"container: cannot pull {image}: "
                                 f"{pulled.stderr.decode(errors='replace').strip()}")

    def command(self, declaration, work: Path, capture: Path) -> list[str]:
        base = [self.engine or "docker", "run", "--rm", "-i", "--network", "none", "--read-only",
                "--tmpfs", "/tmp:rw,noexec,size=1m", "--platform", "linux/amd64", "--cap-drop", "ALL",
                "--security-opt", "no-new-privileges", "--pids-limit", "8", "--memory", "64m",
                "--ulimit", "nproc=64", "--ulimit", "cpu=2", "--ulimit", "fsize=1048576",
                "-v", f"{work}:/work:rw", "-w", "/work", "--env-file", "/dev/null", "--pull", "never"]
        if self.image:
            return base + ["--cap-add", "SYS_PTRACE", "-v", f"{capture}:/capture:rw", self.image,
                           "/usr/bin/strace", "-f", "-n", "-X", "raw", "-e", "raw=all", "-e", "trace=all",
                           "-e", f"inject={inject_set(declaration)}:error=EPERM", "-o", "/capture/trace", "./probe"]
        return base + ["--entrypoint", "/work/probe", BUSYBOX]

    def run(self, declaration, elf):
        self.ensure_image()
        work, capture = prepare(declaration, elf)
        try:
            with open(capture / "stdin", "rb") as stdin, open(capture / "stdout", "wb") as stdout, \
                    open(capture / "stderr", "wb") as stderr:
                result = subprocess.run(self.command(declaration, work, capture), stdin=stdin, stdout=stdout,
                                        stderr=stderr, timeout=120)
            if self.image:
                text = (capture / "trace").read_text()
                return observation(capture, parse_strace(text), strace_outcome(text, result.returncode), work)
            code = result.returncode
            # Without a tracer the engine reports a kill by signal n as status
            # 128 + n, so a status above 128 is that exit status or that signal.
            outcome = {"exitOrSignal": code} if code > 128 else {"exit": code}
            return observation(capture, None, outcome, work)
        finally:
            shutil.rmtree(work, ignore_errors=True)
            shutil.rmtree(capture, ignore_errors=True)


class QemuSystemBackend(Backend):
    name = "qemu-system"
    isolation = "full VM (recipe only, see README)"

    def available(self):
        return False, "not implemented; see the qemu-system recipe in the README"


def all_backends(qemu: str | None = None) -> list[Backend]:
    return [ContainerBackend(), BwrapBackend(), NativeBackend(), QemuUserBackend(qemu), QemuSystemBackend()]


def select_backends(names: list[str] | None, qemu: str | None) -> list[Backend]:
    """Available backends, in preference order, optionally restricted by name."""
    chosen = []
    for backend in all_backends(qemu):
        if names and backend.name not in names:
            continue
        ok, reason = backend.available()
        if ok:
            chosen.append(backend)
        elif names:
            raise ProbeError(f"backend {backend.name} unavailable: {reason}")
    if not chosen:
        raise ProbeError("no execution backend is available")
    return chosen


def primary(backends: list[Backend]) -> Backend:
    """The most isolated tracing backend, else the first available one."""
    for backend in backends:
        if backend.traces:
            return backend
    return backends[0]


def environment(backends: list[Backend]) -> dict:
    tools = {"as": version_of(["as", "--version"]), "ld": version_of(["ld", "--version"])}
    for backend in backends:
        tools.update(backend.tools())
    return {"kernel": platform.release(), "machine": platform.machine(), "tools": dict(sorted(tools.items()))}


# ---------------------------------------------------------------------------
# Comparison and recording


HOST = "<host>"


def host_dependent(declaration: dict) -> list[dict]:
    """The declared host-dependent trace fields: `{"call": i, "ret": true, "why": ...}`
    or `{"call": i, "arg": j, "why": ...}`. A process id, a user id or a stack
    address differs between runs, hosts or backends; such a field must be present in
    every run but its value is not compared. The JSON keeps the recorded value, and
    the Lean proofs that quote it instantiate the corresponding launch parameter or
    nondeterministic choice with it."""
    marks = declaration.get("hostDependent", [])
    if not isinstance(marks, list):
        raise ProbeError("'hostDependent' must be a list")
    for mark in marks:
        if not isinstance(mark, dict) or not isinstance(mark.get("call"), int) or not mark.get("why") or \
                (mark.get("ret") is not True) == (not isinstance(mark.get("arg"), int)):
            raise ProbeError(f"bad hostDependent entry {mark!r}: name a call, ret or arg, and why")
    return marks


def masked_calls(calls: list[dict], marks: list[dict]) -> list[tuple]:
    rows = []
    for index, call in enumerate(calls):
        unreported = call.get("unreported", [])
        args = HOST if "args" in unreported else list(call["args"])
        ret = HOST if "ret" in unreported else call["ret"]
        for mark in marks:
            if mark["call"] != index:
                continue
            if mark.get("ret") is True and ret != HOST:
                ret = HOST if isinstance(ret, int) else ret
            elif args != HOST and isinstance(mark.get("arg"), int) and mark["arg"] < len(args):
                args[mark["arg"]] = HOST
        if args != HOST:
            for position in call.get("low32", []):
                if position < len(args) and args[position] != HOST:
                    args[position] = ("low32", args[position] & 0xFFFFFFFF)
        rows.append((call["nr"], args, ret))
    return rows


def same_arg(first, second) -> bool:
    if isinstance(first, tuple) or isinstance(second, tuple):
        low = [value[1] if isinstance(value, tuple) else value & 0xFFFFFFFF for value in (first, second)]
        return low[0] == low[1]
    return first == second


def rows_agree(want: list[tuple], got: list[tuple]) -> bool:
    if len(want) != len(got):
        return False
    for (nr, args, ret), (nr2, args2, ret2) in zip(want, got):
        if nr != nr2 or (HOST not in (ret, ret2) and ret != ret2):
            return False
        if HOST not in (args, args2) and (len(args) != len(args2) or
                                          not all(same_arg(a, b) for a, b in zip(args, args2))):
            return False
    return True


def same_outcome(expected: dict | None, observed: dict | None) -> bool:
    """Equal outcomes. An untraced container status above 128 (`exitOrSignal`)
    matches that exit status or the signal it encodes."""
    if isinstance(observed, dict) and "exitOrSignal" in observed:
        code = observed["exitOrSignal"]
        return expected in ({"exit": code}, {"signal": code - 128})
    return expected == observed


def disagreements(expected: dict, observed: dict, label: str, marks: list[dict] | None = None) -> list[str]:
    problems = []
    if not same_outcome(expected.get("outcome"), observed.get("outcome")):
        problems.append(f"{label}: outcome expected {expected.get('outcome')!r}, "
                        f"observed {observed.get('outcome')!r}")
    for key in ("stdoutHex", "stderrHex"):
        if expected.get(key) != observed.get(key):
            problems.append(f"{label}: {key} expected {expected.get(key)!r}, observed {observed.get(key)!r}")
    if files_of(expected) != files_of(observed):
        problems.append(f"{label}: final files expected {files_of(expected)!r}, observed {files_of(observed)!r}")
    if observed.get("syscalls") is not None:
        want = masked_calls(expected["syscalls"], marks or [])
        got = masked_calls(observed["syscalls"], marks or [])
        if not rows_agree(want, got):
            problems.append(f"{label}: syscalls expected {want}, observed {got}")
    return problems


def stdin_consumed(declaration: dict, syscalls: list[dict]) -> bytes:
    """The prefix of the declared stdin that the probe's read(0, ...) calls returned."""
    total = sum(call["ret"] for call in syscalls
                if call["name"] == "read" and call["args"] and call["args"][0] == 0 and (call["ret"] or 0) > 0)
    stdin = bytes.fromhex(declaration.get("inputs", {}).get("stdinHex", ""))
    if total > len(stdin):
        raise ProbeError(f"the reads of stdin returned {total} bytes, more than the declared {len(stdin)}")
    return stdin[:total]


def files_of(observation: dict) -> dict[str, str]:
    """The final files of an observation; fixtures recorded before the kit
    observed files (no `files` key) left none behind."""
    return observation.get("files", {})


def consistent_output(observed: dict) -> None:
    """The bytes captured on stdout/stderr are exactly what the write calls returned,
    all stdin reads precede all writes and all stdout writes precede all stderr writes
    (the Lean `Observed.events` lists read bytes, then stdout, then stderr bytes, so
    another interleaving could not be represented)."""
    totals = {1: 0, 2: 0}
    order = []
    for call in observed["syscalls"] or []:
        if call["name"] == "read" and call["args"] and call["args"][0] == 0 and (call["ret"] or 0) > 0:
            order.append(0)
        if call["name"] == "write" and call["args"] and call["args"][0] in totals and (call["ret"] or 0) > 0:
            totals[call["args"][0]] += call["ret"]
            order.append(call["args"][0])
    if observed["syscalls"] is not None:
        if totals[1] != len(observed["stdoutHex"]) // 2 or totals[2] != len(observed["stderrHex"]) // 2:
            raise ProbeError(f"captured output {totals} disagrees with write returns")
        if order != sorted(order):
            raise ProbeError("stdin reads, stdout and stderr writes interleave; Observed.events cannot represent it")


def normalize_stack(declaration: dict, observed: dict) -> None:
    """Replace the declared entry-stack-pointer arguments by "sp".

    `stackArgs` lists `[call index, argument index]` pairs at which the probe
    passes its entry RSP (a buffer on the initial stack). Linux randomizes that
    address, and the model's entry SP is a launch parameter, so the fixture
    records the symbol "sp" and the Lean statement requires the model's call to
    pass the model's entry SP there. Every listed argument must hold the same
    value within one run."""
    calls = observed.get("syscalls")
    positions = declaration.get("stackArgs", [])
    if calls is None or not positions:
        return
    values = set()
    for index, position in positions:
        if index >= len(calls):
            raise ProbeError(f"stackArgs names call {index}, the run made {len(calls)} calls")
        if "args" in calls[index].get("unreported", []):
            continue  # printed symbolically (qemu-user): nothing to normalize
        args = calls[index]["args"]
        if position >= len(args) or not isinstance(args[position], int):
            raise ProbeError(f"stackArgs names argument {position} of call {index}: {args}")
        values.add(args[position])
        args[position] = "sp"
    if len(values) > 1:
        raise ProbeError(f"the declared stack arguments differ within one run: {sorted(values)}")


def usable_backends(declaration: dict, backends: list[Backend]) -> list[Backend]:
    """The backends a probe runs on: all of them except those its `skipBackends`
    names (backend -> reason). qemu-user, for example, holds its own log file open
    at descriptor 3, so a guest's lowest free descriptor there is 4; probes that
    observe descriptor numbers skip it. At least one backend must remain."""
    skipped = declaration.get("skipBackends", {})
    if not isinstance(skipped, dict) or not all(isinstance(reason, str) and reason for reason in skipped.values()):
        raise ProbeError(f"{declaration.get('probe')}: skipBackends maps a backend to its reason")
    chosen = [backend for backend in backends if backend.name not in skipped]
    if not chosen:
        raise ProbeError(f"{declaration.get('probe')}: every available backend is skipped")
    return chosen


def run_everywhere(declaration: dict, elf: bytes, backends: list[Backend]) -> dict[str, dict]:
    results = {}
    for backend in usable_backends(declaration, backends):
        observed = backend.run(declaration, elf)
        consistent_output(observed)
        normalize_stack(declaration, observed)
        results[backend.name] = observed
    return results


def cross_check(results: dict[str, dict], reference: dict, name: str,
                marks: list[dict] | None = None) -> list[str]:
    problems = []
    for backend, observed in results.items():
        problems += disagreements(reference, observed, f"{name}/{backend}", marks)
    return problems


def expected_of(observed: dict) -> dict:
    expected = {"syscalls": observed["syscalls"], "stdoutHex": observed["stdoutHex"],
                "stderrHex": observed["stderrHex"], "outcome": observed["outcome"]}
    if observed.get("files"):
        expected["files"] = observed["files"]
    return expected


def encoded(value: dict) -> str:
    return json.dumps(value, indent=2, sort_keys=False) + "\n"


# ---------------------------------------------------------------------------
# Lean generation


def camel(name: str) -> str:
    return "".join(part[:1].upper() + part[1:] for part in name.split("_"))


def lean_bytes(data: bytes, indent: str = "    ") -> str:
    if not data:
        return "[]"
    rows = []
    for start in range(0, len(data), 16):
        rows.append(indent + ", ".join(f"0x{byte:02x}" for byte in data[start:start + 16]))
    return "[\n" + ",\n".join(rows) + "]"


def lean_files(files: dict[str, str]) -> str:
    """A sorted `Fs.FileSystem` literal: (name bytes, contents) pairs."""
    def inline(data: bytes) -> str:
        return "[" + ", ".join(f"0x{byte:02x}" for byte in data) + "]"
    entries = sorted((name.encode(), bytes.fromhex(data)) for name, data in files.items())
    return "[" + ",\n    ".join(f"({inline(name)},\n      {inline(data)})" for name, data in entries) + "]"


def lean_int(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def lean_module(declaration: dict, elf: bytes) -> str:
    name = declaration["probe"]
    facts = elf_facts(elf, image_kind(declaration))
    header, program = facts["header"], facts["program"]
    expected = declaration["expected"]
    recorded = declaration["recorded"]
    def raw_call(call: dict) -> str:
        args = ", ".join("0" if arg == "sp" else str(arg) for arg in call["args"])
        ret = "none" if call["ret"] is None else f"some {lean_int(call['ret'])}"
        return f"⟨{call['nr']}, [{args}], {ret}⟩"
    syscalls = ",\n    ".join(raw_call(call) for call in expected["syscalls"])
    stack = [f"({index}, {position})" for index, call in enumerate(expected["syscalls"])
             for position, arg in enumerate(call["args"]) if arg == "sp"]
    stack_field = f"\n  stackArgs := [{', '.join(stack)}]" if stack else ""
    outcome = expected["outcome"]
    outcome_text = f".exited {outcome['exit']}" if "exit" in outcome else f".killed {outcome['signal']}"
    header_text = ", ".join(str(header[key]) for key in (
        "osABI", "abiVersion", "fileType", "machine", "version", "entry", "programOffset", "sectionOffset",
        "flags", "headerSize", "programEntrySize", "programCount", "sectionEntrySize", "sectionCount",
        "sectionNameIndex"))
    program_text = ", ".join(str(program[key]) for key in (
        "kind", "flags", "offset", "virtualAddress", "physicalAddress", "fileSize", "memorySize", "alignment"))
    mutant = declaration.get("mutantOf")
    role = f"Mutant of `{mutant}`." if mutant else "Positive probe."
    inputs = declaration.get("inputs", {})
    stdin = bytes.fromhex(inputs.get("stdinHex", ""))
    input_files = inputs.get("files", {})
    if stdin and input_files:
        raise ProbeError(f"{name}: a probe declares stdin or input files, not both (the kit has no combined harness input yet)")
    inputs_text = ""
    input_field = ""
    if stdin:
        inputs_text = f"""
/-- The declared stdin (`inputs.stdinHex`), the harness's stdin file. -/
def stdin : List Byte := {lean_bytes(stdin)}
"""
        input_field = "\n  input := harnessInputWith stdin"
    if input_files:
        for path in input_files:
            checked_relative(path)
        inputs_text = f"""
/-- The declared input files: the work directory the harness runs the probe in, and
the launch file system (`ProcInput.imageFs`) of the model. -/
def inputFiles : Fs.FileSystem := {lean_files(input_files)}
"""
        input_field = "\n  input := harnessInputFiles inputFiles"
    consumed = stdin_consumed(declaration, expected["syscalls"])
    consumed_text = f"\n  stdin := {lean_bytes(consumed)}" if consumed else ""
    final = files_of(expected)
    files_field = f"\n  files := {lean_files(final)}" if final else ""
    marks = host_dependent(declaration)
    varying = ""
    if marks:
        items = "\n".join(
            f"* call {mark['call']}, " + ("return" if mark.get("ret") is True else f"argument {mark['arg']}")
            + f": {mark['why']}" for mark in marks)
        varying = ("\nHost-dependent fields (recorded here, present but not compared in live runs):\n"
                   + items + "\n")
    return f"""module

public import Silmaril.Process.LPS.Probes.Kit

/-! # Probe data `{name}` (generated: do not edit)

Generated by `tools/verification-projects/lps_probes.py gen-lean` from
`{PROBES}/probes/{name}.json`. {role}
ELF sha256 `{sha256(elf)}` ({len(elf)} bytes, built from `{name}.s`).
Linux observation: backend `{recorded['backend']}`, kernel `{recorded['kernel']}`,
agreeing backends {', '.join('`' + item + '`' for item in recorded['agreeingBackends'])}.
`lps_probes.py --check` fails if these constants, the JSON, the pinned bytes or a live
run disagree.
{varying}-/

@[expose] public section

namespace {LEAN_NAMESPACE}.{camel(name)}

open Silmaril.Process.LPS.Probes

/-- The complete ELF file. -/
def fileBytes : List Byte := {lean_bytes(elf)}
{inputs_text}
def probe : Probe where
  fileBytes := fileBytes
  header := ⟨{header_text}⟩
  programHeader := ⟨{program_text}⟩{input_field}

/-- What Linux did: raw syscalls `⟨number, raw arguments, raw return⟩`, output bytes
and the outcome{", with the files left in the work directory" if final else ""}. -/
def observed : Observed where
  syscalls := [
    {syscalls}]{consumed_text}
  stdout := {lean_bytes(bytes.fromhex(expected['stdoutHex']))}
  stderr := {lean_bytes(bytes.fromhex(expected['stderrHex']))}
  outcome := {outcome_text}{files_field}{stack_field}

end {LEAN_NAMESPACE}.{camel(name)}
"""


def lean_path(root: Path, name: str) -> Path:
    return root / LEAN_DATA / f"{camel(name)}.lean"


LEAN_PROBES = "Silmaril/Process/LPS/Probes"
LEAN_PROBES_NAMESPACE = "Silmaril.Process.LPS.Probes"
# Proof modules may also be problem modules (`Silmaril/Process/LPS/Problems`, docs/Problems.md).
LEAN_PROOF_ROOTS = (LEAN_PROBES_NAMESPACE, "Silmaril.Process.LPS.Problems")


DECLARATION = re.compile(r"^(?:protected |private )?(?:theorem|instance|def|abbrev) ([A-Za-z_][\w.']*)")


def declared_names(text: str) -> set[str]:
    """Fully qualified theorem/instance/def names of a Lean file, following
    `namespace`/`end` nesting (enough for the probe modules, which use no sections
    with the same names as namespaces)."""
    stack: list[str] = []
    names = set()
    for line in text.splitlines():
        opened = re.match(r"^namespace ([\w.]+)\s*$", line)
        if opened:
            stack.append(opened.group(1))
            continue
        closed = re.match(r"^end ([\w.]+)\s*$", line)
        if closed and stack and stack[-1] == closed.group(1):
            stack.pop()
            continue
        declared = DECLARATION.match(line)
        if declared:
            names.add(".".join(stack + [declared.group(1)]))
    return names


def lean_link_problems(root: Path, declaration: dict) -> list[str]:
    """The proof module named by the JSON exists, imports the generated data module,
    quotes its `observed`/`probe` constants and states every listed theorem."""
    name = declaration["probe"]
    link = declaration.get("lean")
    if not isinstance(link, dict) or not link.get("module") or not link.get("theorems"):
        return [f"{name}: declare 'lean': {{'module': ..., 'theorems': [...]}} linking the proofs"]
    module = link["module"]
    if not any(module.startswith(root + ".") for root in LEAN_PROOF_ROOTS):
        return [f"{name}: lean module {module} is not under {' or '.join(LEAN_PROOF_ROOTS)}"]
    path = root / (module.replace(".", "/") + ".lean")
    if not path.exists():
        return [f"{name}: lean module {path.relative_to(root)} does not exist"]
    text = path.read_text()
    problems = []
    data_module = f"{LEAN_NAMESPACE}.{camel(name)}"
    if f"import {data_module}" not in text:
        problems.append(f"{name}: {path.relative_to(root)} does not import {data_module}")
    if f"open Data.{camel(name)}" not in text and f"Data.{camel(name)}." not in text:
        problems.append(f"{name}: {path.relative_to(root)} never refers to Data.{camel(name)}")
    declared = declared_names(text)
    for theorem in link["theorems"]:
        if theorem not in declared:
            problems.append(f"{name}: theorem {theorem} is not stated in {path.relative_to(root)}")
    if "sorry" in text or re.search(r"^\s*axiom\b", text, re.MULTILINE) or "native_decide" in text:
        problems.append(f"{name}: {path.relative_to(root)} uses sorry, axiom or native_decide")
    return problems


def mutant_problems(root: Path, declaration: dict) -> list[str]:
    """A mutant really behaves differently on Linux than its original."""
    name, original = declaration["probe"], declaration.get("mutantOf")
    if original is None:
        return []
    try:
        base = load_declaration(root, original)
    except (OSError, ValueError, ProbeError) as error:
        return [f"{name}: cannot load original {original}: {error}"]
    mine, theirs = declaration.get("expected", {}), base.get("expected", {})
    keys = ("outcome", "stdoutHex", "stderrHex")
    if all(mine.get(key) == theirs.get(key) for key in keys) and files_of(mine) == files_of(theirs):
        return [f"{name}: the mutant's recorded behaviour equals {original}'s (outcome, output and files)"]
    return []


# ---------------------------------------------------------------------------
# Commands


def built(root: Path, name: str, scratch: Path) -> bytes:
    declaration = load_declaration(root, name)
    static_check(declaration, (probe_dir(root) / f"{name}.s").read_text())
    elf = build(root, name, scratch / name, image_kind(declaration))
    elf_facts(elf, image_kind(declaration))
    return elf


def record(root: Path, name: str, backends: list[Backend]) -> dict:
    with tempfile.TemporaryDirectory(prefix="lps-probe-build-") as scratch:
        elf = built(root, name, Path(scratch))
    declaration = load_declaration(root, name)
    results = run_everywhere(declaration, elf, backends)
    lead = primary(usable_backends(declaration, backends))
    reference = expected_of(results[lead.name])
    problems = cross_check(results, reference, name, host_dependent(declaration))
    if problems:
        raise ProbeError("backends disagree:\n  " + "\n  ".join(problems))
    declaration["sha256"] = sha256(elf)
    declaration["expected"] = reference
    declaration["recorded"] = {"backend": lead.name, **environment(backends),
                               "agreeingBackends": sorted(results)}
    (probe_dir(root) / f"{name}.json").write_text(encoded(declaration))
    pins = read_pins(root)
    pins[name] = sha256(elf)
    write_pins(root, pins)
    target = lean_path(root, name)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(lean_module(declaration, elf))
    return declaration


def check(root: Path, names: list[str], backends: list[Backend] | None, live: bool = True) -> list[str]:
    """Every link: source -> bytes -> pin -> JSON -> Lean module -> live runs."""
    problems = []
    pins = read_pins(root)
    known = set(probe_names(root))
    if set(pins) != known:
        problems.append(f"{SHA_FILE} lists {sorted(pins)}, probes are {sorted(known)}")
    with tempfile.TemporaryDirectory(prefix="lps-probe-check-") as scratch:
        for name in names:
            try:
                declaration = load_declaration(root, name)
                elf = built(root, name, Path(scratch))
                digest = sha256(elf)
                if pins.get(name) != digest:
                    problems.append(f"{name}: rebuilt sha256 {digest} != {SHA_FILE} {pins.get(name)}")
                if declaration.get("sha256") != digest:
                    problems.append(f"{name}: rebuilt sha256 {digest} != JSON {declaration.get('sha256')}")
                mutant = declaration.get("mutantOf")
                if mutant is not None and mutant not in known:
                    problems.append(f"{name}: mutantOf {mutant!r} is not a probe")
                problems += mutant_problems(root, declaration)
                problems += lean_link_problems(root, declaration)
                path = lean_path(root, name)
                if not path.exists() or path.read_text() != lean_module(declaration, elf):
                    problems.append(f"{name}: {path.relative_to(root)} is stale; run gen-lean")
                if live and backends:
                    results = run_everywhere(declaration, elf, backends)
                    problems += cross_check(results, declaration["expected"], name,
                                            host_dependent(declaration))
            except (ProbeError, OSError, KeyError, ValueError, subprocess.TimeoutExpired) as error:
                problems.append(f"{name}: {error}")
    return problems


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--qemu", help="qemu-x86_64 binary (default: $LPS_PROBES_QEMU or PATH)")
    parser.add_argument("--backend", action="append", help="restrict to these backends (repeatable)")
    parser.add_argument("--check", action="store_true", help="check every link for all probes (default command)")
    sub = parser.add_subparsers(dest="command")
    sub.add_parser("backends", help="list backends and whether they are available here")
    for command in ("run", "record", "gen-lean"):
        item = sub.add_parser(command)
        item.add_argument("probes", nargs="*")
    item = sub.add_parser("build")
    item.add_argument("probe")
    item.add_argument("output", type=Path)
    item = sub.add_parser("check")
    item.add_argument("probes", nargs="*")
    item.add_argument("--offline", action="store_true", help="skip live runs (bytes, pins, JSON and Lean only)")
    args = parser.parse_args(argv)
    root = args.root
    try:
        if args.command == "backends":
            for backend in all_backends(args.qemu):
                ok, reason = backend.available()
                print(f"{backend.name:12} {'yes' if ok else 'no ':3}  {reason}  [{backend.isolation}]")
            return 0
        if args.command == "build":
            with tempfile.TemporaryDirectory(prefix="lps-probe-build-") as scratch:
                elf = built(root, args.probe, Path(scratch))
            args.output.write_bytes(elf)
            print(f"{args.probe}: {sha256(elf)}")
            return 0
        names = getattr(args, "probes", None) or probe_names(root)
        if args.command == "run":
            backends = select_backends(args.backend, args.qemu)
            for name in names:
                with tempfile.TemporaryDirectory(prefix="lps-probe-build-") as scratch:
                    elf = built(root, name, Path(scratch))
                print(json.dumps({name: run_everywhere(load_declaration(root, name), elf, backends)}, indent=2))
            return 0
        if args.command == "record":
            backends = select_backends(args.backend, args.qemu)
            for name in names:
                declaration = record(root, name, backends)
                print(f"{name}: recorded {declaration['expected']['outcome']} via {declaration['recorded']['backend']}, "
                      f"agreeing {declaration['recorded']['agreeingBackends']}")
            return 0
        if args.command == "gen-lean":
            with tempfile.TemporaryDirectory(prefix="lps-probe-build-") as scratch:
                for name in names:
                    declaration = load_declaration(root, name)
                    elf = built(root, name, Path(scratch))
                    target = lean_path(root, name)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_text(lean_module(declaration, elf))
            return 0
        offline = getattr(args, "offline", False)
        backends = None if offline else select_backends(args.backend, args.qemu)
        problems = check(root, names, backends, live=not offline)
        if problems:
            print("lps probes: FAILED\n  " + "\n  ".join(problems), file=sys.stderr)
            return 1
        used = "offline" if offline else ", ".join(backend.name for backend in backends)
        print(f"lps probes: {len(names)} probes agree (sources, sha256, JSON, Lean; backends: {used})")
        return 0
    except (ProbeError, OSError, KeyError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"lps probes: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
