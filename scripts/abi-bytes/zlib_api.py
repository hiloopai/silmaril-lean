#!/usr/bin/env python3
"""Emit the code regions of zlib's remaining API functions in Ubuntu's libz.so.1.3 as a Lean module.

For each function, starting at its `.dynsym` value: a linear sweep of GNU objdump's listing that
follows every direct branch and call target, and stops a path at `ret`, `ud2` or an unconditional
`jmp`. The region is the smallest contiguous byte range holding every instruction reached; the
script FAILS on an indirect branch or call, or a call or jump to the PLT, since a region cannot
contain code it does not see. `%rip`-relative operands are reported, and the read-only data
segment is carried as `Code.data` for the functions that read it.

The bytes are untrusted data: `Silmaril.Elf.Abi.ZlibMatrix.Api.Thms` checks every literal against the
file's kernel bytes (`CodeAt`, `MappedAt`). That the sweep found all reachable code is not
checked by Lean; a missing callee makes the row's open task false, never a theorem.

usage: python3 -I scripts/abi-bytes/zlib_api.py [--check]   (needs objdump on PATH)
"""
import hashlib, pathlib, re, struct, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
ELF = "examples/elf/pinned/zlib-libz.so.1.3"
SHA256 = "f61677c7bdb7c2aa2a243ea781bfd16afcb361cede7b4ef76127a9d8eb9a5242"
OUT = "Silmaril/Machine/Abi/Conformance/ZlibApi/Bytes.lean"
NS = "Silmaril.Machine.Abi.Conformance.ZlibApi"
# Lean name, symbol, expected (st_value, st_size, version name or None for the base version).
FUNCS = [("crc32Combine", "crc32_combine", 0x99f0, 9, "ZLIB_1.2.2"),
         ("adler32Combine", "adler32_combine", 0x7270, 224, "ZLIB_1.2.2"),
         ("crc32CombineGen", "crc32_combine_gen", 0x9a90, 9, "ZLIB_1.2.12"),
         ("crc32CombineOp", "crc32_combine_op", 0x9aa0, 54, "ZLIB_1.2.12"),
         ("getCrcTable", "get_crc_table", 0x7430, 12, None),
         ("zlibVersion", "zlibVersion", 0x11110, 12, None),
         ("zlibCompileFlags", "zlibCompileFlags", 0x11120, 10, "ZLIB_1.2.0.2")]


def elf_hash(name):
    h = 0
    for c in name.encode():
        h = (h << 4) + c
        g = h & 0xF0000000
        if g:
            h ^= g >> 24
        h &= ~g & 0xFFFFFFFF
    return h


def parse(data):
    (_, _, _, _, phoff, shoff, _, _, phentsize, phnum, shentsize, shnum, _) = struct.unpack_from(
        "<HHIQQQIHHHHHH", data, 16)
    phdrs = [struct.unpack_from("<IIQQQQQQ", data, phoff + i * phentsize) for i in range(phnum)]
    shdrs = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * shentsize) for i in range(shnum)]
    verdefs, versym, syms = {}, None, {}
    for sh in shdrs:
        if sh[1] == 0x6fffffff:
            versym = sh
        if sh[1] == 0x6ffffffd:  # SHT_GNU_verdef
            strtab = shdrs[sh[6]]
            off = sh[4]
            while True:
                _, _, ndx, cnt, _, aux, nxt = struct.unpack_from("<HHHHIII", data, off)
                nm = struct.unpack_from("<I", data, off + aux)[0]
                s = strtab[4] + nm
                verdefs[ndx] = data[s:data.index(b"\0", s)].decode()
                if not nxt:
                    break
                off += nxt
    for sh in shdrs:
        if sh[1] != 11:
            continue
        strtab = shdrs[sh[6]]
        for k in range(sh[5] // sh[9]):
            name, info, _, shndx, value, size = struct.unpack_from("<IBBHQQ", data, sh[4] + k * sh[9])
            s = strtab[4] + name
            nm = data[s:data.index(b"\0", s)].decode()
            v = struct.unpack_from("<H", data, versym[4] + 2 * k)[0] & 0x7fff
            if shndx != 0 and info & 0xf == 2:
                syms.setdefault(nm, []).append((value, size, verdefs.get(v) if v > 1 else None, k))
    return phdrs, syms


def listing(path):
    out = subprocess.run(["objdump", "-d", "-w", "-z", "--no-show-raw-insn", str(path)],
                         check=True, capture_output=True, text=True).stdout
    insns, plt = {}, set()
    section = None
    for line in out.splitlines():
        m = re.match(r"Disassembly of section (\S+):", line)
        if m:
            section = m.group(1)
            continue
        m = re.match(r"\s+([0-9a-f]+):\s+(.*)$", line)
        if not m:
            continue
        addr, text = int(m.group(1), 16), m.group(2).strip()
        if section in (".plt", ".plt.got", ".plt.sec"):
            plt.add(addr)
        elif section == ".text":
            insns[addr] = text
    addrs = sorted(insns)
    nxt = {a: b for a, b in zip(addrs, addrs[1:])}
    return insns, nxt, plt


def sweep(entry, insns, nxt, plt, name):
    seen, todo, riprel = set(), [entry], set()
    while todo:
        a = todo.pop()
        while a is not None and a not in seen:
            if a not in insns:
                sys.exit(f"{name}: no instruction at {a:#x}")
            seen.add(a)
            t = insns[a]
            op = t.split()[0] if t else ""
            if "(%rip)" in t:
                m2 = re.search(r"#\s+([0-9a-f]+)", t)
                riprel.add(int(m2.group(1), 16) if m2 else None)
            if re.match(r"(notrack\s+)?(jmp|call)q?\s+\*", t) or re.match(r"(jmp|call)\s+\*", t):
                sys.exit(f"{name}: indirect branch at {a:#x}: {t}")
            m = re.match(r"(j\w+|call)\s+([0-9a-f]+)\b", t)
            if m:
                tgt = int(m.group(2), 16)
                if tgt in plt or "@plt" in t:
                    sys.exit(f"{name}: branch to the PLT at {a:#x}: {t}")
                todo.append(tgt)
                if m.group(1) == "jmp":
                    break
            if op in ("ret", "ud2", "hlt") or t.startswith("ret"):
                break
            a = nxt.get(a)
    return seen, riprel


def read(data, phdrs, vaddr, n, flags):
    for kind, fl, off, va, _, filesz, _, _ in phdrs:
        if kind == 1 and fl == flags and va <= vaddr and vaddr + n <= va + filesz:
            return data[off + vaddr - va:off + vaddr - va + n]
    sys.exit(f"no PT_LOAD with flags {flags} maps [{vaddr:#x}, {vaddr + n:#x})")


def lean_bytes(name, doc, bs):
    out = [f"/-- {doc} -/", f"def {name} : List (BitVec 8) := ["]
    rows = [bs[i:i + 16] for i in range(0, len(bs), 16)]
    for k, row in enumerate(rows):
        out.append("  " + ", ".join(f"0x{b:02x}" for b in row) + ("," if k + 1 < len(rows) else ""))
    return out + ["]", ""]


def main(argv):
    check = "--check" in argv
    path = ROOT / ELF
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != SHA256:
        sys.exit(f"{ELF}: SHA-256 differs from the pin")
    phdrs, syms = parse(data)
    insns, nxt, plt = listing(path)
    ro = [p for p in phdrs if p[0] == 1 and p[1] == 4 and p[3] != 0]
    rova, rosz = ro[0][3], ro[0][5]
    body = ["module", "", f"/-! # zlib 1.3 `libz.so.1.3` (Ubuntu): the regions of the remaining API functions", "",
            f"GENERATED by `scripts/abi-bytes/zlib_api.py` from `{ELF}`", f"(SHA-256 `{SHA256}`); do not edit.", "",
            "Untrusted data, checked against the file by `Silmaril.Elf.Abi.ZlibMatrix.Api.Thms`. Each region is the",
            "smallest byte range holding every instruction a sweep from the entry reaches (direct branch and",
            "call targets followed; indirect branches and PLT calls refused by the generator). -/", "",
            "set_option maxRecDepth 100000", "", "@[expose] public section", "", f"namespace {NS}", ""]
    report = []
    for lean, sym, value, size, ver in FUNCS:
        got = syms.get(sym)
        if not got or (got[0][0], got[0][1], got[0][2]) != (value, size, ver):
            sys.exit(f"{sym}: .dynsym is {got}, expected {(value, size, ver)}")
        idx = got[0][3]
        seen, riprel = sweep(value, insns, nxt, plt, sym)
        lo, hi = min(seen), max(seen)
        last = nxt.get(hi, hi + 16)
        hi_end = last if last - hi <= 15 else hi + 15
        # the end of the last instruction: the next instruction's address
        bs = read(data, phdrs, lo, hi_end - lo, 5)
        reads_ro = bool(riprel)
        if any(x is None or not (rova <= x < rova + rosz) for x in riprel):
            sys.exit(f"{sym}: a %rip-relative operand outside the read-only data segment: {riprel}")
        body += lean_bytes(f"{lean}Region", f"`{sym}`: entry `{value:#x}` (`.dynsym` {idx}, {size} B, "
                           f"{'version ' + ver if ver else 'base version'}); region `[{lo:#x}, {hi_end:#x})`, "
                           f"entry offset `{value - lo:#x}`; {len(seen)} instructions reached"
                           f"{'; reads %rip-relative data' if reads_ro else ''}.", bs)
        report.append((lean, sym, idx, lo, hi_end - lo, value - lo, size, ver, elf_hash(ver) if ver else None, reads_ro))
    # The read-only data segment is ZlibLibz.rodata (Silmaril.Machine.Abi.Conformance.ZlibLibz);
    # every %rip-relative operand was checked to point inside it.
    body += [f"/-- The regions as (name, symbol, `.dynsym` index, base, length, entry offset, extent,",
             "version name, version ELF hash, reads read-only data): the generator's report. -/",
             "def regions : List (String × String × Nat × Nat × Nat × Nat × Nat × Option String × Option Nat × Bool) := ["]
    body += [",\n".join(f'  ("{l}", "{s}", {i}, {lo:#x}, {n}, {o:#x}, {sz}, {("some " + chr(34) + v + chr(34)) if v else "none"}, '
                        f'{("some " + str(h)) if h is not None else "none"}, {"true" if r else "false"})'
                        for l, s, i, lo, n, o, sz, v, h, r in report), "]", "",
             f"end {NS}", "", "end", ""]
    text = "\n".join(body)
    out = ROOT / OUT
    if check:
        if not out.exists() or out.read_text() != text:
            sys.exit(f"{OUT}: out of date")
        print(f"{OUT}: up to date")
        return
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(text)
    for r in report:
        print(r)


if __name__ == "__main__":
    main(sys.argv[1:])
