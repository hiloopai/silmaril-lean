"""Independent GNU/LLVM tool checks and native smoke tests for the built matrix."""
import ctypes as c
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

from build import BASELINE, BUILDS, DEFINES, SOURCE, require, run

TINY = ("sqlite3_libversion_number", "sqlite3_threadsafe", "sqlite3_str_length")
SYMBOL = re.compile(r"^\s*(\d+):\s+(\w+)\s+(\w+)\s+(\w+)\s+(\w+)\s+(\w+)\s+(\S+)(?:\s+(\S+))?")
INSN = re.compile(r"^\s*([0-9a-f]+):\s*((?:[0-9a-f]{2}(?:\s+|$))+)\s*(.*)$")
RELOCATION = re.compile(r"^([0-9a-f]+)\s+[0-9a-f]+\s+R_X86_64_", re.M)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def read_symbols(path, option):
    records = []
    for line in run(["readelf", "-W", option, str(path)]).splitlines():
        row = SYMBOL.match(line)
        if row is None:
            continue
        index, address, size, kind, bind, visibility, section, name = row.groups()
        if int(index) != 0:
            records.append((int(address, 16), int(size, 16 if size.startswith("0x") else 10),
                            kind, bind, visibility, section, name))
    return records


def disassembly(path, sample, tool):
    start = sample["address"]
    end = start + sample["size_bytes"]
    if tool == "objdump":
        flags = ["-M", "intel", "--insn-width=16"]
    else:
        flags = ["--x86-asm-syntax=intel"]
    command = [tool, "-d", "-z", *flags, f"--start-address={start}", f"--stop-address={end}", str(path)]
    instructions = {}
    cursor = start
    for line in run(command).splitlines():
        match = INSN.match(line)
        if match is None:
            continue
        address, raw, asm = match.groups()
        address = int(address, 16)
        if start <= address < end:
            data = bytes.fromhex(raw)
            require(address == cursor, f"{path.name} {tool}: gap at {cursor:#x}")
            instructions[address] = (data, asm)
            cursor += len(data)
    require(cursor == end, f"{path.name} {tool}: truncated slice {start:#x}..{end:#x}")
    data = b"".join(raw for raw, _ in instructions.values())
    require(sha256(data) == sample["exact_sha256"], f"{path.name} {tool}: slice hash mismatch")
    require(len(instructions) == sample["counts"]["instructions"],
            f"{path.name} {tool}: instruction count mismatch at {start:#x}")
    return instructions


def check_sample(path, record, symbols, relocations, rodata):
    name, sample = record
    start = sample["address"]
    end = start + sample["size_bytes"]
    require(any(a == start and size == end - start and kind == "FUNC" and symbol == name
                for a, size, kind, _, _, _, symbol in symbols), f"readelf symbol extent for {name}")
    instructions = disassembly(path, sample, "objdump")
    direct_calls = indirect_calls = indirect_jumps = 0
    for _, asm in instructions.values():
        transfer = re.match(r"^(?:notrack\s+)?(call|jmp)\s+(\S+)", asm)
        if transfer:
            mnemonic, operand = transfer.groups()
            direct = re.fullmatch(r"(?:0x)?[0-9a-f]+", operand)
            direct_calls += int(mnemonic == "call" and bool(direct))
            indirect_calls += int(mnemonic == "call" and not direct)
            indirect_jumps += int(mnemonic == "jmp" and not direct)
    counts = sample["counts"]
    locked = sum(asm.startswith("lock ") for _, asm in instructions.values())
    require(locked == counts["lock_prefix_sites"], f"objdump LOCK count for {name}")
    fences = sum(asm == "mfence" for _, asm in instructions.values())
    require(fences == counts["mfence_sites"], f"objdump MFENCE count for {name}")
    require((direct_calls, indirect_calls, indirect_jumps) ==
            (counts["direct_call_sites"], counts["indirect_call_sites"], counts["indirect_jump_sites"]),
            f"objdump transfer counts for {name}: {(direct_calls, indirect_calls, indirect_jumps)}")
    require(sum(start <= address < end for address in relocations) ==
            counts["executable_relocations_in_decoded_spans"], f"readelf relocation count for {name}")
    if sample["short_slice_hex"] is not None:
        data = b"".join(raw for raw, _ in instructions.values())
        require(data.hex() == sample["short_slice_hex"], f"objdump short slice for {name}")
    for transfer in sample["transfer_examples"]:
        destination = transfer["destination"]
        if destination is not None and destination.startswith("plt:"):
            symbol = destination.removeprefix("plt:").split("@")[0]
            require(f"<{symbol}@plt>" in instructions[transfer["address"]][1],
                    f"objdump PLT destination for {name}: {symbol}")
    for table in sample["table_examples"]:
        jump = table["jump_address"]
        require(re.match(r"^jmp\s+r[\da-z]+$", instructions[jump][1]), f"objdump table jump for {name}")
        address, position, size = rodata
        base = table["table_address"]
        require(address <= base <= address + size - 8, f"readelf .rodata table extent for {name}")
        with path.open("rb") as artifact:
            artifact.seek(position + base - address)
            data = artifact.read(8)
        decoded = [base + int.from_bytes(data[i:i + 4], "little", signed=True) for i in (0, 4)]
        require(decoded == table["first_two_destinations"] and all(a in instructions for a in decoded),
                f"table entries for {name}")
    if name in TINY:
        disassembly(path, sample, "llvm-objdump")
    return len(sample["table_examples"])


def runtime_check(path):
    dll = c.CDLL(str(Path(path).resolve()), mode=os.RTLD_NOW | c.RTLD_LOCAL)

    def bind(name, result, *parameters):
        function = getattr(dll, name)
        function.restype = result
        function.argtypes = parameters
        return function

    version = bind("sqlite3_libversion", c.c_char_p)().decode()
    number = bind("sqlite3_libversion_number", c.c_int)()
    source_id = bind("sqlite3_sourceid", c.c_char_p)().decode()
    threadsafe = bind("sqlite3_threadsafe", c.c_int)()
    require(not hasattr(dll, "sqlite3_load_extension") and not hasattr(dll, "sqlite3_enable_load_extension"),
            "extension-loading API is present")
    callback_type = c.CFUNCTYPE(c.c_int, c.c_void_p, c.c_int, c.POINTER(c.c_char_p), c.POINTER(c.c_char_p))
    sqlite_open = bind("sqlite3_open", c.c_int, c.c_char_p, c.POINTER(c.c_void_p))
    sqlite_close = bind("sqlite3_close", c.c_int, c.c_void_p)
    sqlite_exec = bind("sqlite3_exec", c.c_int, c.c_void_p, c.c_char_p, callback_type,
                       c.c_void_p, c.c_void_p)
    sqlite_errmsg = bind("sqlite3_errmsg", c.c_char_p, c.c_void_p)
    db = c.c_void_p()

    def sql(statement):
        rows = []

        @callback_type
        def collect(_, count, values, _columns):
            rows.append([values[i].decode() if values[i] is not None else None for i in range(count)])
            return 0

        result = sqlite_exec(db, statement.encode(), collect, None, None)
        require(result == 0, f"{statement}: {sqlite_errmsg(db).decode()}")
        return rows

    with tempfile.TemporaryDirectory() as scratch:
        try:
            require(sqlite_open(os.fsencode(Path(scratch) / "smoke.db"), c.byref(db)) == 0, "sqlite3_open")
            options = sorted(row[0] for row in sql("PRAGMA compile_options"))
            before = sql("PRAGMA mmap_size")
            after = sql("PRAGMA mmap_size=1048576")
            rows = sql("CREATE TABLE items(v); INSERT INTO items VALUES (1),(2),(3);"
                       " SELECT sum(v), count(*) FROM items WHERE v >= 2;")
        finally:
            require(sqlite_close(db) == 0, "sqlite3_close")
    require(version == SOURCE["version"] and number == 3054001 and threadsafe == 1, "SQLite version/thread mode")
    require("OMIT_LOAD_EXTENSION" in options and "THREADSAFE=1" in options
            and "MAX_MMAP_SIZE=0" in options, "runtime compile options")
    require(before == after == [["0"]] and rows == [["5", "2"]], "mmap or SQL smoke result")
    return {
        "version": version, "version_number": number, "source_id": source_id,
        "threadsafe": threadsafe, "compile_options": options, "mmap_before": 0,
        "mmap_after_request": 0, "query_rows": rows, "extension_apis_absent": True,
    }


def verify_artifacts(work, metadata):
    require(set(metadata["builds"]) == set(BUILDS), "manifest build IDs")
    for name in ("sqlite3.c", "sqlite3.h"):
        require(sha256((work / "source" / name).read_bytes()) == SOURCE[name], f"source {name}")
    for build in BUILDS:
        directory = work / build
        files = metadata["builds"][build]["files"]
        require(set(files) == {"sqlite3.o", "libsqlite3.so", "relocs.so", "stripped.so", "macros.txt"},
                f"{build}: manifest file list")
        for filename, record in files.items():
            data = (directory / filename).read_bytes()
            require(len(data) == record["size_bytes"] and sha256(data) == record["sha256"],
                    f"{build}: {filename} manifest mismatch")
        macros = (directory / "macros.txt").read_text().splitlines()
        for key, value in DEFINES.items():
            require(f"#define {key} {value}" in macros, f"{build}: {key}")


def check_tools(directory, result, source_id):
    ordinary = directory / "libsqlite3.so"
    reloc_link = directory / "relocs.so"
    stripped = directory / "stripped.so"
    static = read_symbols(reloc_link, "--syms")
    dynamic = read_symbols(reloc_link, "--dyn-syms")
    # --syms prints both tables with .dynsym first.
    require(static[:len(dynamic)] == dynamic, f"{directory.name}: readelf symbol table ordering")
    static = static[len(dynamic):]
    functions = [(a, size) for a, size, kind, _, _, section, _ in static if kind == "FUNC" and section != "UND"]
    inventory = result["inventory"]
    require(len(functions) == inventory["defined_function_records"]
            and sum(size == 0 for _, size in functions) == inventory["zero_size_records"],
            f"{directory.name}: readelf STT_FUNC counts")
    exports = {name for _, _, kind, bind, _, section, name in dynamic
               if kind == "FUNC" and bind != "LOCAL" and section != "UND"}
    require(len(exports) == result["dynamic_export_names"], f"{directory.name}: readelf exports")
    stripped_dyn = read_symbols(stripped, "--dyn-syms")
    require(read_symbols(stripped, "--syms") == stripped_dyn, f"{directory.name}: readelf stripped static symbol table")
    require(len(dynamic) == len(stripped_dyn) == result["stripped_pair"]["dynamic_symbol_records"],
            f"{directory.name}: readelf dynamic symbol count")
    require(not any(section.startswith("BAD") for *_, section, _ in stripped_dyn),
            f"{directory.name}: readelf stripped dynamic section indices")

    soname = []
    needed = []
    for path in (ordinary, stripped, reloc_link):
        text = run(["readelf", "-W", "-d", str(path)])
        soname.append(re.findall(r"\(SONAME\).*\[([^\]]+)\]", text))
        needed.append(re.findall(r"\(NEEDED\).*\[([^\]]+)\]", text))
    require(all(name == ["libsqlite3.so.0"] for name in soname), f"{directory.name}: SONAME")
    require(needed[0] == needed[1] == needed[2] and "libc.so.6" in needed[0],
            f"{directory.name}: loader dependencies")
    for path, key in ((ordinary, "build_id"), (stripped, "build_id"), (reloc_link, "relocation_link_build_id")):
        notes = run(["readelf", "-W", "-n", str(path)])
        require(re.findall(r"Build ID: (\w+)", notes) == [result["stripped_pair"][key]], f"{path}: build ID")

    sections = run(["readelf", "-W", "-S", str(reloc_link)])
    rodata = tuple(int(value, 16) for value in
                   re.search(r"\.rodata\s+PROGBITS\s+(\w+)\s+(\w+)\s+(\w+)", sections).groups())
    relocs_text = run(["readelf", "-W", "-r", str(reloc_link)])
    text_block = re.search(r"Relocation section '\.rela\.text'[^\n]*\n(.*?)(?:\n\n|\Z)", relocs_text, re.S)[1]
    relocations = [int(address, 16) for address in RELOCATION.findall(text_block)]
    samples = {name: sample for name, sample in result["samples"].items() if sample is not None}
    require(all(name in samples for name in TINY), f"{directory.name}: missing tiny symbol")
    tables = sum(check_sample(reloc_link, record, static, relocations, rodata) for record in samples.items())
    check_dwarf = directory.name in (BASELINE, "clang-O2")
    if check_dwarf:
        dwarf_text = run(["readelf", "--debug-dump=info", str(ordinary)])
        require(dwarf_text.count("(DW_TAG_inlined_subroutine)") == result["inline_hints"]["inline_dies"],
                f"{directory.name}: DWARF inline count")

    # Launch each dlopen in an isolated process, so a prior build cannot supply symbols.
    checks = [json.loads(run([sys.executable, str(Path(__file__).resolve()), str(path)]))
              for path in (ordinary, stripped)]
    require(checks[0] == checks[1] and checks[0]["source_id"] == source_id,
            f"{directory.name}: runtime summary or source ID mismatch")
    return {
        "soname": soname[0][0], "needed": needed[0], "gnu_objdump_slices_checked": len(samples),
        "llvm_objdump_slices_checked": len(TINY), "relative_table_examples_checked": tables,
        "readelf_dwarf_inline_count_checked": check_dwarf, "runtime_artifacts_checked": len(checks),
        "runtime": checks[0],
    }


def verify_matrix(work, metadata, analysis):
    results = {}
    for build in BUILDS:
        try:
            results[build] = check_tools(work / build, analysis["builds"][build],
                                         metadata["source"]["sqlite_source_id"])
        except ValueError as error:
            raise ValueError(f"{build}: {error}") from error
    build_options = [
        {option for option in result["runtime"]["compile_options"] if not option.startswith("COMPILER=")}
        for result in results.values()
    ]
    require(all(options == build_options[0] for options in build_options), "SQLite compile options differ")
    return results


if __name__ == "__main__":
    print(json.dumps(runtime_check(sys.argv[1]), sort_keys=True))
