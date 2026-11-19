#!/usr/bin/env python3
"""Execute exact existing ELF excerpts natively; no SUT rebuild or semantic proof.

PIE executables cannot be dlopen'd. Only these position-independent, call-free
function bytes are copied to an anonymous RX mapping. This is an excerpt test,
not a whole-ELF loader test. Model-side tests check ABI and caller-memory effects.
"""
import ctypes as C
import importlib.util
import json
import mmap
import platform
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('binary_view', ROOT/'tools/compiler-explorer/equivalence.py')
e = importlib.util.module_from_spec(spec)
spec.loader.exec_module(e)


def main():
    assert platform.machine() == 'x86_64', 'native x86-64 validation required'
    manifest = json.loads((ROOT/'corpus/darkhttpd/equivalence/logencoding/manifest.json').read_text())
    functions, mappings, records = [], [], []
    libc = C.CDLL(None, use_errno=True)
    libc.mprotect.argtypes = [C.c_void_p, C.c_size_t, C.c_int]
    for endpoint in manifest['endpoints']:
        e.validate_darkhttpd_build(ROOT, endpoint)
        raw = (ROOT/endpoint['path']).read_bytes()
        assert e.c.sha(raw) == endpoint['sha256']
        actual = e.c.elf_function(raw, 'needs_logencoding')
        assert actual == endpoint['functions']['needs_logencoding']
        code = bytes.fromhex(actual['bytes_hex'])
        memory = mmap.mmap(-1, mmap.PAGESIZE, prot=mmap.PROT_READ | mmap.PROT_WRITE)
        memory.write(code)
        address = C.addressof(C.c_char.from_buffer(memory))
        assert libc.mprotect(address, mmap.PAGESIZE, mmap.PROT_READ | mmap.PROT_EXEC) == 0
        assert C.string_at(address, len(code)) == code
        # The extra parameters deliberately set arbitrary RSI/RDX caller bits;
        # actual C signature observes only DIL, and returns signed int in EAX.
        functions.append(C.CFUNCTYPE(C.c_uint32, C.c_uint64, C.c_uint64, C.c_uint64)(address))
        mappings.append(memory)
        records.append(dict(path=endpoint['path'], sha256=endpoint['sha256'], **actual))
    patterns = [0, 1, 0x123456789abcde, 0xffffffffffffff]
    for salt in patterns:
        for byte in range(256):
            rdi = salt*256 + byte
            rdx = (salt*17 + 0xfedcba9876543210) % 2**64
            assert functions[0](rdi, salt, rdx) == functions[1](rdi, salt, rdx), (byte, salt)
    print(json.dumps(dict(artifacts=records, pairs=1024, byte_inputs=256,
        upper_register_patterns=patterns, actual_native_eax_equality=True,
        scope='Exact ELF excerpts in anonymous RX mappings; no SUT rebuild, whole-ELF load, general ABI/memory or semantic proof. Finite native observations; contextual obligation UNPROVED.'), indent=2))


if __name__ == '__main__':
    main()
