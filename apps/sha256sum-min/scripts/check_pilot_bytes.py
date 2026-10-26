# Checks that ELF's linked sha256_compress is the pilot image: the 459 clang
# -O2 bytes of tests/x86/sha256_compress_clang_O2.hex with disp32 at +0xb7 =
# K - (f + 0xbb), and that the 256 bytes at sha256_compress_K are the pilot's
# K table. Usage: python3 -I check_pilot_bytes.py ELF HEX  (prints JSON)
import hashlib, json, struct, subprocess, sys
elf, hexpath = sys.argv[1], sys.argv[2]
raw = bytes.fromhex(''.join(open(hexpath).read().split()))
data = open(elf, 'rb').read()
assert data[:4] == b'\x7fELF' and data[4] == 2
phoff, = struct.unpack_from('<Q', data, 0x20); phentsize, phnum = struct.unpack_from('<HH', data, 0x36)
loads = []
for i in range(phnum):
    p_type, p_flags, p_offset, p_vaddr, _, p_filesz, _, _ = struct.unpack_from('<IIQQQQQQ', data, phoff + i * phentsize)
    if p_type == 1: loads.append((p_vaddr, p_offset, p_filesz, p_flags))
def read(va, n):
    for v, o, sz, _ in loads:
        if v <= va and va + n <= v + sz: return data[o + va - v: o + va - v + n]
    raise KeyError(hex(va))
syms = {}
for line in subprocess.run(['nm', '-S', elf], capture_output=True, text=True, check=True).stdout.splitlines():
    f = line.split()
    if len(f) == 4: syms[f[3]] = (int(f[0], 16), int(f[1], 16))
f, fsz = syms['sha256_compress']; k, ksz = syms['sha256_compress_K']
assert fsz == 459 and ksz == 256
got = read(f, 459)
disp = struct.unpack_from('<i', got, 0xb7)[0]
ok_disp = (f + 0xbb + disp) == k
ok_rest = got[:0xb7] == raw[:0xb7] and got[0xbb:] == raw[0xbb:]
kb = read(k, 256)
ok_k = hashlib.sha256(kb).hexdigest() == '74ef7306e7452d6859b6463ce496b8df30925f69e1b2969e1f3f34bbc9c6af04'
print(json.dumps({'textBase': hex(f), 'rodataBase': hex(k), 'disp32': disp,
                  'bytes_match_except_disp': ok_rest, 'disp_reaches_K': ok_disp, 'K_matches': ok_k,
                  'linked_function_sha256': hashlib.sha256(got).hexdigest()}, indent=1))
sys.exit(0 if ok_rest and ok_disp and ok_k else 1)
