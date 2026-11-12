# Generate the escape ranges of Silmaril/Wasm/Tools/RustDebug/Defs.lean (Rust str Debug):
# python3 -I tools/wasm-tools/tests/gen-rust-ranges.py > ranges.txt (uses Python unicodedata).
import unicodedata, sys
OGE = [(0x09BE,0x09BE),(0x09D7,0x09D7),(0x0B3E,0x0B3E),(0x0B57,0x0B57),(0x0BBE,0x0BBE),(0x0BD7,0x0BD7),
 (0x0CC2,0x0CC2),(0x0CD5,0x0CD6),(0x0D3E,0x0D3E),(0x0D57,0x0D57),(0x0DCF,0x0DCF),(0x0DDF,0x0DDF),
 (0x1B35,0x1B35),(0x200C,0x200C),(0x302E,0x302F),(0xFF9E,0xFF9F),(0x1133E,0x1133E),(0x11357,0x11357),
 (0x114B0,0x114B0),(0x114BD,0x114BD),(0x115AF,0x115AF),(0x11930,0x11930),(0x1D165,0x1D165),
 (0x1D16E,0x1D172),(0xE0020,0xE007F),(0x1F3FB,0x1F3FF),
 # Default_Ignorable_Code_Point letters, escaped by Rust's is_printable
 (0x115F,0x1160),(0x3164,0x3164),(0xFFA0,0xFFA0)]
def esc(c):
    if c == 0x20: return False
    cat = unicodedata.category(chr(c))
    if cat in ("Cc","Cf","Cs","Co","Cn","Zl","Zp","Zs","Mn","Me"): return True
    return any(lo <= c <= hi for lo,hi in OGE)
rs=[]; start=None
for c in range(0x110000):
    e=esc(c)
    if e and start is None: start=c
    if not e and start is not None: rs.append((start,c-1)); start=None
if start is not None: rs.append((start,0x10FFFF))
print(len(rs), file=sys.stderr)
out=[]
for i in range(0,len(rs),6):
    out.append("  " + ", ".join(f"(0x{a:X}, 0x{b:X})" for a,b in rs[i:i+6]))
print(",\n".join(out))
