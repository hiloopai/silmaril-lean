module

public meta import Silmaril.Wasm.Wat.Float

/-! Exact bit regressions for the shared WAT literal decoder. These exercise
rounding boundaries that host binary64 followed by binary32 conversion can lose,
as well as subnormals, payload preservation and malformed input. -/

open Silmaril.Wasm.Wat

#guard (floatBits 32 "0").toOption == some 0
#guard (floatBits 32 "-0.0").toOption == some 0x80000000
#guard (floatBits 64 "-0x0p999999999999999999999").toOption == some 0x8000000000000000
#guard (floatBits 32 "1.e2").toOption == some 0x42c80000
#guard (floatBits 32 "0x1.p4").toOption == some 0x41800000
#guard (floatBits 32 "0.1").toOption == some 0x3dcccccd
#guard (floatBits 64 "0.1").toOption == some 0x3fb999999999999a
#guard (floatBits 32 "1_2.5_0e+0").toOption == some 0x41480000
#guard (floatBits 32 "0x1.A_Bp+1").toOption == some 0x40558000

-- Ties to even, including opposite parity and direct binary32 rounding.
#guard (floatBits 32 "16777217").toOption == some 0x4b800000
#guard (floatBits 32 "16777219").toOption == some 0x4b800002
#guard (floatBits 64 "9007199254740993").toOption == some 0x4340000000000000
#guard (floatBits 32 "1.000000059604644775390625").toOption == some 0x3f800000
#guard (floatBits 32 "1.000000059604644775390626").toOption == some 0x3f800001
#guard (floatBits 32 "1.000000178813934326171875").toOption == some 0x3f800002

-- Gradual underflow, the halfway point at zero and the normal/subnormal boundary.
#guard (floatBits 32 "0x1p-149").toOption == some 1
#guard (floatBits 32 "0x1p-150").toOption == some 0
#guard (floatBits 32 "0x1.000002p-150").toOption == some 1
#guard (floatBits 32 "-0x1p-150").toOption == some 0x80000000
#guard (floatBits 32 "0x0.fffffep-126").toOption == some 0x007fffff
#guard (floatBits 32 "0x1p-126").toOption == some 0x00800000
#guard (floatBits 64 "0x1p-1074").toOption == some 1
#guard (floatBits 64 "0x1p-1075").toOption == some 0
#guard (floatBits 64 "0x1.0000000000001p-1075").toOption == some 1
#guard (floatBits 64 "0x1p-1022").toOption == some 0x0010000000000000

-- Finite overflow is rejected, but explicit infinity and every NaN payload are retained.
#guard (floatBits 32 "0x1.fffffep127").toOption == some 0x7f7fffff
#guard (floatBits 32 "0x1.ffffffp127").toOption.isNone
#guard (floatBits 64 "0x1.fffffffffffffp1023").toOption == some 0x7fefffffffffffff
#guard (floatBits 64 "0x1.fffffffffffff8p1023").toOption.isNone
#guard (floatBits 32 "+inf").toOption == some 0x7f800000
#guard (floatBits 64 "-inf").toOption == some 0xfff0000000000000
#guard (floatBits 32 "nan").toOption == some 0x7fc00000
#guard (floatBits 64 "-nan").toOption == some 0xfff8000000000000
#guard (floatBits 32 "nan:0x1").toOption == some 0x7f800001
#guard (floatBits 32 "-nan:0x7f_ffff").toOption == some 0xffffffff
#guard (floatBits 64 "nan:0x1").toOption == some 0x7ff0000000000001
#guard (floatBits 32 "nan:0x0").toOption.isNone
#guard (floatBits 32 "nan:0x800000").toOption.isNone

-- Huge exponents are decided without allocating huge powers or shifts.
#guard (floatBits 32 "1e999999999999999999999").toOption.isNone
#guard (floatBits 32 "-1e-999999999999999999999").toOption == some 0x80000000
#guard (floatBits 64 "0x1p999999999999999999999").toOption.isNone
#guard (floatBits 64 "0x1p-999999999999999999999").toOption == some 0

#guard ([".1", "0x.1p0", "1__0", "1._0", "1_.0", "1e", "1e+", "1e1e2",
  "1.2.3", "nan:0x", "NaN", "INF", "0X1p0", "--1", "1e0x1"].all fun s =>
    (floatBits 32 s).toOption.isNone)
