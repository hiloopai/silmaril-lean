module

public import Silmaril.Machine.CBackend.Lir.Absint.Check.Defs

/-!
# `parse_hex4` (cJSON acc76239, gcc 13.3, -O2 build): certified memory safety

`parse_hex4(const unsigned char *input)` decodes four hex digits. This module
lifts its x86-64 machine code (from the static fuzzer binary
`cjson_read_fuzzer.o2`, sha256 `24d6c4703dacb153…`, in the proto corpus of
`research/silmaril-binary-verify`) to Lir, and checks an analyser-produced
post-fixpoint with `Absint.check` in the kernel. `memSafe` follows: every
memory access of every run reads one of the four input bytes.

Trust: the checker and `check_sound` are proved. The lift from x86 to Lir
was produced by `scripts/absint/absint.py` and is *not* checked against the x86
semantics yet; the kernel-checked examples at the end compare the Lir program
with the native machine code on 64 inputs.

Size: 33 x86 instructions (112 bytes), 10 Lir blocks,
55 Lir operations; certificate: 31 entries (as analysed).
-/

@[expose] public section

namespace Silmaril.Machine.Lir.Absint.ParseHex4O2

/-- The proposed Lir lift (registers: rax=0 … rdi=7, temporaries from 16). -/
def prog : Prog Nat := ⟨[{
  params := [.reg 7]
  entry := 0
  blocks := [
    -- block 0: x86 0x401b20
    ⟨[.op (.const 16 0#64),
        .op (.unary .zext32 1 16),
        .op (.const 17 0#64),
        .op (.unary .zext32 0 17),
        .op (.binary .add 18 7 1),
        .op (.load .b1 .zero 2 18 0),
        .op (.const 20 18446744073709551568#64),
        .op (.binary .add 19 2 20),
        .op (.unary .zext32 6 19),
        .op (.const 21 9#64),
        .op (.unary .zext8 22 6),
        .op (.binary (.cmp .gtu) 23 22 21)],
      .branch 23 4 1⟩,
    -- block 1: x86 0x401b31
    ⟨[.op (.binary .add 16 0 2),
        .op (.const 18 18446744073709551568#64),
        .op (.binary .add 17 16 18),
        .op (.unary .zext32 0 17)],
      .jump 2⟩,
    -- block 2: x86 0x401b35
    ⟨[.op (.const 16 3#64),
        .op (.binary (.cmp .eq) 17 1 16)],
      .branch 17 6 3⟩,
    -- block 3: x86 0x401b3b
    ⟨[.op (.const 16 1#64),
        .op (.binary .add 17 1 16),
        .op (.move 1 17),
        .op (.const 18 4#64),
        .op (.binary .shl32 0 0 18),
        .op (.binary .add 19 7 1),
        .op (.load .b1 .zero 2 19 0),
        .op (.const 21 18446744073709551568#64),
        .op (.binary .add 20 2 21),
        .op (.unary .zext32 6 20),
        .op (.const 22 9#64),
        .op (.unary .zext8 23 6),
        .op (.binary (.cmp .leu) 24 23 22)],
      .branch 24 1 4⟩,
    -- block 4: x86 0x401b4f
    ⟨[.op (.const 17 18446744073709551551#64),
        .op (.binary .add 16 2 17),
        .op (.unary .zext32 6 16),
        .op (.const 18 5#64),
        .op (.unary .zext8 19 6),
        .op (.binary (.cmp .gtu) 20 19 18)],
      .branch 20 7 5⟩,
    -- block 5: x86 0x401b58
    ⟨[.op (.binary .add 16 0 2),
        .op (.const 18 18446744073709551561#64),
        .op (.binary .add 17 16 18),
        .op (.unary .zext32 0 17),
        .op (.const 19 3#64),
        .op (.binary (.cmp .ne) 20 1 19)],
      .branch 20 3 6⟩,
    -- block 6: x86 0x401b62
    ⟨[],
      .ret [.reg 0]⟩,
    -- block 7: x86 0x401b68
    ⟨[.op (.const 17 18446744073709551519#64),
        .op (.binary .add 16 2 17),
        .op (.unary .zext32 6 16),
        .op (.const 18 5#64),
        .op (.unary .zext8 19 6),
        .op (.binary (.cmp .gtu) 20 19 18)],
      .branch 20 9 8⟩,
    -- block 8: x86 0x401b71
    ⟨[.op (.binary .add 16 0 2),
        .op (.const 18 18446744073709551529#64),
        .op (.binary .add 17 16 18),
        .op (.unary .zext32 0 17)],
      .jump 2⟩,
    -- block 9: x86 0x401b80
    ⟨[.op (.const 16 0#64),
        .op (.unary .zext32 0 16)],
      .ret [.reg 0]⟩
  ] }]⟩

/-- The certificate: the regions and the entry state of every block. -/
def cert : Cert Nat := ⟨[(0, 4)], [
  ⟨[(7, .off 0 0 0)], []⟩,
  ⟨[(1, .num 0 3), (6, .num 0 4294967295), (7, .off 0 0 0)], []⟩,
  ⟨[(0, .num 0 4294967295), (1, .num 0 3), (6, .num 0 4294967295), (7, .off 0 0 0)], []⟩,
  ⟨[(0, .num 0 4294967295), (1, .num 0 2), (6, .num 0 4294967295), (7, .off 0 0 0)], []⟩,
  ⟨[(1, .num 0 3), (6, .num 0 4294967295), (7, .off 0 0 0)], []⟩,
  ⟨[(1, .num 0 3), (6, .num 0 4294967295), (7, .off 0 0 0)], []⟩,
  ⟨[(0, .num 0 4294967295), (1, .num 3 3), (6, .num 0 4294967295), (7, .off 0 0 0)], []⟩,
  ⟨[(1, .num 0 3), (6, .num 0 4294967295), (7, .off 0 0 0)], []⟩,
  ⟨[(1, .num 0 3), (6, .num 0 4294967295), (7, .off 0 0 0)], []⟩,
  ⟨[(1, .num 0 3), (6, .num 0 4294967295), (7, .off 0 0 0)], []⟩
]⟩

set_option maxRecDepth 100000 in
/-- The kernel checks the certificate. -/
theorem cert_ok : check prog 0 cert = true := by decide +kernel

/-- **`parse_hex4` touches only its 4-byte input.** For every input pointer `a` whose
4-byte buffer lies below `2^64`, every load and store of every run of the lifted
function from its entry accesses bytes inside `[a, a + 4)`. -/
theorem memSafe (a : Word) (mem : Memory) (ha : a.toNat + 4 < 2 ^ 64)
    {s₀ s : State Nat} (h₀ : prog.start 0 [a] mem = some s₀) (hr : Steps prog s₀ s)
    {addr : Nat} {w : Width} (hacc : access? prog s = some (addr, w)) :
    a.toNat ≤ addr ∧ addr + w.bytes ≤ a.toNat + 4 := by
  simp only [Prog.start, Prog.enter, Prog.func?, prog, Option.bind, Frame.writeAll,
    Frame.write, Option.map, List.getElem?_cons_zero, Option.some.injEq] at h₀
  subst h₀
  have hsym : symbols [.reg 7] ((Frame.empty : Frame Nat).set 7 a) 0 = a := by
    simp [symbols, Frame.get]
  obtain ⟨sym, n, hmem, h1, h2⟩ := check_sound cert_ok rfl rfl rfl
    (by intro s' n' h; simp only [cert, List.mem_cons, List.not_mem_nil, or_false,
          Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [hsym]; exact ha) hr hacc
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  rw [hsym] at h1 h2
  exact ⟨h1, h2⟩

/-- The checker is not vacuous: the same invariants with a region one byte
shorter are rejected. -/
example : check prog 0 { cert with regions := [(0, 3)] } = false := by decide +kernel

/-- `memSafe` is not vacuous: a run from the entry reaches a load of the first
input byte. -/
example : ∃ s, Steps prog ⟨⟨0, 0, 0⟩, (Frame.empty : Frame Nat).set 7 0#64, [],
    Memory.ofList 8 [48#8, 48#8, 48#8, 48#8]⟩ s ∧ access? prog s = some (0, .b1) :=
  ⟨_, run_running (n := 5) rfl, rfl⟩

/-! ## Lift conformance: the Lir program against the native machine code

Each example states that the Lir program, run by Lean's `step` (fuel 200) on a
4-byte input at address 0, returns the value the native x86 code returned when
`scripts/absint/absint.py` called it (ctypes, on an mmap'd copy of its bytes).
The kernel checks each example; the expected values come from the hardware.
This tests the lift; it does not prove it. -/

example : (prog.runMain 200 0 [0] (Memory.ofList 8 [99#8, 100#8, 49#8, 56#8])).returnedValues? =
    some [52504#64] := by decide +kernel  -- b'cd18'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [247#8, 130#8, 124#8, 103#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\xf7\x82|g'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [57#8, 102#8, 98#8, 67#8])).returnedValues? =
    some [40892#64] := by decide +kernel  -- b'9fbC'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [228#8, 232#8, 55#8, 129#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\xe4\xe87\x81'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [52#8, 57#8, 52#8, 51#8])).returnedValues? =
    some [18755#64] := by decide +kernel  -- b'4943'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [158#8, 204#8, 64#8, 252#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x9e\xcc@\xfc'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [66#8, 68#8, 52#8, 57#8])).returnedValues? =
    some [48457#64] := by decide +kernel  -- b'BD49'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [25#8, 186#8, 18#8, 230#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x19\xba\x12\xe6'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [70#8, 97#8, 102#8, 66#8])).returnedValues? =
    some [64251#64] := by decide +kernel  -- b'FafB'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [25#8, 90#8, 111#8, 80#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x19ZoP'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [68#8, 69#8, 54#8, 66#8])).returnedValues? =
    some [56939#64] := by decide +kernel  -- b'DE6B'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [122#8, 113#8, 221#8, 133#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'zq\xdd\x85'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [56#8, 49#8, 66#8, 48#8])).returnedValues? =
    some [33200#64] := by decide +kernel  -- b'81B0'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [23#8, 184#8, 215#8, 102#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x17\xb8\xd7f'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [70#8, 69#8, 48#8, 68#8])).returnedValues? =
    some [65037#64] := by decide +kernel  -- b'FE0D'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [126#8, 211#8, 222#8, 85#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'~\xd3\xdeU'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [55#8, 97#8, 50#8, 54#8])).returnedValues? =
    some [31270#64] := by decide +kernel  -- b'7a26'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [234#8, 145#8, 56#8, 61#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\xea\x918='
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [52#8, 66#8, 101#8, 50#8])).returnedValues? =
    some [19426#64] := by decide +kernel  -- b'4Be2'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [20#8, 254#8, 81#8, 224#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x14\xfeQ\xe0'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [65#8, 102#8, 51#8, 57#8])).returnedValues? =
    some [44857#64] := by decide +kernel  -- b'Af39'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [141#8, 74#8, 180#8, 31#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x8dJ\xb4\x1f'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [66#8, 97#8, 66#8, 54#8])).returnedValues? =
    some [47798#64] := by decide +kernel  -- b'BaB6'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [246#8, 204#8, 154#8, 140#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\xf6\xcc\x9a\x8c'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [67#8, 57#8, 101#8, 50#8])).returnedValues? =
    some [51682#64] := by decide +kernel  -- b'C9e2'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [152#8, 204#8, 98#8, 81#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x98\xccbQ'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [67#8, 55#8, 57#8, 53#8])).returnedValues? =
    some [51093#64] := by decide +kernel  -- b'C795'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [48#8, 210#8, 47#8, 8#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'0\xd2/\x08'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [68#8, 70#8, 56#8, 102#8])).returnedValues? =
    some [57231#64] := by decide +kernel  -- b'DF8f'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [17#8, 22#8, 173#8, 193#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x11\x16\xad\xc1'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [52#8, 52#8, 49#8, 50#8])).returnedValues? =
    some [17426#64] := by decide +kernel  -- b'4412'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [229#8, 179#8, 236#8, 212#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\xe5\xb3\xec\xd4'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [66#8, 70#8, 99#8, 65#8])).returnedValues? =
    some [49098#64] := by decide +kernel  -- b'BFcA'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [70#8, 133#8, 207#8, 60#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'F\x85\xcf<'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [54#8, 70#8, 67#8, 100#8])).returnedValues? =
    some [28621#64] := by decide +kernel  -- b'6FCd'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [148#8, 70#8, 115#8, 126#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x94Fs~'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [70#8, 69#8, 98#8, 50#8])).returnedValues? =
    some [65202#64] := by decide +kernel  -- b'FEb2'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [83#8, 156#8, 29#8, 124#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'S\x9c\x1d|'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [67#8, 69#8, 97#8, 54#8])).returnedValues? =
    some [52902#64] := by decide +kernel  -- b'CEa6'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [62#8, 4#8, 187#8, 69#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'>\x04\xbbE'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [51#8, 55#8, 98#8, 53#8])).returnedValues? =
    some [14261#64] := by decide +kernel  -- b'37b5'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [85#8, 109#8, 208#8, 15#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'Um\xd0\x0f'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [51#8, 52#8, 55#8, 49#8])).returnedValues? =
    some [13425#64] := by decide +kernel  -- b'3471'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [209#8, 146#8, 162#8, 232#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\xd1\x92\xa2\xe8'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [66#8, 68#8, 70#8, 50#8])).returnedValues? =
    some [48626#64] := by decide +kernel  -- b'BDF2'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [6#8, 31#8, 162#8, 48#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x06\x1f\xa20'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [68#8, 67#8, 51#8, 99#8])).returnedValues? =
    some [56380#64] := by decide +kernel  -- b'DC3c'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [23#8, 94#8, 213#8, 251#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x17^\xd5\xfb'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [51#8, 49#8, 68#8, 48#8])).returnedValues? =
    some [12752#64] := by decide +kernel  -- b'31D0'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [49#8, 246#8, 248#8, 47#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'1\xf6\xf8/'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [51#8, 102#8, 54#8, 49#8])).returnedValues? =
    some [16225#64] := by decide +kernel  -- b'3f61'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [239#8, 173#8, 5#8, 139#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\xef\xad\x05\x8b'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [100#8, 68#8, 51#8, 56#8])).returnedValues? =
    some [56632#64] := by decide +kernel  -- b'dD38'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [17#8, 56#8, 18#8, 165#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x118\x12\xa5'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [57#8, 98#8, 100#8, 53#8])).returnedValues? =
    some [39893#64] := by decide +kernel  -- b'9bd5'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [15#8, 128#8, 119#8, 10#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x0f\x80w\n'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [68#8, 51#8, 99#8, 54#8])).returnedValues? =
    some [54214#64] := by decide +kernel  -- b'D3c6'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [66#8, 91#8, 231#8, 187#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'B[\xe7\xbb'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [102#8, 67#8, 53#8, 70#8])).returnedValues? =
    some [64607#64] := by decide +kernel  -- b'fC5F'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [52#8, 247#8, 196#8, 14#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'4\xf7\xc4\x0e'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [70#8, 53#8, 53#8, 97#8])).returnedValues? =
    some [62810#64] := by decide +kernel  -- b'F55a'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [135#8, 64#8, 30#8, 152#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'\x87@\x1e\x98'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [101#8, 70#8, 53#8, 48#8])).returnedValues? =
    some [61264#64] := by decide +kernel  -- b'eF50'
example : (prog.runMain 200 0 [0] (Memory.ofList 8 [120#8, 174#8, 104#8, 230#8])).returnedValues? =
    some [0#64] := by decide +kernel  -- b'x\xaeh\xe6'

end Silmaril.Machine.Lir.Absint.ParseHex4O2
