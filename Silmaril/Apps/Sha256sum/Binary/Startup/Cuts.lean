module

public import Silmaril.Apps.Sha256sum.Binary.Startup.Facts

/-! # The cut points of the startup of `sha256sum-min`

The startup (argv = [prog], any environment, no option, the default operand `"-"`) runs with
no system call from `_start` (`0x401000`) to the read loop of `digest_file`. It is split at
two cut points of `X86Sys` states, both relative to a fixed launch context `Ctx` (the entry
stack pointer, the launch memory, the argument and environment strings):

```
_start ──▶ cmain ──set_program_name──▶ AtOptParse (0x4034a6)
       ──POSIXLY_CORRECT scan, option parsing (none), checks, operand "-"──▶ AtDigestEntry (0x402de0)
       ──digest_file prologue (c_streq "-", have_read_stdin, sha_init)──▶ read-loop head (0x402ef0)
```

* `AtOptParse`: in `cmain` at `0x4034a6`, right after `set_program_name` and
  `getopt_argv0 = argv[0]` (the stores to `program_name` and `getopt_argv0` done), before the
  scan of the environment for `POSIXLY_CORRECT=` (`lea (%r15,%rbx,1),%rsi`).
* `AtDigestEntry`: at `digest_file`'s entry (`0x402de0`) from the stdin-path call. `do_check`
  is 0, so `cmain` takes `je 0x40418f` at `0x4039b7` and calls from `0x40419a`
  (`mov %r14,%rdx; lea 0x70(%rsp),%rsi; mov %r12,%rdi; call digest_file`): the return address
  is **`0x40419f`** (the call at `0x403c7b` is on the `--check` branch). The operand is the
  literal `"-"` at `0x406052`, `bin` is `cmain`'s `0x70(%rsp)`, `missing` its `0x90(%rsp)`.

`cmain`'s frame: `csp = sp0 - 240` (six pushes and `sub $0xb8`, under the return address of
`call cmain` at `sp0 - 8`). The footprints: `W1` (the stack room below `sp0`, `program_name`,
`getopt_argv0`) up to `AtOptParse`, and `W2` (also `binary` and `argv[0]`'s slot, where the
default operand is stored) up to `AtDigestEntry`.

Status: definitions only.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Apps.Sha256sum.X86Sys (XState)

/-- The launch context of a startup run: the entry stack pointer, the launch memory, the
`argv[0]` pointer and string (with its NUL), the `envp` pointers and strings (with their
NULs). -/
structure Ctx where
  sp0 : Word
  m0 : Memory
  argv0 : Word
  arg : List Byte
  envs : List Word
  envStrs : List (List Byte)

/-- `L` (ending in a NUL) is readable at `p`. -/
def CString (m : Memory) (p : Word) (L : List Byte) : Prop :=
  L.getLast? = some 0 ∧ m.readBytes p.toNat L.length = some L

/-- What the launch gives (`SysModel.Launch`): the image mapped and read-only below `.data`,
the aligned stack pointer above the image and its room, the System V vectors (`argc = 1`),
the strings, which lie above the vectors. -/
structure LaunchFacts (c : Ctx) : Prop where
  mapped : Image.image.Mapped c.m0
  ro : Ro c.m0
  aligned : c.sp0.toNat % 16 = 0
  spLo : 0x423150 ≤ c.sp0.toNat
  spHi : c.sp0.toNat ≤ 0x7ffffffff000
  rw : ∀ acc : Silmaril.Process.Access, acc ≠ .execute →
    c.m0.Permitted acc (c.sp0.toNat - 0x10000) (0x10000 + 16)
  argc : loadN c.m0 c.sp0 8 = some 1#64
  argv0 : loadN c.m0 (c.sp0 + 8#64) 8 = some c.argv0
  argvEnd : loadN c.m0 (c.sp0 + 16#64) 8 = some 0#64
  envLen : c.envs.length = c.envStrs.length
  envw : ∀ k (hk : k < c.envs.length),
    loadN c.m0 (c.sp0 + BitVec.ofNat 64 (24 + 8 * k)) 8 = some c.envs[k]
  envEnd : loadN c.m0 (c.sp0 + BitVec.ofNat 64 (24 + 8 * c.envs.length)) 8 = some 0#64
  argStr : CString c.m0 c.argv0 c.arg
  envStr : ∀ k (hk : k < c.envs.length) (hk' : k < c.envStrs.length),
    CString c.m0 c.envs[k] c.envStrs[k]
  above : ∀ p ∈ c.argv0 :: c.envs, c.sp0.toNat + 8 * (c.envs.length + 4) ≤ p.toNat

/-- Up to `AtOptParse`: the stack room below `sp0`, `program_name`, `getopt_argv0`. -/
def W1 (sp0 : Word) (a : Nat) : Prop :=
  (sp0.toNat - 0x10000 ≤ a ∧ a < sp0.toNat) ∨ (0x412118 ≤ a ∧ a < 0x412128)

/-- Up to `AtDigestEntry`: also `binary` (`0x409010`) and `argv[0]`'s slot. -/
def W2 (sp0 : Word) (a : Nat) : Prop :=
  W1 sp0 a ∨ (0x409010 ≤ a ∧ a < 0x409014) ∨ (sp0.toNat + 8 ≤ a ∧ a < sp0.toNat + 16)

/-- **`cmain`'s entry** (`0x4033f0`), from `_start`'s `call cmain`: the entry stack pointer in
`rdi` (`mov %rsp,%rdi` before `and $-16,%rsp`; `sp0` is aligned), the return address
`0x40100e` pushed at `sp0 - 8`; only `W1` written (the push is in the stack room). -/
structure AtCmainEntry (c : Ctx) (s : XState) : Prop where
  faulted : s.faulted = false
  rip : s.core.rip = 0x4033f0#64
  rsp : s.core.read .rsp = c.sp0 - 8#64
  rdi : s.core.read .rdi = c.sp0
  mem : Memory.WritesWithin c.m0 s.memory (W1 c.sp0)

/-- **`cmain` after `set_program_name`** (`0x4034a6`): `argc` in `rsi` (`movslq`) and `r14`,
`argv` in `r15`, `8 * (argc + 1)` in `rbx`, the entry stack pointer in `r11`, `argv[0]` in
`rdi`, `posixly_correct = 0` in `r12`, `cmain`'s frame at `sp0 - 240`; only `W1` written. -/
structure AtOptParse (c : Ctx) (s : XState) : Prop where
  faulted : s.faulted = false
  rip : s.core.rip = 0x4034a6#64
  rsp : s.core.read .rsp = c.sp0 - 240#64
  rsi : s.core.read .rsi = 1#64
  r11 : s.core.read .r11 = c.sp0
  r12 : s.core.read .r12 = 0#64
  r14 : s.core.read .r14 = 1#64
  r15 : s.core.read .r15 = c.sp0 + 8#64
  rbx : s.core.read .rbx = 16#64
  rdi : s.core.read .rdi = c.argv0
  mem : Memory.WritesWithin c.m0 s.memory (W1 c.sp0)

/-- **`digest_file`'s entry from the stdin-path call** (`0x402de0`, return address
`0x40419f` at `sp0 - 248`): the operand `"-"` (`0x406052`) in `rdi`, `bin` (`csp + 0x70`) in
`rsi`, `missing` (`csp + 0x90`) in `rdx`, where `csp = sp0 - 240`; only `W2` written. -/
structure AtDigestEntry (c : Ctx) (s : XState) : Prop where
  faulted : s.faulted = false
  rip : s.core.rip = 0x402de0#64
  rsp : s.core.read .rsp = c.sp0 - 248#64
  ret : loadN s.memory (c.sp0 - 248#64) 8 = some 0x40419f#64
  rdi : s.core.read .rdi = 0x406052#64
  rsi : s.core.read .rsi = c.sp0 - 240#64 + 0x70#64
  rdx : s.core.read .rdx = c.sp0 - 240#64 + 0x90#64
  mem : Memory.WritesWithin c.m0 s.memory (W2 c.sp0)

end Silmaril.Apps.Sha256sum.Binary.Startup

namespace Silmaril.Apps.Sha256sum.Binary.Startup

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (loadN)

/-- A byte of a string, through a footprint that misses it. -/
theorem cstring_load {m0 m : Memory} {W : Nat → Prop} (hww : Memory.WritesWithin m0 m W)
    {p : Word} {L : List Byte} (hs : CString m0 p L)
    (hout : ∀ i < L.length, ¬ W (p.toNat + i)) (q : Word) (idx : Nat) (hidx : idx < L.length)
    (hq : q.toNat = p.toNat + idx) :
    loadN m q 1 = some (L[idx].setWidth 64) := by
  rw [loadN_ww hww (fun i hi => by
    rw [hq]; have := hout (idx + i) (by omega); simpa [Nat.add_assoc] using this)]
  have hr := Memory.readBytes_sub_range hs.2 (offset := idx) (len := 1) hidx (by omega)
  unfold loadN
  rw [hq, hr]
  simp only [Option.map_some, Option.some.injEq]
  rw [List.take_one, List.head?_drop, List.getElem?_eq_getElem hidx]
  simp only [Option.toList_some, Silmaril.X86.Ext.leValue]
  apply BitVec.eq_of_toNat_eq
  simp

theorem CString.pos {m : Memory} {p : Word} {L : List Byte} (hs : CString m p L) :
    0 < L.length := by
  have := hs.1; cases h : L with
  | nil => rw [h] at this; simp at this
  | cons _ _ => simp

/-- A byte of the string that is not its terminating NUL is followed by another byte. -/
theorem CString.lt {m : Memory} {p : Word} {L : List Byte} (hs : CString m p L) {i : Nat}
    (hi : i < L.length) (hnz : L[i] ≠ 0) : i + 1 < L.length := by
  have hl := hs.1
  rw [List.getLast?_eq_getElem?] at hl
  by_contra hc
  have e : i = L.length - 1 := by omega
  subst e
  rw [List.getElem?_eq_getElem hi] at hl
  exact hnz (Option.some.inj hl)

theorem CString.lt! {m : Memory} {p : Word} {L : List Byte} (hs : CString m p L) {i : Nat}
    (hi : i < L.length) (hnz : L[i]! ≠ 0) : i + 1 < L.length :=
  hs.lt hi (by rwa [getElem!_pos L i hi] at hnz)

/-- The string does not wrap. -/
theorem CString.noWrap {m : Memory} {p : Word} {L : List Byte} (hs : CString m p L) :
    p.toNat + L.length ≤ 2 ^ 64 := by
  have := Memory.readWith_permitted hs.2
  rw [Memory.Permitted, Memory.checkSpan_iff] at this
  simpa [Silmaril.Process.addressLimit] using this.2.1

/-- A byte of the read-only data segment (`.rodata`, `[0x406000, 0x408010)`), through a
footprint below the stack pointer and in `.data`/`.bss`. -/
theorem rodata_load {m0 m : Memory} (hm : Image.image.Mapped m0) {W : Nat → Prop}
    (hww : Memory.WritesWithin m0 m W) (off : Nat) (hoff : off < 0x2010)
    (hout : ¬ W (0x406000 + off)) :
    loadN m (BitVec.ofNat 64 (0x406000 + off)) 1 =
      some (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue ((Image.seg2.contents.drop off).take 1))) := by
  rw [loadN_ww hww (fun i hi => by
    have : i = 0 := by omega
    subst this
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simpa using hout)]
  have := readWith_segment hm seg2_mem Image.image_wf (acc := .read) (by decide) off 1
    (by simp [Image.seg2]; omega) (by decide)
  unfold loadN Memory.readBytes
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [Image.seg2] at this ⊢
  rw [this]
  rfl

/-- A byte of the string at `p`, by its address. -/
theorem cstring_load2 {m0 m : Memory} {W : Nat → Prop} (hww : Memory.WritesWithin m0 m W)
    {p : Word} {L : List Byte} (hs : CString m0 p L)
    (hout : ∀ i < L.length, ¬ W (p.toNat + i)) (q : Word) (h1 : p.toNat ≤ q.toNat)
    (h2 : q.toNat < p.toNat + L.length) :
    loadN m q 1 = some (L[q.toNat - p.toNat]!.setWidth 64) := by
  rw [cstring_load hww hs hout q (q.toNat - p.toNat) (by omega) (by omega),
    getElem!_pos L _ (by omega)]

theorem add_ofNat_sub (x : Word) (j : Nat) : x + BitVec.ofNat 64 j - x = BitVec.ofNat 64 j := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem toNat_add_ofNat (x : Word) (j : Nat) (h : x.toNat + j < 2 ^ 64) :
    (x + BitVec.ofNat 64 j).toNat = x.toNat + j := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2^64)]; omega

theorem add_ofNat_succ (x : Word) (j : Nat) :
    x + BitVec.ofNat 64 j + 1#64 = x + BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

end Silmaril.Apps.Sha256sum.Binary.Startup

/-- A footprint side condition of `sv_mem`: the store's span is inside `W1`/`W2`. -/
macro "sv_within" : tactic => `(tactic| (intro i hi; (try simp only [Silmaril.Machine.LittleEndian.encodeWords_length, Silmaril.X86.length_encodeWords_singleton, Silmaril.X86.Ext.length_leBytes, List.length_cons, List.length_nil] at hi); simp only [Silmaril.Apps.Sha256sum.Binary.Startup.W1, Silmaril.Apps.Sha256sum.Binary.Startup.W2]; sv_disj))
