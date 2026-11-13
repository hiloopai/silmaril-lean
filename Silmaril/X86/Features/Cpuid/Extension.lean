module

public import Silmaril.X86.Features.Cpuid.Profile
public import Silmaril.X86.Features.Lattice.Wire
public import Silmaril.X86.Model.Profile

/-!
# CPUID and XGETBV as an extension

`sysExt p` is the extension of the feature-parametric machine that executes the
two instructions through which user-mode code observes its processor, with the
answers of the profile `p`:

* **CPUID** (`0F A2`, SDM Vol. 2A): reads EAX (leaf) and ECX (subleaf), and
  writes `p.cpuid leaf subleaf` to EAX, EBX, ECX and EDX, zero-extended to 64
  bits. Flags, memory and the other registers are unchanged. The register
  effect is `Ext.Wire.cpuidState`, the same function the byte-faithful `Wire`
  machine uses (`sysExt_cpuid_agrees_wire`).
* **XGETBV** (`0F 01 D0`, SDM Vol. 2B): #UD unless CR4.OSXSAVE is set, which user
  mode observes as CPUID.1:ECX.OSXSAVE[bit 27] (`Profile.osxsave`). With ECX = 0
  it writes XCR0 to EDX:EAX (the upper halves of RAX and RDX cleared). ECX = 1
  (XINUSE, only when CPUID.(EAX=0DH,ECX=1):EAX[2] is set) is not modelled
  (`unmodeled`, chaos); any other ECX is #GP(0).

Neither instruction requires a `Feature`: CPUID exists on every x86-64
processor, and XGETBV's precondition (OSXSAVE) is part of the profile rather
than a feature, so it raises `Fault.invalidOpcode`, a settled outcome.

## Decoding

The decoder accepts exactly the two plain encodings (no prefixes) and is a
prefix code (`sysDecode_eq_some_iff`). The integer decoder rejects both
(`ext_decode_sys`: its length decoder has no entry for `0F A2` or `0F 01`), so
a step at such bytes goes to the extension (`step_sys`).

## Relation to the other extensions

* The hub's `X86.cpuidExt pl` (`Model/Profile.lean`, CPUID alone, the extension of
  `Cpu.config`) embeds into `sysExt p` whenever `p.platform = pl`
  (`cpuidExt_embeds_sys`): same decoding, no features, the same execution. So
  `Cpu.config c ≤ c.toProfile.config` (`Models.lean`): everything proved for a
  hub `Cpu` holds with XGETBV added.
* `wireExt` (`Lattice/Wire.lean`) also decodes `0F A2`. It agrees with `sysExt p` at
  the decoded length (`cpuid_agrees_wire`); `Wire` advances RIP by the encoding's
  length whatever length it is passed, so the agreement is at that length, not an
  `Embeds`. A configuration should contain only one of `sysExt` and `wireExt`,
  since they are not disjoint.
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Sz)
open Silmaril.Process (Memory)

/-- The processor-identification instructions. -/
inductive SysInstr where
  | cpuid
  | xgetbv
  deriving DecidableEq, Repr

namespace SysInstr

/-- The encodings. -/
def encode : SysInstr → List Byte
  | .cpuid => [0x0F, 0xA2]
  | .xgetbv => [0x0F, 0x01, 0xD0]

/-- Decode a plain CPUID or XGETBV. -/
def decode : List Byte → Option (SysInstr × Nat)
  | b0 :: b1 :: rest =>
    if b0 = 0x0F ∧ b1 = 0xA2 then some (.cpuid, 2)
    else if b0 = 0x0F ∧ b1 = 0x01 ∧ rest.head? = some 0xD0 then some (.xgetbv, 3)
    else none
  | _ => none

/-- The decoder is the prefix code of `encode`. -/
theorem decode_eq_some_iff {bytes : List Byte} {x : SysInstr} {n : Nat} :
    decode bytes = some (x, n) ↔ n = (encode x).length ∧ bytes.take n = encode x := by
  rcases bytes with _ | ⟨b0, _ | ⟨b1, rest⟩⟩
  · cases x <;> simp [decode, encode]
  · cases x <;> simp [decode, encode] <;> (intro h; subst h; simp)
  · rcases rest with _ | ⟨b2, rest⟩
    · cases x <;> simp only [decode, encode] <;> split_ifs <;> simp_all; grind
    · cases x <;> simp only [decode, encode] <;> split_ifs <;> simp_all <;> grind

theorem decode_encode_append (x : SysInstr) (rest : List Byte) :
    decode (encode x ++ rest) = some (x, (encode x).length) :=
  decode_eq_some_iff.mpr ⟨rfl, by simp⟩

/-- The decoder laws. -/
def decoder : Machine.Decoder SysInstr where
  decode := decode
  encode := encode
  decode_length_pos h := by
    obtain ⟨rfl, -⟩ := decode_eq_some_iff.mp h
    rename_i x; cases x <;> decide
  decode_length_le h := by
    obtain ⟨rfl, ht⟩ := decode_eq_some_iff.mp h
    have := congrArg List.length ht
    simp only [List.length_take] at this
    omega
  decode_append := by
    intro bytes x n extra h
    obtain ⟨rfl, ht⟩ := decode_eq_some_iff.mp h
    refine decode_eq_some_iff.mpr ⟨rfl, ?_⟩
    have hle : (encode x).length ≤ bytes.length := by
      have := congrArg List.length ht
      simp only [List.length_take] at this
      omega
    rw [List.take_append_of_le_length hle, ht]
  decode_take h := by
    obtain ⟨rfl, ht⟩ := decode_eq_some_iff.mp h
    exact decode_eq_some_iff.mpr ⟨rfl, by rw [List.take_take, Nat.min_self, ht]⟩
  decode_encode_append := decode_encode_append

end SysInstr

/-! ## Semantics -/

/-- XGETBV with ECX = 0: EDX:EAX ← XCR0, zero-extended. -/
def xgetbvState (xcr0 : BitVec 64) (s : X86.State) : X86.State :=
  Sz.d.write (Sz.d.write s .rax (xcr0.extractLsb' 0 32)) .rdx (xcr0.extractLsb' 32 32)

/-- Execute CPUID or XGETBV on the profile `p`, with RIP advanced by the decoded
length (as every `Extension` does; the decoder only produces the encodings'
lengths). -/
def sysExec (p : Profile) : SysInstr → Nat → State → Memory → Result
  | .cpuid, n, s, memory =>
    Result.pure (fun s => s.setCore (Ext.Wire.cpuidState p.platform s.core)) n s memory
  | .xgetbv, n, s, memory =>
    if !p.osxsave then .fault .invalidOpcode
    else
      let ecx := Sz.d.read s.core .rcx
      if ecx = 0 then Result.pure (fun s => s.setCore (xgetbvState p.xcr0 s.core)) n s memory
      else if ecx = 1 then .unmodeled
      else .fault .generalProtection

/-- CPUID and XGETBV, answering as the profile `p`. -/
def sysExt (p : Profile) : Extension where
  name := "CPUID/XGETBV"
  Syntax := SysInstr
  decoder := SysInstr.decoder
  requires _ := []
  exec := sysExec p

@[simp] theorem sysExt_decode (p : Profile) : (sysExt p).decoder.decode = SysInstr.decode := rfl

@[simp] theorem sysExt_requires (p : Profile) (x : SysInstr) : (sysExt p).requires x = [] := rfl

theorem cpuidState_rip (platform : Ext.Wire.Platform) (s : X86.State) :
    (Ext.Wire.cpuidState platform s).rip = s.rip := rfl

theorem xgetbvState_rip (xcr0 : BitVec 64) (s : X86.State) : (xgetbvState xcr0 s).rip = s.rip :=
  rfl

/-- CPUID is a pure register instruction. -/
theorem sysExt_cpuid_pure (p : Profile) : (sysExt p).Pure SysInstr.cpuid :=
  Extension.Pure.of_eq (e := sysExt p) (fun s => s.setCore (Ext.Wire.cpuidState p.platform s.core))
    (fun _ => rfl) fun _ _ _ => rfl

/-! ## The register effects -/

/-- CPUID's results, zero-extended to 64 bits. -/
theorem cpuidState_read (platform : Ext.Wire.Platform) (s : X86.State) :
    let reply := platform.cpuid (Sz.d.read s .rax) (Sz.d.read s .rcx)
    (Ext.Wire.cpuidState platform s).read .rax = reply.eax.setWidth 64 ∧
    (Ext.Wire.cpuidState platform s).read .rbx = reply.ebx.setWidth 64 ∧
    (Ext.Wire.cpuidState platform s).read .rcx = reply.ecx.setWidth 64 ∧
    (Ext.Wire.cpuidState platform s).read .rdx = reply.edx.setWidth 64 := by
  simp [Ext.Wire.cpuidState, Sz.write]

/-- XGETBV's results: the low and high halves of XCR0, zero-extended. -/
theorem xgetbvState_read (xcr0 : BitVec 64) (s : X86.State) :
    (xgetbvState xcr0 s).read .rax = (xcr0.extractLsb' 0 32).setWidth 64 ∧
    (xgetbvState xcr0 s).read .rdx = (xcr0.extractLsb' 32 32).setWidth 64 := by
  simp [xgetbvState, Sz.write]

/-! ## The integer decoder rejects both encodings -/

/-- `Ext.decode` rejects every window starting with CPUID or XGETBV. -/
theorem ext_decode_sys (x : SysInstr) (more : List Byte) :
    Ext.decode (x.encode ++ more) = none := by
  have h : Ext.parseRaw x.encode = .bad := by cases x <;> rfl
  unfold Ext.decode
  rw [Ext.good_parseRaw.bad h more]

/-! ## Steps -/

/-- A step at a CPUID or XGETBV. -/
theorem step_sys {F : FeatureSet} {exts : List Extension} {exit : Word} {m : MState}
    {p : Profile} (hd : Extension.PairwiseDisjoint exts) (he : sysExt p ∈ exts) {x : SysInstr}
    (fetched : m.memory.fetchBytes m.state.core.rip.toNat x.encode.length = some x.encode)
    (hperm : m.memory.Permitted .execute m.state.core.rip.toNat x.encode.length) :
    step F exts exit m =
      match sysExec p x x.encode.length m.state m.memory with
      | .retired s memory => .retired ⟨s, memory⟩
      | .fault f => .fault f
      | .unmodeled => .unmodeled := by
  obtain ⟨more, hmore⟩ := X86.fetchBytes_prefix_fetchWindow fetched (limit := maxInstrLength)
    (by cases x <;> decide)
  have hw : fetchWindow m.memory maxInstrLength m.state.core.rip.toNat = x.encode ++ more :=
    hmore.symm
  rw [step_of_ext (e := sysExt p) (x := x) (n := x.encode.length)
    (by rw [hw]; exact ext_decode_sys x more)
    (by rw [hw]; exact extDecode_of_mem hd he (SysInstr.decode_encode_append x more)) hperm]
  rfl

/-- `step_sys` with the execute permission read off the fetch. -/
theorem step_sys_fetch {F : FeatureSet} {exts : List Extension} {exit : Word} {m : MState}
    {p : Profile} (hd : Extension.PairwiseDisjoint exts) (he : sysExt p ∈ exts) {x : SysInstr}
    (fetched : m.memory.fetchBytes m.state.core.rip.toNat x.encode.length = some x.encode) :
    step F exts exit m =
      match sysExec p x x.encode.length m.state m.memory with
      | .retired s memory => .retired ⟨s, memory⟩
      | .fault f => .fault f
      | .unmodeled => .unmodeled :=
  step_sys hd he fetched (Memory.readWith_permitted fetched)

/-- CPUID retires with the profile's reply. -/
theorem step_cpuid {F : FeatureSet} {exts : List Extension} {exit : Word} {m : MState}
    {p : Profile} (hd : Extension.PairwiseDisjoint exts) (he : sysExt p ∈ exts)
    (fetched : m.memory.fetchBytes m.state.core.rip.toNat 2 = some [0x0F, 0xA2]) :
    step F exts exit m =
      .retired ⟨(m.state.setCore (Ext.Wire.cpuidState p.platform m.state.core)).advance 2,
        m.memory⟩ :=
  step_sys_fetch (x := .cpuid) hd he fetched

/-! ## The hub's CPUID, and the `Wire` CPUID -/

/-- **Consilience with the hub.** `X86.cpuidExt` (CPUID alone, `Model/Profile.lean`)
embeds into `sysExt p` on the platform `p.platform`. -/
theorem cpuidExt_embeds_sys (p : Profile) : (X86.cpuidExt p.platform).Embeds (sysExt p) := by
  refine ⟨fun _ => .cpuid, fun bytes _ n h => ?_, fun _ => rfl, fun _ _ _ _ => rfl⟩
  obtain ⟨ht, rfl⟩ := X86.cpuidDecode_eq_some h
  exact SysInstr.decode_eq_some_iff.mpr ⟨rfl, ht⟩

/-- `Wire` decodes CPUID, with its own two bytes. -/
theorem wire_decode_cpuid (rest : List Byte) :
    Ext.Wire.decode (SysInstr.encode .cpuid ++ rest) =
      some ⟨.cpuid, SysInstr.encode .cpuid⟩ :=
  Ext.Wire.decode_append (by decide) rest

/-- The `Wire` form of CPUID. -/
def wireCpuid : WireForm :=
  ⟨⟨.cpuid, SysInstr.encode .cpuid⟩, by
    have := wire_decode_cpuid []
    simp only [List.append_nil] at this
    exact ⟨this, by simpa using ext_decode_sys .cpuid []⟩⟩

/-- **Consilience with `Wire`.** On bytes starting with CPUID, `wireExt p.platform`
decodes `wireCpuid` with length 2, and at that length it executes exactly as
`sysExt p`'s CPUID. -/
theorem cpuid_agrees_wire (p : Profile) (rest : List Byte) (s : State) (m : Memory) :
    (wireExt p.platform).decoder.decode (SysInstr.encode .cpuid ++ rest) =
        some (wireCpuid, (SysInstr.encode .cpuid).length) ∧
      (wireExt p.platform).exec wireCpuid 2 s m = (sysExt p).exec .cpuid 2 s m := by
  refine ⟨?_, rfl⟩
  rw [wireExt_decode]
  exact (wireDecode_eq_some_iff (x := wireCpuid)).mpr
    ⟨ext_decode_sys .cpuid _, wire_decode_cpuid _, rfl⟩

end Silmaril.X86.Features
