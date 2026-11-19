module

public import Silmaril.Machine.Abi.Conformance.LeafArith.Witness.Defs
public import Silmaril.X86.Ladder.LeafArith.Thms
public import Silmaril.X86.Cert.Kinds.Thms
public import Silmaril.Proofs.Machine.Abi.Conformance.SysvInt
public import Silmaril.Proofs.Machine.Abi.Conformance.Basic
public import Silmaril.X86.Open.FsBase.Thms

/-!
# ABI conformance of rung 01 `clamp_i32` and `sat_add_u32`: proofs

From first-return contracts of the code (`clamp_strict`, `sat_strict`: track A's block
certificates of the pinned gcc `-O2` code through the generic `BlockCert.FunCert.strict`, as
`Machine.Abi.OpenMachine` derives them) by `conforms_of_strict`. Non-vacuity is a concrete
state: the 181 code bytes at `0x401370`, `rsp = 0x8ff8` with the return address `0x401000`,
one region mapping every address read-write, the arguments in `rdi`, `rsi`, `rdx`. The memory
construction follows `Machine.Abi.OpenMachine`'s non-vacuity witness (copied: it is a `Proofs`
module of another topic).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance.LeafArith

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region addressLimit)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86
open Silmaril.X86.Ladder.LeafArith
open Silmaril.Machine.Abi
open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options callOf)
open Silmaril.Proofs.Machine.Abi.Conformance.SysvInt
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.LeafArith
open Silmaril.Machine.Abi.Conformance.LeafArith.Witness
open Silmaril.Proofs.Machine.Abi.Conformance

/-! ## A concrete entry state -/





theorem permits_all (acc) (a : Nat) (ha : a < 2 ^ 64) : mem.permits acc a = true := by
  have : a < 18446744073709551616 := ha
  cases acc <;>
    simp [Memory.permits, mem, allRegion, Silmaril.Process.Region.Contains,
      Silmaril.Process.Permissions.allows, this]

theorem permitted (acc) (a n : Nat) (h : a + n < 2 ^ 64) : mem.Permitted acc a n := by
  simp only [Memory.Permitted, Memory.checkSpan_iff]
  exact ⟨by simp only [addressLimit]; omega, by simp only [addressLimit]; omega,
    fun i _ => permits_all acc _ (by omega)⟩

theorem code_get (i : Nat) (hi : i < code.length) :
    mem.bytes.get? (0x401370 + i) = some Ladder.LeafArith.code[i] :=
  Memory.install_get _ _ _ _ hi

theorem ret_get (i : Nat) (hi : i < retEnc.length) :
    mem.bytes.get? (0x8ff8 + i) = some retEnc[i] := by
  simp only [retEnc, Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
    List.length_nil] at hi
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by omega)]
  exact Memory.install_get _ _ _ _ (by simp [retEnc]; omega)

theorem code_length : code.length = 181 := by decide +kernel

theorem loaded : Silmaril.X86.Ext.Loaded mem base code :=
  Memory.readWith_eq _ _ _ code
    (permitted _ _ _ (by rw [show base.toNat = 0x401370 from rfl, code_length]; omega)) code_get

theorem ret_read : mem.readBytes 0x8ff8 8 = some retEnc :=
  Memory.readWith_eq _ _ _ retEnc (permitted _ _ _ (by decide)) ret_get

theorem retOf_st (off : Nat) (x y z : Word) :
    FnContract.retOf (st off x y z).core (st off x y z).memory = retAt := by
  simp only [FnContract.retOf]
  rw [show ((st off x y z).core.read .rsp).toNat = 0x8ff8 from rfl,
    show (st off x y z).memory = mem from rfl, ret_read]
  decide

theorem placed (off len : Nat) (x y z : Word) : Placed (region off len) (ffiSt off x y z) := by
  refine ⟨loaded, rfl, (fun _ h => nomatch h), fun o ho => ?_⟩
  change o < code.length at ho
  rw [code_length] at ho
  show FnContract.retOf (st off x y z).core (st off x y z).memory ≠ _
  rw [retOf_st]
  change retAt ≠ base + BitVec.ofNat 64 o
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show retAt.toNat = 0x401000 from rfl,
    show base.toNat = 0x401370 from rfl] at this
  omega

theorem stack (p : Proto) (hp : p.signature.arguments.length ≤ 6) (off len : Nat) (x y z : Word) :
    Stack sysvInt p (region off len) 0 (fun _ => False) (ffiSt off x y z) := by
  have ha : sysvInt.argArea p = 0 := by
    show 8 * (p.signature.arguments.length - 6) = 0
    omega
  have hsp : sp (ffiSt off x y z) = 0x8ff8 := rfl
  refine ⟨by omega, ?_, ?_, ?_, ?_, (fun _ h => nomatch h), ?_, (fun _ h => nomatch h),
    (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
    (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
    (fun _ h => nomatch h)⟩
  · rw [ha, hsp]; decide
  · rw [ha, hsp]; exact permitted _ _ _ (by decide)
  · rw [ha, hsp]; exact permitted _ _ _ (by decide)
  · right
    rw [ha, hsp]
    show 0x8ff8 - 0 + (0 + 8 + 0) ≤ base.toNat
    decide
  · intro r hr
    rw [ha, hsp]
    simp only [region, image, List.mem_cons, List.not_mem_nil, or_false] at hr
    right
    rcases hr with rfl | rfl | rfl | rfl <;> decide


theorem clamp_entry : sysvInt.conv.Entry clampProto clampArgs (ffiSt 0x30 5 0 3) := by
  refine ⟨retAt, rfl, ⟨⟨rfl, _, rfl, (chunk32_iff _ .rdi _).2 rfl⟩,
    ⟨rfl, _, rfl, (chunk32_iff _ .rsi _).2 rfl⟩, ⟨rfl, _, rfl, (chunk32_iff _ .rdx _).2 rfl⟩,
    trivial⟩, ?_, ?_, ret_read, rfl, rfl, rfl, fun _ h => nomatch h⟩
  · change ((0x8ff8 : Word).toNat + 8) % 16 = 0
    decide
  · change (0x8ff8 : Word).toNat + 8 + alignUp (8 * (3 - 6)) 16 ≤ 2 ^ 64
    decide


theorem sat_entry : sysvInt.conv.Entry satProto satArgs (ffiSt 0x90 0xfffffff0 0x20 0) := by
  refine ⟨retAt, rfl, ⟨⟨rfl, _, rfl, (chunk32_iff _ .rdi _).2 rfl⟩,
    ⟨rfl, _, rfl, (chunk32_iff _ .rsi _).2 rfl⟩, trivial⟩, ?_, ?_, ret_read, rfl, rfl, rfl,
    fun _ h => nomatch h⟩
  · change ((0x8ff8 : Word).toNat + 8) % 16 = 0
    decide
  · change (0x8ff8 : Word).toNat + 8 + alignUp (8 * (2 - 6)) 16 ≤ 2 ^ 64
    decide

/-- The arguments `(x, y, z)` in `rdi`, `rsi`, `rdx`, zero-extended. -/
abbrev wide (x : BitVec 32) : Word := x.setWidth 64

theorem low32 (x : BitVec 32) : (wide x).setWidth 32 = x := by
  simp [wide]

/-- **Every** call `clamp_i32(x, lo, hi)` has an admitted entry state. -/
theorem clamp_entry_of (x lo hi : BitVec 32) :
    sysvInt.conv.Entry clampProto (.cons x (.cons lo (.cons hi .nil)))
      (ffiSt 0x30 (wide x) (wide lo) (wide hi)) := by
  refine ⟨retAt, rfl, ⟨⟨rfl, _, rfl, (chunk32_iff _ .rdi _).2 (low32 x)⟩,
    ⟨rfl, _, rfl, (chunk32_iff _ .rsi _).2 (low32 lo)⟩,
    ⟨rfl, _, rfl, (chunk32_iff _ .rdx _).2 (low32 hi)⟩,
    trivial⟩, ?_, ?_, ret_read, rfl, rfl, rfl, fun _ h => nomatch h⟩
  · change ((0x8ff8 : Word).toNat + 8) % 16 = 0
    decide
  · change (0x8ff8 : Word).toNat + 8 + alignUp (8 * (3 - 6)) 16 ≤ 2 ^ 64
    decide

/-- **Every** call `sat_add_u32(x, y)` has an admitted entry state. -/
theorem sat_entry_of (x y : BitVec 32) :
    sysvInt.conv.Entry satProto (.cons x (.cons y .nil)) (ffiSt 0x90 (wide x) (wide y) 0) := by
  refine ⟨retAt, rfl, ⟨⟨rfl, _, rfl, (chunk32_iff _ .rdi _).2 (low32 x)⟩,
    ⟨rfl, _, rfl, (chunk32_iff _ .rsi _).2 (low32 y)⟩, trivial⟩, ?_, ?_, ret_read, rfl, rfl, rfl,
    fun _ h => nomatch h⟩
  · change ((0x8ff8 : Word).toNat + 8) % 16 = 0
    decide
  · change (0x8ff8 : Word).toNat + 8 + alignUp (8 * (2 - 6)) 16 ≤ 2 ^ 64
    decide

/-! ## First-return contracts -/

theorem clamp_strict :
    (clampSpec'.restrict (FnContract.RetOutside Open.isa base code.length)).Strict Open.isa :=
  BlockCert.FunCert.strict (F := clampCert) clampSpec' (entry := ⟨0x30, clampL30⟩)
    (by simp [clampCert]) clamp_i32_checked clamp_i32_vc fun _ hab he => ⟨he.1, he.2, rfl, hab⟩

theorem sat_strict :
    (satSpec.restrict (FnContract.RetOutside Open.isa base code.length)).Strict Open.isa :=
  BlockCert.FunCert.strict (F := satCert) satSpec (entry := ⟨0x90, Bir.sat_add_u32.L_401400⟩)
    (by simp [satCert]) sat_add_u32_checked sat_add_u32_vc fun _ hab he => ⟨he.1, he.2, rfl, hab⟩

/-! ## Arguments and results -/

theorem clamp_args {x lo hi : BitVec 32} {s : Ffi.State}
    (entry : sysvInt.conv.Entry clampProto (.cons x (.cons lo (.cons hi .nil))) s) :
    r32 .rdi s.machine = x ∧ r32 .rsi s.machine = lo ∧ r32 .rdx s.machine = hi := by
  obtain ⟨exit, e⟩ := entry
  obtain ⟨⟨-, b0, e0, c0⟩, ⟨-, b1, e1, c1⟩, ⟨-, b2, e2, c2⟩, -⟩ := e.argumentsAt
  subst e0 e1 e2
  exact ⟨(chunk32_iff _ .rdi _).1 c0, (chunk32_iff _ .rsi _).1 c1, (chunk32_iff _ .rdx _).1 c2⟩

theorem sat_args {a b : BitVec 32} {s : Ffi.State}
    (entry : sysvInt.conv.Entry satProto (.cons a (.cons b .nil)) s) :
    r32 .rdi s.machine = a ∧ r32 .rsi s.machine = b := by
  obtain ⟨exit, e⟩ := entry
  obtain ⟨⟨-, b0, e0, c0⟩, ⟨-, b1, e1, c1⟩, -⟩ := e.argumentsAt
  subst e0 e1
  exact ⟨(chunk32_iff _ .rdi _).1 c0, (chunk32_iff _ .rsi _).1 c1⟩

/-- No open-machine run writes the FS base (`Open.step_fsBase`). -/
theorem fs_of_runs {P : MState → Prop} {m t : MState} (r : FnContract.RunsIn Open.isa P m t) :
    t.core.fsBase = m.core.fsBase := by
  induction r with
  | refl => rfl
  | step _ hs _ ih => exact ih.trans (Silmaril.X86.Open.step_fsBase hs)

theorem writesWithin_mono {m m' : Memory} {P Q : Nat → Prop} (h : m.WritesWithin m' P)
    (hPQ : ∀ x, P x → Q x) : m.WritesWithin m' Q :=
  ⟨h.1, fun x hx => h.2 x fun hp => hx (hPQ x hp)⟩

/-! ## The rows -/

theorem clamp_declared : Declares sysvInt hdr "clamp_i32" clampProto :=
  ⟨_, (by decide +kernel : hdr.proto? "clamp_i32" =
    some ⟨.int .int .signed, [.int .int .signed, .int .int .signed, .int .int .signed], false⟩), rfl⟩

theorem sat_declared : Declares sysvInt hdr "sat_add_u32" satProto :=
  ⟨_, (by decide +kernel : hdr.proto? "sat_add_u32" =
    some ⟨.typedef "u32" (.int .int .unsigned),
      [.typedef "u32" (.int .int .unsigned), .typedef "u32" (.int .int .unsigned)], false⟩), rfl⟩

theorem clamp_conforms (mode : Mode) :
    Conforms sysvInt (Mach.ofInt Open.isa) mode hdr "clamp_i32" clampProto clampCode 0 clampS := by
  refine conforms_of_strict clamp_strict clamp_declared (by decide +kernel)
    ⟨clampArgs, ffiSt 0x30 5 0 3, ⟨fun _ _ => trivial, clamp_entry, trivial, placed _ _ _ _ _, stack _ (by decide) _ _ _ _ _, rfl⟩,
      trivial⟩
    (fun a _ _ _ => match a with
      | .cons x (.cons lo (.cons hi .nil)) => ⟨ffiSt 0x30 (wide x) (wide lo) (wide hi),
          ⟨fun _ _ => trivial, clamp_entry_of x lo hi, trivial, placed _ _ _ _ _, stack _ (by decide) _ _ _ _ _, rfl⟩,
          trivial, fun _ => Iff.rfl, fun _ h => h.elim⟩)
    (fun _ _ ad => abiEntry_of_entry ad.entry)
    (fun _ _ _ ad _ hx => hx ▸ ⟨⟨ad.placed.loaded, ad.placed.pc⟩, ad.placed.retOutside⟩) ?_
  intro a s x t ad _ hx fr res
  subst hx
  refine ⟨return_of_result (fun _ => rfl) (fun _ => rfl) ad.entry res, ?_,
    writesWithin_mono res.frame (fun _ h => nomatch h), fs_of_runs fr.1⟩
  match a, ad with
  | .cons x (.cons lo (.cons hi .nil)), ad =>
    obtain ⟨hx, hl, hh⟩ := clamp_args ad.entry
    have hrax : (t.core.read .rax).setWidth 32 = clampSpec x lo hi := by
      rw [show t.core.read .rax = _ from res.post, ← hx, ← hl, ← hh]
      simp
    exact ⟨clampSpec x lo hi, (resultAt_int32 _ _ _ _ _).2 hrax, rfl⟩

theorem sat_conforms (mode : Mode) :
    Conforms sysvInt (Mach.ofInt Open.isa) mode hdr "sat_add_u32" satProto satCode 0 satS := by
  refine conforms_of_strict sat_strict sat_declared (by decide +kernel)
    ⟨satArgs, ffiSt 0x90 0xfffffff0 0x20 0,
      ⟨fun _ _ => trivial, sat_entry, trivial, placed _ _ _ _ _, stack _ (by decide) _ _ _ _ _, rfl⟩, trivial⟩
    (fun a _ _ _ => match a with
      | .cons x (.cons y .nil) => ⟨ffiSt 0x90 (wide x) (wide y) 0,
          ⟨fun _ _ => trivial, sat_entry_of x y, trivial, placed _ _ _ _ _, stack _ (by decide) _ _ _ _ _, rfl⟩,
          trivial, fun _ => Iff.rfl, fun _ h => h.elim⟩)
    (fun _ _ ad => abiEntry_of_entry ad.entry)
    (fun _ _ _ ad _ hx => hx ▸ ⟨⟨ad.placed.loaded, ad.placed.pc⟩, ad.placed.retOutside⟩) ?_
  intro a s x t ad _ hx fr res
  subst hx
  refine ⟨return_of_result (fun _ => rfl) (fun _ => rfl) ad.entry res, ?_,
    writesWithin_mono res.frame (fun _ h => nomatch h), fs_of_runs fr.1⟩
  match a, ad with
  | .cons x (.cons y .nil), ad =>
    obtain ⟨hx, hy⟩ := sat_args ad.entry
    have hrax : (t.core.read .rax).setWidth 32 = satAddSpec x y := by
      rw [show t.core.read .rax = _ from res.post, ← hx, ← hy]
      simp
    exact ⟨satAddSpec x y, (resultAt_uint32 _ _ _ _ _).2 hrax, rfl⟩

/-- **The statement discriminates**: `clamp_i32` does not conform with the spec "returns its
first argument". On `clamp_i32(5, 0, 3)` the one outcome reads back as `3`, not `5`. -/
theorem clamp_rejects_first (mode : Mode) :
    ¬ Conforms sysvInt (Mach.ofInt Open.isa) mode hdr "clamp_i32" clampProto clampCode 0 clampFirstS := by
  intro bad
  have ad : Admit sysvInt (Mach.ofInt Open.isa) clampProto clampCode 0 clampFirstS clampArgs (ffiSt 0x30 5 0 3) :=
    ⟨fun _ _ => trivial, clamp_entry, trivial, placed _ _ _ _ _, stack _ (by decide) _ _ _ _ _, rfl⟩
  have ad' : Admit sysvInt (Mach.ofInt Open.isa) clampProto clampCode 0 clampS clampArgs (ffiSt 0x30 5 0 3) :=
    ⟨fun _ _ => trivial, clamp_entry, trivial, placed _ _ _ _ _, stack _ (by decide) _ _ _ _ _, rfl⟩
  have good := clamp_conforms .total
  obtain ⟨t, ht⟩ := good.progress rfl _ _ ad' trivial _ rfl
  have ht' : t ∈ callModelOf (Mach.ofInt Open.isa) (ffiSt 0x30 5 0 3) := ⟨_, rfl, ht⟩
  obtain ⟨r, hr, hpost⟩ := (good.sound _ _ ad' trivial t ht').result
  obtain ⟨r', hr', hpost'⟩ := (bad.sound _ _ ad trivial t ht').result
  have e1 := (resultAt_int32 _ _ _ _ _).1 hr
  have e2 := (resultAt_int32 _ _ _ _ _).1 hr'
  have h1 : @Eq (BitVec 32) r (clampSpec 5 0 3) := hpost
  have h2 : @Eq (BitVec 32) r' 5 := hpost'
  have : clampSpec 5 0 3 = (5 : BitVec 32) := by rw [← h1, ← h2]; exact e1.symm.trans e2
  exact absurd this (by decide)

theorem coverage_check : coverage.check sysvInt hdr = true := by decide +kernel

theorem header_sat : HeaderSatPartial sysvInt (Mach.ofInt Open.isa) hdr coverage impl := by
  refine ⟨by decide, coverage_check, fun f hf => ?_⟩
  simp only [coverage, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨_, rfl, clamp_conforms .total⟩
  · exact ⟨_, rfl, sat_conforms .total⟩

end Silmaril.Proofs.Machine.Abi.Conformance.LeafArith

end
