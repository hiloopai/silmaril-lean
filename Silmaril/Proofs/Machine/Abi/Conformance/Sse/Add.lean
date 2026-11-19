module

public import Silmaril.Machine.Abi.Conformance.Sse.Add.Defs
public import Silmaril.Machine.Abi.Conformance.Thms
public import Silmaril.Machine.Abi.Conformance.Sse.Thms
public import Silmaril.Proofs.Machine.Abi.Conformance.Sse
public import Silmaril.Proofs.Machine.Abi.Conformance.Basic
public import Silmaril.Proofs.Machine.Abi.Conformance.Negative
public import Silmaril.X86.Spec.Ensures
public import Silmaril.X86.Float.Semantics

/-!
# `double add(double, double)` as `addsd %xmm1, %xmm0; ret` on `Mach.str9L`: proofs

* the witness: the code (padded with ten `int3` in memory, outside the code) at `0x401000`,
  `rsp = 0x8ff8` with the return address `0x402000`, one region mapping every address, the
  arguments in the low halves of vector registers 0 and 1, MXCSR `m` (`st`);
* the run: from every completion of every admitted call, `addsd` (the `floatExt` lane:
  `Str9L.step_of_listed_float`) then `ret` (`Str9D`'s chain: the machine's listing law), the
  second state the first return (`firstReturn`);
* the row (`conforms`) and the negative on `Open` (`open_not`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance.Sse.Add

open Silmaril.X86 (State MState Word Byte Reg XReg)
open Silmaril.Process (Memory Region)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Sse
open Silmaril.Machine.Abi.Conformance.Sse.Add

/-! ## Declaration -/

theorem declared : Declares abi hdr "add" proto := by
  refine ⟨_, (by decide +kernel :
    hdr.proto? "add" = some ⟨.float .double, [.float .double, .float .double], false⟩), ?_⟩
  show lowerScalar Silmaril.Data.Layout.sysvX86_64 hdr.env
    ⟨.float .double, [.float .double, .float .double], false⟩ = .ok proto
  have h : (lowerScalar Silmaril.Data.Layout.sysvX86_64 hdr.env
      ⟨.float .double, [.float .double, .float .double], false⟩).toOption = some proto := by
    decide +kernel
  revert h
  cases lowerScalar Silmaril.Data.Layout.sysvX86_64 hdr.env
    ⟨.float .double, [.float .double, .float .double], false⟩ <;> simp [Except.toOption]

/-! ## The witness -/

def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩

def retAt : Word := 0x402000

def retEnc : List Byte := Silmaril.Machine.LittleEndian.encodeWords [retAt]

/-- The code and ten `int3` bytes after it (outside the code). -/
def padded : List Byte := bytes ++ List.replicate 10 0xCC

def mem : Memory :=
  ⟨[allRegion], Memory.install (Memory.install ∅ 0x8ff8 retEnc) 0x401000 padded⟩

def core0 : State :=
  ⟨fun r => match r with | .rsp => 0x8ff8 | _ => 0, 0x401000,
    ⟨none, none, none, none, none, none⟩, 0⟩

/-- `a` and `b` in the low halves of vector registers 0 and 1. -/
def vecs (a b : BitVec 64) (i : Nat) : BitVec 512 :=
  if i = 0 then a.setWidth 512 else if i = 1 then b.setWidth 512 else 0

/-- **The witness call** `add(a, b)`. -/
def st (a b : BitVec 64) (m : BitVec 32) : Ffi.State :=
  ⟨⟨core0, mem⟩, vecs a b, fun _ => 0, false, true, m, 0x037F, 0⟩

theorem permits_all (acc) (a : Nat) (ha : a < 2 ^ 64) : mem.permits acc a = true := by
  have : a < 18446744073709551616 := ha
  cases acc <;>
    simp [Memory.permits, mem, allRegion, Silmaril.Process.Region.Contains,
      Silmaril.Process.Permissions.allows, this]

theorem permitted (acc) (a n : Nat) (h : a + n < 2 ^ 64) : mem.Permitted acc a n := by
  simp only [Memory.Permitted, Memory.checkSpan_iff]
  exact ⟨by simp only [Silmaril.Process.addressLimit]; omega,
    by simp only [Silmaril.Process.addressLimit]; omega,
    fun i _ => permits_all acc _ (by omega)⟩

theorem padded_length : padded.length = 15 := rfl

theorem loaded_padded : Silmaril.X86.Ext.Loaded mem 0x401000 padded :=
  Memory.readWith_eq _ _ _ padded (permitted _ _ _ (by rw [padded_length]; decide))
    fun i hi => Memory.install_get _ _ _ _ hi

theorem loaded : Silmaril.X86.Ext.Loaded mem code.base bytes := by
  have h := Silmaril.X86.Ext.Loaded.fetchBytes_sub loaded_padded (offset := 0) (len := 5)
    (by decide) (by rw [padded_length]; decide)
  exact h

theorem ret_read : mem.readBytes 0x8ff8 8 = some retEnc := by
  refine Memory.readWith_eq _ _ _ retEnc (permitted _ _ _ (by decide)) fun i hi => ?_
  simp only [retEnc, Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
    List.length_nil] at hi
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by rw [padded_length]; omega)]
  exact Memory.install_get _ _ _ _ (by simp [retEnc]; omega)

theorem retOf_st (a b : BitVec 64) (m : BitVec 32) :
    Silmaril.X86.FnContract.retOf (st a b m).machine.core (st a b m).machine.memory = retAt :=
  Silmaril.X86.FnContract.retOf_of_readBytes ret_read

/-- `sysvScalar`'s plan for `proto`: XMM0 and XMM1 in, XMM0 out, no stack. -/
theorem plan_eq : Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result =
    ⟨[⟨Silmaril.Machine.Abi.SystemV.Scalar.Kind.double.object, [⟨0, 8, .vector 0 0⟩], none⟩,
      ⟨Silmaril.Machine.Abi.SystemV.Scalar.Kind.double.object, [⟨0, 8, .vector 1 0⟩], none⟩],
      .direct [⟨0, 8, .vector 0 0⟩], 0, 16, 0, 2, none⟩ := by decide

theorem argArea_eq : abi.argArea proto = 0 := by decide

theorem low_vecs (v : BitVec 64) : (v.setWidth 512).setWidth 64 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj]

/-- The C arguments `(a, b)`. -/
def args (a b : BitVec 64) : abi.V.Args proto := (a, (b, PUnit.unit))

/-- **Every call `add(a, b)` has an admitted entry state.** -/
theorem entry_st (a b : BitVec 64) (m : BitVec 32) : abi.conv.Entry proto (args a b) (st a b m) := by
  refine ⟨retAt, rfl, ?_, ?_, ?_, ret_read, ?_, rfl, rfl, ?_⟩
  · show Ffi.ArgumentsAt (st a b m) (proto.args.map Silmaril.Machine.Abi.SystemV.Scalar.Arg.spec)
      (args a b) (Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result).arguments
    rw [plan_eq]
    exact ⟨⟨rfl, _, rfl, (vector_chunk_iff _ (by decide) _).2 (low_vecs a)⟩,
      ⟨rfl, _, rfl, (vector_chunk_iff _ (by decide) _).2 (low_vecs b)⟩, trivial⟩
  · show ((0x8ff8 : Word).toNat + 8) %
      (Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result).stackAlign = 0
    rw [plan_eq]; decide
  · show (0x8ff8 : Word).toNat + 8 +
      (Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result).stackSize ≤ 2 ^ 64
    rw [plan_eq]; decide
  · rfl
  · show ∀ count, (Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result).variadicAL =
      some count → _
    rw [plan_eq]
    exact fun _ h => nomatch h

theorem placed (a b : BitVec 64) (m : BitVec 32) : Placed code (st a b m) := by
  refine ⟨loaded, rfl, (fun _ h => nomatch h), fun o ho => ?_⟩
  change o < 5 at ho
  rw [retOf_st]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show retAt.toNat = 0x402000 from rfl,
    show code.base.toNat = 0x401000 from rfl] at this
  omega

theorem stack (a b : BitVec 64) (m : BitVec 32) : Stack abi proto code 0 (fun _ => False) (st a b m) := by
  have hsp : sp (st a b m) = 0x8ff8 := rfl
  have hown : ∀ x, ¬ abi.owned proto (st a b m) x := by
    intro x h
    have h0 : sretBytes proto = 0 := by decide
    simp only [abi, AbiDef.defaultEnv, sysvScalar, h0, Nat.add_zero] at h
    omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, (fun _ h => nomatch h), (fun _ h => nomatch h),
    (fun _ h => nomatch h), (fun x h => absurd h (hown x)), (fun x h => absurd h (hown x)),
    (fun x h => absurd h (hown x)), (fun x h => absurd h (hown x)), (fun x h => absurd h (hown x)),
    (fun x h => absurd h (hown x)), (fun x h => absurd h (hown x))⟩
  · rw [argArea_eq, hsp]; decide
  · rw [argArea_eq, hsp]; exact permitted _ _ _ (by decide)
  · rw [argArea_eq, hsp]; exact permitted _ _ _ (by decide)
  · right
    rw [argArea_eq, hsp]
    decide

/-- **The admitted call `add(a, b)`** on every machine whose states are all live. -/
theorem admit_st {M : Mach} (hl : ∀ x, M.isa.live x) (S : CallSpec abi.V proto)
    (hS : S.objects = fun _ _ _ => False) (a b : BitVec 64) (m : BitVec 32)
    (hm : m &&& 0xffc0 = 0x1F80) :
    Admit abi M proto code 0 S (args a b) (st a b m) := by
  refine ⟨fun x _ => hl x, entry_st a b m, ⟨trivial, hm⟩, placed a b m, ?_, rfl⟩
  rw [hS]
  exact stack a b m

/-! ## What an admitted call fixes -/

/-- An admitted call: its return address, DF clear, x87 mode, the arguments in the low halves of
vector registers 0 and 1, and the default MXCSR control bits. -/
theorem entry_facts {M : Mach} {S : CallSpec abi.V proto} {a : abi.V.Args proto} {s : Ffi.State}
    (ad : Admit abi M proto code 0 S a s) :
    ∃ exit, s.machine.memory.readBytes (s.machine.core.read .rsp).toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [exit]) ∧
      s.direction = false ∧ s.x87Mode = true ∧
      (s.vectors 0).setWidth 64 = a.1 ∧ (s.vectors 1).setWidth 64 = a.2.1 ∧
      s.mxcsr &&& 0xffc0 = 0x1F80 := by
  obtain ⟨exit, e⟩ := ad.entry
  have hargs := e.argumentsAt
  change Ffi.ArgumentsAt s (proto.args.map Silmaril.Machine.Abi.SystemV.Scalar.Arg.spec) a
    (Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result).arguments at hargs
  rw [plan_eq] at hargs
  obtain ⟨⟨-, b0, e0, c0⟩, ⟨-, b1, e1, c1⟩, -⟩ := hargs
  change b0 = Ffi.bytesOfNat a.1.toNat 0 8 at e0
  change b1 = Ffi.bytesOfNat a.2.1.toNat 0 8 at e1
  subst e0 e1
  exact ⟨exit, e.returnAddress, e.direction, e.x87Mode,
    (vector_chunk_iff s (by decide) _).1 c0, (vector_chunk_iff s (by decide) _).1 c1, ad.env.2⟩

/-! ## The run -/

/-- `addsd %xmm1, %xmm0`. -/
abbrev addsd : Silmaril.X86.Float.Instr := .arith .add .double .xmm0 (.reg .xmm1)

/-- The scalar SSE state of a machine state. -/
def fsOf (x : SState) : Silmaril.X86.Float.State := ⟨x.l.core, x.l.x.d.v.g.x.xmm, x.l.mxcsr⟩

/-- The binary64 sum `addsd` computes in the low lane of XMM0. -/
def sumOf (x : SState) : BitVec 64 :=
  (Silmaril.X86.Float.Scalar.binary (fsOf x).mxcsr .double .add
    (Silmaril.X86.Float.lane .double ((fsOf x).readX .xmm0))
    (Silmaril.X86.Float.lane .double ((fsOf x).readX .xmm1))).value

/-- The scalar state after `addsd` with every exception masked. -/
def addT (x : SState) : Silmaril.X86.Float.State :=
  Silmaril.X86.Float.advance addsd
    { (fun u : Silmaril.X86.Float.State => u.writeX .xmm0 (Silmaril.X86.Float.setLane .double
        (u.readX .xmm0) (sumOf x))) (fsOf x) with
      mxcsr := (fsOf x).mxcsr.record (Silmaril.X86.Float.Scalar.binaryDetected (fsOf x).mxcsr
        .double .add (Silmaril.X86.Float.lane .double ((fsOf x).readX .xmm0))
        (Silmaril.X86.Float.lane .double ((fsOf x).readX .xmm1))).all }

theorem exec_addsd (x : SState) (hm : (fsOf x).mxcsr.AllMasked) :
    addsd.exec (fsOf x) x.l.memory = .commit (addT x) x.l.memory := by
  have h1 := Silmaril.X86.Float.exec_arith_binary (op := .add) (a := .add) (p := .double)
    (dst := .xmm0) (src := .reg .xmm1) (s := fsOf x) (memory := x.l.memory)
    (y := Silmaril.X86.Float.lane .double ((fsOf x).readX .xmm1)) rfl rfl
  rw [h1, Silmaril.X86.Float.finish_of_allMasked _ _ _ hm]
  rfl

/-- The machine state after `addsd`. -/
def x1 (x : SState) : SState :=
  { x with l := ⟨⟨⟨⟨{ x.l.x.d.v.g with x := ⟨⟨(addT x).core, x.l.memory⟩, (addT x).xmm⟩ },
    x.l.x.d.v.hi⟩, x.l.x.d.df⟩, x.l.x.fpu⟩, (addT x).mxcsr⟩ }

theorem step_addsd (x : SState) (hl : Silmaril.X86.Ext.Loaded x.l.memory code.base bytes)
    (hrip : x.l.core.rip = code.base) (hm : x.l.mxcsr.AllMasked) :
    mach.isa.step x = some (x1 x) := by
  rw [Sse.str9L_step x (Silmaril.X86.Str9L.towerMissing_of_listed_lane (o := 0) (l := 4) hl
    (by rw [hrip]; rfl) (by decide) (by decide) (by decide) Silmaril.X86.Str9L.laneBad_addsd.1)]
  show (Silmaril.X86.Str9L.step _ (Silmaril.X86.Features.floatExt :: _) x.l).map _ = _
  rw [Silmaril.X86.Str9L.step_of_listed_float (o := 0) (l := 4) hl
    (by rw [hrip]; rfl) (by decide) (by decide) Silmaril.X86.Str9L.laneBad_addsd.1
    Silmaril.X86.Str9L.laneBad_addsd.2 (by decide) (exec_addsd x hm)]
  rfl

theorem x1_rip (x : SState) : (x1 x).l.core.rip = x.l.core.rip + 4 := rfl

/-- `ret`, as `Str9D` decodes it. -/
abbrev retI : Silmaril.X86.Str9FsX.Instr :=
  .base (.str9 (.ext9 (.ext8 (.base .ret))))

/-- The core after `ret` to `exit`. -/
def retCore (c : State) (exit : Word) : State :=
  { c.write .rsp (c.read .rsp + 8#64) with rip := exit }

theorem retCore_read (c : State) (exit : Word) (r : Reg) :
    (retCore c exit).read r = (c.write .rsp (c.read .rsp + 8#64)).read r := rfl

/-- The machine state after `ret` to `exit`. -/
def x2 (x : SState) (exit : Word) : SState :=
  mach.isa.upd (x1 x) (retCore (x1 x).l.core exit) x.l.memory

theorem step_ret (x : SState) (exit : Word) (hl : Silmaril.X86.Ext.Loaded x.l.memory code.base bytes)
    (hrip : x.l.core.rip = code.base)
    (hra : x.l.memory.readBytes (x.l.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit])) :
    mach.isa.step (x1 x) = some (x2 x exit) := by
  have hw : Silmaril.X86.Spec.WordAt x.l.memory ((x1 x).l.core.read .rsp) exit :=
    ⟨_, hra, by simp⟩
  refine mach.isa.step_of (s := x1 x) (o := 4) (l := 1) (i := retI) trivial hl
    (by show (x1 x).l.core.rip = _; rw [x1_rip, hrip]; rfl) (by decide) (by decide) ?_ trivial
  exact Silmaril.X86.Spec.exec_ret_eq hw

/-! ## Every completion of every admitted call -/

section Completion

variable {S : CallSpec abi.V proto} {a : abi.V.Args proto} {s : Ffi.State} {x : SState}

theorem fills_m (hx : mach.Fills s x) : x.l.x.d.v.g.x.m = s.machine := hx .machine rfl

theorem fills_core (hx : mach.Fills s x) : x.l.core = s.machine.core := by
  show x.l.x.d.v.g.x.m.core = _; rw [fills_m hx]

theorem fills_mem (hx : mach.Fills s x) : x.l.memory = s.machine.memory := by
  show x.l.x.d.v.g.x.m.memory = _; rw [fills_m hx]

/-- **The default control bits mask every exception**, whatever the status flags. -/
theorem allMasked_of_control {m : BitVec 32} (h : m &&& 0xffc0 = 0x1F80) :
    (⟨m⟩ : Silmaril.X86.Float.MXCSR).AllMasked := by
  have bit : ∀ k, 7 ≤ k → k ≤ 12 → m.getLsbD k = true := by
    intro k h1 h2
    have e := congrArg (fun v : BitVec 32 => v.getLsbD k) h
    simp only [BitVec.getLsbD_and] at e
    rcases (by omega : k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    · revert e; generalize m.getLsbD _ = b; cases b <;> decide
  simp only [Silmaril.X86.Float.MXCSR.AllMasked, Silmaril.X86.Float.MXCSR.im,
    Silmaril.X86.Float.MXCSR.dm, Silmaril.X86.Float.MXCSR.zm, Silmaril.X86.Float.MXCSR.om,
    Silmaril.X86.Float.MXCSR.um, Silmaril.X86.Float.MXCSR.pm, bit 7 (by omega) (by omega),
    bit 8 (by omega) (by omega), bit 9 (by omega) (by omega), bit 10 (by omega) (by omega),
    bit 11 (by omega) (by omega), bit 12 (by omega) (by omega), Bool.and_self]

/-- **`sum` reads only the MXCSR control bits** (DAZ, FTZ with UM, RC). -/
theorem sum_mask (m : BitVec 32) (a b : BitVec 64) : sum m a b = sum (m &&& 0xffc0) a b := by
  have keep : ∀ k, (0xffc0 : BitVec 32).getLsbD k = true → (m &&& 0xffc0).getLsbD k = m.getLsbD k :=
    fun k hk => by rw [BitVec.getLsbD_and, hk, Bool.and_true]
  have h6 := keep 6 (by decide)
  have h11 := keep 11 (by decide)
  have h15 := keep 15 (by decide)
  have hrc : (m &&& 0xffc0).extractLsb' 13 2 = m.extractLsb' 13 2 := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [keep 13 (by decide)]
    · rw [keep 14 (by decide)]
  simp only [sum, Silmaril.X86.Float.Scalar.binary, Silmaril.X86.Float.MXCSR.profile,
    Silmaril.X86.Float.MXCSR.control, Silmaril.X86.Float.MXCSR.rounding,
    Silmaril.X86.Float.MXCSR.daz, Silmaril.X86.Float.MXCSR.fz, Silmaril.X86.Float.MXCSR.um,
    Silmaril.X86.Float.MXCSR.rc, h6, h11, h15, hrc]
  rfl

theorem sum_control {m m' : BitVec 32} (h : m &&& 0xffc0 = m' &&& 0xffc0) (a b : BitVec 64) :
    sum m a b = sum m' a b := by
  rw [sum_mask m, sum_mask m', h]

theorem masked (ad : Admit abi mach proto code 0 S a s) (hx : mach.Fills s x) :
    x.l.mxcsr.AllMasked := by
  obtain ⟨_, _, _, _, _, _, hm⟩ := entry_facts ad
  rw [Sse.fills_mxcsr hx]
  exact allMasked_of_control hm

theorem not_returned_of_rip {y : SState} (hy : y.l.core.rip = code.base + BitVec.ofNat 64 4 ∨
      y.l.core.rip = code.base + BitVec.ofNat 64 0)
    (ad : Admit abi mach proto code 0 S a s) (hx : mach.Fills s x) :
    ¬ Silmaril.X86.FnContract.Returned mach.isa x y := by
  intro h
  have hr : y.l.core.rip = Silmaril.X86.FnContract.retOf s.machine.core s.machine.memory := by
    have := h.1
    simp only [mach, Mach.str9L, Sse.isa] at this
    rw [this, fills_core hx, fills_mem hx]
  rcases hy with e | e
  · exact ad.placed.retOutside 4 (by decide) (hr.symm.trans e)
  · exact ad.placed.retOutside 0 (by decide) (hr.symm.trans e)

/-- **The first return**: `addsd` then `ret`, from every completion of every admitted call. -/
theorem firstReturn (ad : Admit abi mach proto code 0 S a s) (hx : mach.Fills s x) {exit : Word}
    (hra : s.machine.memory.readBytes (s.machine.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit])) :
    Silmaril.X86.FnContract.FirstReturn mach.isa x (x2 x exit) := by
  have hl : Silmaril.X86.Ext.Loaded x.l.memory code.base bytes := by
    rw [fills_mem hx]; exact ad.placed.loaded
  have hrip : x.l.core.rip = code.base := by
    rw [fills_core hx]; exact ad.placed.pc
  have hra' : x.l.memory.readBytes (x.l.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit]) := by
    rw [fills_mem hx, fills_core hx]; exact hra
  refine ⟨.step (not_returned_of_rip (.inr hrip) ad hx) (step_addsd x hl hrip (masked ad hx))
    (.step (not_returned_of_rip (.inl (by rw [x1_rip, hrip]; rfl)) ad hx)
      (step_ret x exit hl hrip hra') (.refl _)), ?_, ?_⟩
  · show exit = Silmaril.X86.FnContract.retOf x.l.core x.l.memory
    exact (Silmaril.X86.FnContract.retOf_of_readBytes hra').symm
  · show (retCore (x1 x).l.core exit).read .rsp = x.l.core.read .rsp + 8#64
    rw [retCore_read, Silmaril.X86.State.read_write_same]
    rfl

/-- MXCSR's control bits are kept when status flags are ORed in. -/
theorem record_control (m : Silmaril.X86.Float.MXCSR) (e : Silmaril.X86.Float.Exceptions) :
    (m.record e).bits &&& 0xffc0 = m.bits &&& 0xffc0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Silmaril.X86.Float.MXCSR.record, BitVec.getLsbD_and, BitVec.getLsbD_or]
  by_cases h : 6 ≤ i
  · rw [Silmaril.X86.Float.Exceptions.toBits_getLsbD_of_ge e h, Bool.or_false]
  · have : (0xffc0 : BitVec 32).getLsbD i = false := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [this, Bool.and_false, Bool.and_false]

theorem low_setLane (v : BitVec 128) (r : BitVec 64) :
    (Silmaril.X86.Float.setLane .double v r).setWidth 64 = r := by
  show ((v.extractLsb' 64 64 ++ r : BitVec 128)).setWidth 64 = r
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  simp [hj]

theorem lane_eq (v : BitVec 128) : Silmaril.X86.Float.lane .double v = v.setWidth 64 := by
  show v.extractLsb' 0 64 = v.setWidth 64
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  simp [hj]

/-- **A conforming return** from every completion. -/
theorem good (ad : Admit abi mach proto code 0 S a s) (hx : mach.Fills s x) {exit : Word}
    (hra : s.machine.memory.readBytes (s.machine.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit]))
    (hpost : ∀ t, S.post a s (sum s.mxcsr a.1 a.2.1) t) :
    Good abi proto 0 S a s (mach.store s (x2 x exit)) := by
  obtain ⟨_, _, hdir, hmode, ha0, ha1, -⟩ := entry_facts ad
  have hcore := fills_core hx
  refine ⟨⟨exit, hra, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩, ⟨_, ?_, hpost _⟩, ?_, ?_⟩
  · rfl
  · show (retCore (x1 x).l.core exit).read .rsp = s.machine.core.read .rsp + 8
    rw [retCore_read, Silmaril.X86.State.read_write_same, ← hcore]
    rfl
  · intro r hr
    have hne : r ≠ .rsp := by
      simp only [Silmaril.X86.sysv64, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    show (retCore (x1 x).l.core exit).read r = s.machine.core.read r
    rw [retCore_read, Silmaril.X86.State.read_write_other _ _ _ _ hne, ← hcore]
    rfl
  · show x.l.x.d.df = false
    have hd : x.l.x.d.df = s.direction := hx .direction rfl
    rw [hd, hdir]
  · exact hmode
  · show (x.l.mxcsr.record _).bits &&& 0xffc0 = s.mxcsr &&& 0xffc0
    have hm : x.l.mxcsr.bits = s.mxcsr := hx .mxcsr rfl
    rw [record_control, hm]
  · exact (hx .x87Control rfl : x.l.x.fpu.control = s.x87Control)
  · refine (resultAt_store_double (F := Silmaril.X86.Features.FeatureSet.baseline64)
      (exts := Silmaril.X86.Features.sseExts) [.scalar .double, .scalar .double] (by decide) s
      (x2 x exit) _).2 ?_
    show (Silmaril.X86.Float.setLane .double (x.l.xmm .xmm0) (sumOf x)).setWidth 64 = _
    rw [low_setLane]
    show (Silmaril.X86.Float.Scalar.binary x.l.mxcsr .double .add
      (Silmaril.X86.Float.lane .double (x.l.xmm .xmm0))
      (Silmaril.X86.Float.lane .double (x.l.xmm .xmm1))).value = _
    rw [lane_eq, lane_eq, Sse.fills_mxcsr hx,
      show x.l.xmm .xmm0 = x.l.xmm (Silmaril.X86.Sep.Plan.xregOfIdx 0) from rfl,
      show x.l.xmm .xmm1 = x.l.xmm (Silmaril.X86.Sep.Plan.xregOfIdx 1) from rfl]
    obtain ⟨exit', e⟩ := ad.entry
    have hargs := e.argumentsAt
    change Ffi.ArgumentsAt s (proto.args.map Silmaril.Machine.Abi.SystemV.Scalar.Arg.spec) a
      (Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result).arguments at hargs
    rw [plan_eq] at hargs
    obtain ⟨⟨-, b0, e0, c0⟩, ⟨-, b1, e1, c1⟩, -⟩ := hargs
    change b0 = Ffi.bytesOfNat a.1.toNat 0 8 at e0
    change b1 = Ffi.bytesOfNat a.2.1.toNat 0 8 at e1
    subst e0 e1
    rw [Sse.entry_xmm (by decide) c0 hx, Sse.entry_xmm (by decide) c1 hx]
    rfl
  · show s.machine.memory.WritesWithin x.l.memory _
    rw [fills_mem hx]
    exact Memory.WritesWithin.refl _ _
  · show (retCore (x1 x).l.core exit).fsBase = s.machine.core.fsBase
    rw [← hcore]; rfl

end Completion

/-! ## The row -/

/-- **`addsd %xmm1, %xmm0; ret` conforms to the default-environment subset of `sysvScalar` as
`double add(double, double)` on `Mach.str9L`**, in total mode, with the result `sum`. -/
theorem conforms : Conforms abi mach .total hdr "add" proto code 0 spec := by
  refine ⟨declared, by decide,
    ⟨args 0 0, st 0 0 0x1F80, admit_st (fun _ => trivial) spec rfl 0 0 _ (by decide), trivial⟩,
    fun a _ _ _ => ?_, fun a s ad _ x hx => ?_, fun _ a s ad _ x hx => ?_, fun a s ad _ t ht => ?_⟩
  · obtain ⟨a0, a1, ⟨⟩⟩ := a
    exact ⟨st a0 a1 0x1F80, admit_st (fun _ => trivial) spec rfl a0 a1 _ (by decide), trivial, fun _ => Iff.rfl,
      fun _ h => h.elim⟩
  · obtain ⟨exit, hra, -⟩ := entry_facts ad
    exact Silmaril.Proofs.Machine.Abi.Conformance.noStuck_of_firstReturn (firstReturn ad hx hra)
  · obtain ⟨exit, hra, -⟩ := entry_facts ad
    exact ⟨_, _, firstReturn ad hx hra, rfl⟩
  · obtain ⟨x, hx, y, fr, rfl⟩ := ht
    obtain ⟨exit, hra, -⟩ := entry_facts ad
    rw [Silmaril.X86.FnContract.firstReturn_unique fr (firstReturn ad hx hra)]
    exact good ad hx hra (fun _ => rfl)

/-! ## The negative: `Open` has no `addsd` -/

theorem open_stuck (a b : BitVec 64) (m : BitVec 32) :
    Silmaril.X86.Open.step (st a b m).machine = none := by
  have hw : Silmaril.X86.fetchWindow mem Silmaril.X86.maxInstrLength 0x401000 =
      (padded.drop 0).take 15 :=
    Silmaril.Proofs.Machine.Abi.Conformance.Negative.window_of_loaded loaded_padded 15 0
      (by rw [padded_length])
  have hext : Silmaril.X86.Ext.fetch mem 0x401000 = .undecodable := by
    unfold Silmaril.X86.Ext.fetch
    rw [hw]
    have h1 : Silmaril.X86.Ext.decode ((padded.drop 0).take 15) = none := by decide +kernel
    rw [h1]
    have h2 : (match Silmaril.X86.Ext.parseRaw ((padded.drop 0).take 15) with
        | .eof => false | _ => true) = true := by decide +kernel
    simp only
    revert h2
    cases Silmaril.X86.Ext.parseRaw ((padded.drop 0).take 15) <;> simp
  have h8 : Silmaril.X86.Ext8.fetch mem 0x401000 = .inl .undecodable := by
    unfold Silmaril.X86.Ext8.fetch
    rw [hext]
    simp only
    rw [hw]
    have h3 : Silmaril.X86.Ext8.decodeNew ((padded.drop 0).take 15) = none := by decide +kernel
    rw [h3]
  unfold Silmaril.X86.Open.step
  rw [show (st a b m).machine.memory = mem from rfl,
    show (st a b m).machine.core.rip.toNat = 0x401000 from rfl, h8]

/-- **The same bytes do not conform on `Open`**, in either mode, for the same spec: the
admitted call `add(0, 0)` is stuck at `addsd`. -/
theorem open_not (mode : Mode) :
    ¬ Conforms abi (Mach.ofInt Silmaril.X86.Open.isa) mode hdr "add" proto code 0 spec := by
  intro h
  have ad := admit_st (M := Mach.ofInt Silmaril.X86.Open.isa) (fun _ => trivial) spec rfl 0 0 0x1F80 (by decide)
  have := Silmaril.Machine.Abi.Conformance.Conforms.steps h (by decide) ad trivial
    (x := (st 0 0 0x1F80).machine) rfl
  change (Silmaril.X86.Open.step (st 0 0 0x1F80).machine).isSome = true at this
  rw [open_stuck] at this
  cases this

end Silmaril.Proofs.Machine.Abi.Conformance.Sse.Add

end
