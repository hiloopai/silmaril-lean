module

public import Silmaril.X86.Sep.Plan.Defs
public import Silmaril.X86.Sep.BI.Defs
public import Silmaril.X86.Sep.Thms
/-!
# Proofs: placement assertions agree with the ABI model's `Ffi` reading of a plan

Behind `Silmaril/Machine/X86/Sep/Plan/Thms.lean`. Imports only headers.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep.Plan

open Silmaril.X86 (Reg XReg Word Byte MState)
open Silmaril.X86.Sse9 (Xmm XState)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Xmm
open Silmaril.X86.Sep.Plan
open Silmaril.Machine.SystemV.Abi (Chunk Argument CallPlan Location)
open Silmaril.Machine.SystemV.Abi.Ffi (ChunksAt locationBytes bytesOfNat StoredAt)

/-! ## Bytes -/

theorem extractLsb'_eq_ofNat {w : Nat} (v : BitVec w) (k : Nat) :
    v.extractLsb' k 8 = BitVec.ofNat 8 (v.toNat / 2 ^ k) := by
  simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

/-- `Ffi.bytesOfNat` is `byteSlice`, as `Sep` bytes. -/
theorem toSepBytes_bytesOfNat {w : Nat} (v : BitVec w) (off n : Nat) :
    toSepBytes (bytesOfNat v.toNat off n) = byteSlice v off n := by
  simp only [toSepBytes, bytesOfNat, byteSlice, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, extractLsb'_eq_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp

/-- Truncating above the slice does not change it. -/
theorem byteSlice_setWidth {w m : Nat} (v : BitVec w) {off n : Nat} (h : 8 * (off + n) ≤ m) :
    byteSlice (v.setWidth m) off n = byteSlice v off n := by
  simp only [byteSlice]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * (off + j) + i < m := by omega
  simp [this]

theorem toSepBytes_length (bs : Silmaril.Cerberus.NativeTypes.Bytes) :
    (toSepBytes bs).length = bs.length := by
  simp [toSepBytes]

theorem toSepBytes_inj {a b : Silmaril.Cerberus.NativeTypes.Bytes} :
    toSepBytes a = toSepBytes b ↔ a = b := by
  constructor
  · intro h
    refine List.map_injective_iff.mpr ?_ h
    intro x y e
    have e' := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at e'
    have hx := x.toNat_lt
    have hy := y.toNat_lt
    apply UInt8.toNat_inj.mp
    rw [Nat.mod_eq_of_lt (by simpa using hx), Nat.mod_eq_of_lt (by simpa using hy)] at e'
    exact e'
  · rintro rfl; rfl

theorem slice_toSepBytes (bs : Silmaril.Cerberus.NativeTypes.Bytes) (off n : Nat) :
    slice (toSepBytes bs) off n = toSepBytes ((bs.drop off).take n) := by
  simp [slice, toSepBytes, List.map_drop, List.map_take]

theorem xregOfIdx_toNat {i : Nat} (hi : i < 16) : (xregOfIdx i).toBitVec.toNat = i := by
  simp [xregOfIdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

/-! ## One chunk against `Ffi.locationBytes` -/

/-- **One chunk.** On the `Ffi.State` projection, a chunk's `ChunkVal` is `modelled` plus
`Ffi.ChunksAt`'s per-chunk condition. -/
theorem chunkVal_ffi (s : Silmaril.Machine.SystemV.Abi.Ffi.State)
    (bs : Silmaril.Cerberus.NativeTypes.Bytes) (c : Chunk) :
    ChunkVal (fun r => s.machine.core.read r) (ffiXState s).xmm (toSepBytes bs) c ↔
      modelled c = true ∧ c.offset + c.bytes ≤ bs.length ∧
        locationBytes s c.location c.bytes = some ((bs.drop c.offset).take c.bytes) := by
  obtain ⟨off, n, loc⟩ := c
  simp only [ChunkVal, toSepBytes_length, slice_toSepBytes]
  cases loc with
  | gp r =>
    simp only [modelled, decide_eq_true_eq, locationBytes]
    constructor
    · rintro ⟨hn, hl, he⟩
      refine ⟨hn, hl, ?_⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hn), Option.some.injEq, ← toSepBytes_inj,
        toSepBytes_bytesOfNat,
        byteSlice_setWidth _ (by omega)]
      exact he
    · rintro ⟨hn, hl, he⟩
      refine ⟨hn, hl, ?_⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hn), Option.some.injEq, ← toSepBytes_inj,
        toSepBytes_bytesOfNat,
        byteSlice_setWidth _ (by omega)] at he
      exact he
  | vector i o =>
    simp only [modelled, Bool.and_eq_true, decide_eq_true_eq, locationBytes]
    constructor
    · rintro ⟨⟨hi, ho⟩, hl, he⟩
      refine ⟨⟨hi, ho⟩, hl, ?_⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Option.some.injEq, ← toSepBytes_inj,
        toSepBytes_bytesOfNat]
      rw [← he]
      simp only [ffiXState, xregOfIdx_toNat hi]
      exact (byteSlice_setWidth _ (by omega)).symm
    · rintro ⟨⟨hi, ho⟩, hl, he⟩
      refine ⟨⟨hi, ho⟩, hl, ?_⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Option.some.injEq, ← toSepBytes_inj,
        toSepBytes_bytesOfNat] at he
      rw [← he]
      simp only [ffiXState, xregOfIdx_toNat hi]
      exact byteSlice_setWidth _ (by omega)
  | x87 i =>
    simp [modelled]

/-! ## Chunk lists against `Ffi.ChunksAt` -/

theorem mem_gpRegs {cs : List Chunk} {c : Chunk} {r : Reg} (hc : c ∈ cs)
    (hl : c.location = .gp r) : r ∈ gpRegs cs :=
  List.mem_filterMap.mpr ⟨c, hc, by simp [hl]⟩

theorem mem_xRegs {cs : List Chunk} {c : Chunk} {i o : Nat} (hc : c ∈ cs)
    (hl : c.location = .vector i o) : xregOfIdx i ∈ xRegs cs :=
  List.mem_filterMap.mpr ⟨c, hc, by simp [hl]⟩

/-- On owned registers, the values of a `chunksPt` witness are the machine's. -/
theorem chunkVal_congr {g g' : Reg → Word} {v v' : XReg → Silmaril.X86.Sse9.Xmm} {cs : List Chunk}
    (hg : ∀ r ∈ gpRegs cs, g r = g' r) (hv : ∀ x ∈ xRegs cs, v x = v' x)
    {bytes : List Byte} {c : Chunk} (hc : c ∈ cs) :
    ChunkVal g v bytes c ↔ ChunkVal g' v' bytes c := by
  obtain ⟨off, n, loc⟩ := c
  cases loc with
  | gp r => simp only [ChunkVal]; rw [hg r (mem_gpRegs hc rfl)]
  | vector i o => simp only [ChunkVal]; rw [hv _ (mem_xRegs hc rfl)]
  | x87 i => simp only [ChunkVal]

/-- **`chunksPt` holds of the `Ffi.State` projection iff `Ffi.ChunksAt` holds**, for chunks
that this logic models. -/
theorem chunksPt_iff_chunksAt (s : Silmaril.Machine.SystemV.Abi.Ffi.State)
    (bs : Silmaril.Cerberus.NativeTypes.Bytes) (cs : List Chunk) :
    XHolds (chunksPt (toSepBytes bs) cs) (ffiXState s) ↔
      (∀ c ∈ cs, modelled c = true) ∧ ChunksAt s bs cs := by
  constructor
  · rintro ⟨h, ⟨g, v, rfl, hall⟩, hle₁, hle₂⟩
    have hg : ∀ r ∈ gpRegs cs, g r = s.machine.core.read r := by
      intro r hr
      have := hle₁ (.reg r) (.word (g r)) (by simp [regsFrag, hr])
      simp only [ffiXState, toXFrag, toFrag, Option.some.injEq, Val.word.injEq] at this
      exact this.symm
    have hv : ∀ x ∈ xRegs cs, v x = (ffiXState s).xmm x := by
      intro x hx
      have := hle₂ x (v x) (by simp [xmmsMap, hx])
      simp only [toXFrag, XMap.all, Option.some.injEq] at this
      exact this.symm
    have key : ∀ c ∈ cs, modelled c = true ∧ c.offset + c.bytes ≤ bs.length ∧
        locationBytes s c.location c.bytes = some ((bs.drop c.offset).take c.bytes) :=
      fun c hc => (chunkVal_ffi s bs c).mp ((chunkVal_congr hg hv hc).mp (hall c hc))
    exact ⟨fun c hc => (key c hc).1, fun c hc => (key c hc).2⟩
  · rintro ⟨hm, hat⟩
    refine ⟨(regsFrag (gpRegs cs) (fun r => s.machine.core.read r),
      xmmsMap (xRegs cs) (ffiXState s).xmm), ⟨_, _, rfl, fun c hc =>
        (chunkVal_ffi s bs c).mpr ⟨hm c hc, hat c hc⟩⟩, ?_, ?_⟩
    · intro l w hw
      cases l <;> simp only [regsFrag, reduceCtorEq] at hw
      split at hw
      · cases hw; rfl
      · cases hw
    · intro x w hw
      simp only [xmmsMap] at hw
      split at hw
      · cases hw; rfl
      · cases hw

/-- One chunk. -/
theorem chunkPt_iff_chunksAt (s : Silmaril.Machine.SystemV.Abi.Ffi.State)
    (bs : Silmaril.Cerberus.NativeTypes.Bytes) (c : Chunk) :
    XHolds (chunkPt (toSepBytes bs) c) (ffiXState s) ↔
      modelled c = true ∧ ChunksAt s bs [c] := by
  rw [chunkPt, chunksPt_iff_chunksAt]
  simp

/-! ## Arguments -/

theorem argPt_stack {fr : Frame} {a : Argument} {off : Nat} (h : a.stackOffset = some off)
    (bytes : List Byte) :
    argPt fr a bytes = ↑ₓ(bytesPt (fr.sp.toNat + 8 + off) bytes) := by
  simp [argPt, h]

theorem argPt_reg {fr : Frame} {a : Argument} (h : a.stackOffset = none) (bytes : List Byte) :
    argPt fr a bytes = chunksPt bytes a.chunks := by
  simp [argPt, h]

/-- A register argument holds of the projection iff `Ffi.ChunksAt` holds (modelled chunks). -/
theorem argPt_reg_iff (s : Silmaril.Machine.SystemV.Abi.Ffi.State) (fr : Frame) {a : Argument}
    (h : a.stackOffset = none) (bs : Silmaril.Cerberus.NativeTypes.Bytes) :
    XHolds (argPt fr a (toSepBytes bs)) (ffiXState s) ↔
      (∀ c ∈ a.chunks, modelled c = true) ∧ ChunksAt s bs a.chunks := by
  rw [argPt_reg h, chunksPt_iff_chunksAt]

/-- A non-empty run of byte atoms does not wrap. -/
theorem bytesAt_bound {need : Silmaril.Process.Permissions → Prop} :
    ∀ {a : Nat} {bs : List Byte} {h : Frag}, bs ≠ [] → bytesAt need a bs h →
      a + bs.length ≤ 2 ^ 64
  | _, [], _, hne, _ => absurd rfl hne
  | a, [_], _, _, hp => by
    obtain ⟨_, _, _, _, ⟨ha, _⟩, _⟩ := hp
    simp only [Silmaril.Process.addressLimit] at ha
    simp; omega
  | a, _ :: b :: bs, _, _, hp => by
    obtain ⟨_, _, _, _, _, hr⟩ := hp
    have := bytesAt_bound (List.cons_ne_nil b bs) hr
    simp only [List.length_cons] at this ⊢
    omega

/-- **A stack argument is stored where `Ffi.ArgumentAt` reads it**: at
`[rsp + 8 + stackOffset]`, when the frame's `sp` is the projection's `rsp`. -/
theorem argPt_stack_storedAt (s : Silmaril.Machine.SystemV.Abi.Ffi.State) {fr : Frame}
    {a : Argument} {off : Nat} (h : a.stackOffset = some off)
    (hsp : fr.sp = s.machine.core.read .rsp) {bs : Silmaril.Cerberus.NativeTypes.Bytes}
    (hne : bs ≠ []) (hh : XHolds (argPt fr a (toSepBytes bs)) (ffiXState s)) :
    StoredAt s ((s.machine.core.read .rsp).toNat + 8 + off) bs := by
  rw [argPt_stack h] at hh
  obtain ⟨hx, ⟨hp, _⟩, hle₁, _⟩ := hh
  rw [hsp] at hp
  have hne' : toSepBytes bs ≠ [] := by simpa [toSepBytes] using hne
  have hr := Silmaril.X86.Sep.readBytes_of_bytesPt hne' hp hle₁
  have hb := bytesAt_bound hne' hp
  rw [toSepBytes_length] at hr hb
  exact ⟨hb, hr⟩

/-! ## The BI of `XFrag` -/

/-- `xsep` is the generic BI separating conjunction over `XFrag`, with K3's product
separation algebra. So K3's `Laws (BI.ops XFrag)` apply to `XSProp`. -/
theorem xsep_eq_bi_sep : xsep = Silmaril.X86.Sep.BI.sep (α := XFrag) := by
  funext P Q h
  simp only [xsep, Silmaril.X86.Sep.BI.sep]
  have hu : ∀ a b : XFrag, XFrag.union a b = Silmaril.X86.Sep.BI.SepAlg.union a b :=
    fun _ _ => rfl
  simp only [hu]
  rfl

theorem xemp_eq_bi_emp : xemp = Silmaril.X86.Sep.BI.emp (α := XFrag) := rfl

/-! ## Plans computed by `Abi.plan` (decided by the kernel)

The C layout shapes. Every alignment is a power of two (the layout check adds
a power-of-two check to `objectOfCtype`). Each `plan_*` is `decide` (on `Except.toOption`);
each `*_argsPt` unfolds the placement assertion of that plan. -/

namespace Examples

open Silmaril.Machine.SystemV.Abi (Object plan aggregate)

/-- `decide` on `Except` equality is stuck in the module system (Batteries' instance body is
not exposed); `Option`'s is not, so the examples decide `Except.toOption`. -/
theorem ok_of_toOption {α : Type} {e : Except String α} {x : α} (h : e.toOption = some x) :
    e = .ok x := by
  cases e <;> simp_all [Except.toOption]

/-- `struct pair { u64 a, b; }`: INTEGER, INTEGER. -/
def pairObj : Object := aggregate 16 8 [⟨0, .integer 8, none⟩, ⟨64, .integer 8, none⟩]
/-- `struct big { u64 x[4]; }`: 32 bytes, MEMORY. -/
def bigObj : Object := aggregate 32 8
  [⟨0, .integer 8, none⟩, ⟨64, .integer 8, none⟩, ⟨128, .integer 8, none⟩, ⟨192, .integer 8, none⟩]
/-- `struct mix { u32 a; u16 b; u8 c; }`: one INTEGER eightbyte with a padding byte. -/
def mixObj : Object := aggregate 8 4
  [⟨0, .integer 4, none⟩, ⟨32, .integer 2, none⟩, ⟨48, .integer 1, none⟩]
/-- `struct vec2 { double x, y; }`: SSE, SSE. -/
def vec2Obj : Object := aggregate 16 8
  [⟨0, .floating .binary64, none⟩, ⟨64, .floating .binary64, none⟩]
/-- `int fmt7(char *buf, u64 cap, const char *fmt, ...)` called with seven `int`s. -/
def fmt7Args : List Object :=
  [.pointer, .integer 8, .pointer] ++ List.replicate 7 (.integer 4)

/-- `struct pair pair_swap(struct pair p)`: `rdi:rsi` in, `rax:rdx` out. -/
theorem plan_pair : plan {} [pairObj] (some pairObj) 1 false = .ok
    ⟨[⟨pairObj, [⟨0, 8, .gp .rdi⟩, ⟨8, 8, .gp .rsi⟩], none⟩],
      .direct [⟨0, 8, .gp .rax⟩, ⟨8, 8, .gp .rdx⟩], 0, 16, 2, 0, none⟩ :=
    ok_of_toOption (by decide)

/-- `struct big big_pass(struct big b)`: the argument at `[rsp + 8]`, the result by sret. -/
theorem plan_big : plan {} [bigObj] (some bigObj) 1 false = .ok
    ⟨[⟨bigObj, [], some 0⟩], .indirect 32 8, 32, 16, 1, 0, none⟩ :=
    ok_of_toOption (by decide)

/-- `u32 mix_get(struct mix m)`: all eight bytes (with padding) in `rdi`, result in `eax`. -/
theorem plan_mix : plan {} [mixObj] (some (.integer 4)) 1 false = .ok
    ⟨[⟨mixObj, [⟨0, 8, .gp .rdi⟩], none⟩], .direct [⟨0, 4, .gp .rax⟩], 0, 16, 1, 0, none⟩ :=
    ok_of_toOption (by decide)

/-- `struct vec2 vec2_add(struct vec2 a)`: `xmm0`, `xmm1` in and out (low quadwords). -/
theorem plan_vec2 : plan {} [vec2Obj] (some vec2Obj) 1 false = .ok
    ⟨[⟨vec2Obj, [⟨0, 8, .vector 0 0⟩, ⟨8, 8, .vector 1 0⟩], none⟩],
      .direct [⟨0, 8, .vector 0 0⟩, ⟨8, 8, .vector 1 0⟩], 0, 16, 0, 2, none⟩ :=
    ok_of_toOption (by decide)

/-- `fmt7`: three named arguments and seven variadic `int`s; the first three `int`s take
`rcx`, `r8`, `r9`, the last four spill to `[rsp + 8 + 0, 8, 16, 24]`; `al` bounds 0 vector
registers. -/
theorem plan_fmt7 : plan {} fmt7Args (some (.integer 4)) 3 true = .ok
    ⟨[⟨.pointer, [⟨0, 8, .gp .rdi⟩], none⟩, ⟨.integer 8, [⟨0, 8, .gp .rsi⟩], none⟩,
      ⟨.pointer, [⟨0, 8, .gp .rdx⟩], none⟩, ⟨.integer 4, [⟨0, 4, .gp .rcx⟩], none⟩,
      ⟨.integer 4, [⟨0, 4, .gp .r8⟩], none⟩, ⟨.integer 4, [⟨0, 4, .gp .r9⟩], none⟩,
      ⟨.integer 4, [], some 0⟩, ⟨.integer 4, [], some 8⟩, ⟨.integer 4, [], some 16⟩,
      ⟨.integer 4, [], some 24⟩],
      .direct [⟨0, 4, .gp .rax⟩], 32, 16, 6, 0, some 0⟩ :=
    ok_of_toOption (by decide)

theorem pair_argsPt {p : CallPlan} (hp : plan {} [pairObj] (some pairObj) 1 false = .ok p)
    (fr : Frame) (b rb : List Byte) (sret : Option Word) :
    argsPt fr p [b] = (chunksPt b [⟨0, 8, .gp .rdi⟩, ⟨8, 8, .gp .rsi⟩] ∗ₓ xemp) ∧
      retPt p.result sret rb = chunksPt rb [⟨0, 8, .gp .rax⟩, ⟨8, 8, .gp .rdx⟩] := by
  rw [plan_pair] at hp; cases hp; exact ⟨rfl, rfl⟩

theorem big_argsPt {p : CallPlan} (hp : plan {} [bigObj] (some bigObj) 1 false = .ok p)
    (fr : Frame) (b rb : List Byte) (r : Word) :
    argsPt fr p [b] = (↑ₓ(bytesPt (fr.sp.toNat + 8 + 0) b) ∗ₓ xemp) ∧
      sretPt p.result (some r) = ↑ₓ(regPt .rdi r ∗ blockAny r.toNat 32 ∗ ⌜r.toNat % 8 = 0⌝) ∧
      retPt p.result (some r) rb = ↑ₓ(regPt .rax r ∗ bytesPt r.toNat rb ∗ ⌜rb.length = 32⌝) ∧
      p.stackSize = 32 := by
  rw [plan_big] at hp; cases hp; exact ⟨rfl, rfl, rfl, rfl⟩

theorem mix_argsPt {p : CallPlan} (hp : plan {} [mixObj] (some (.integer 4)) 1 false = .ok p)
    (fr : Frame) (b : List Byte) :
    argsPt fr p [b] = (chunksPt b [⟨0, 8, .gp .rdi⟩] ∗ₓ xemp) ∧ sretPt p.result none = xemp := by
  rw [plan_mix] at hp; cases hp; exact ⟨rfl, rfl⟩

theorem vec2_argsPt {p : CallPlan} (hp : plan {} [vec2Obj] (some vec2Obj) 1 false = .ok p)
    (fr : Frame) (b rb : List Byte) (sret : Option Word) :
    argsPt fr p [b] = (chunksPt b [⟨0, 8, .vector 0 0⟩, ⟨8, 8, .vector 1 0⟩] ∗ₓ xemp) ∧
      retPt p.result sret rb = chunksPt rb [⟨0, 8, .vector 0 0⟩, ⟨8, 8, .vector 1 0⟩] := by
  rw [plan_vec2] at hp; cases hp; exact ⟨rfl, rfl⟩

theorem fmt7_argsPt {p : CallPlan} (hp : plan {} fmt7Args (some (.integer 4)) 3 true = .ok p)
    (fr : Frame) (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : List Byte) :
    argsPt fr p [b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉] =
      (chunksPt b₀ [⟨0, 8, .gp .rdi⟩] ∗ₓ chunksPt b₁ [⟨0, 8, .gp .rsi⟩] ∗ₓ
        chunksPt b₂ [⟨0, 8, .gp .rdx⟩] ∗ₓ chunksPt b₃ [⟨0, 4, .gp .rcx⟩] ∗ₓ
        chunksPt b₄ [⟨0, 4, .gp .r8⟩] ∗ₓ chunksPt b₅ [⟨0, 4, .gp .r9⟩] ∗ₓ
        ↑ₓ(bytesPt (fr.sp.toNat + 8 + 0) b₆) ∗ₓ ↑ₓ(bytesPt (fr.sp.toNat + 8 + 8) b₇) ∗ₓ
        ↑ₓ(bytesPt (fr.sp.toNat + 8 + 16) b₈) ∗ₓ ↑ₓ(bytesPt (fr.sp.toNat + 8 + 24) b₉) ∗ₓ
        xemp) ∧
      alPt p =
        ↑ₓ(sexists fun w : Word => regPt .rax w ∗ ⌜0 ≤ w.toNat % 256 ∧ w.toNat % 256 ≤ 8⌝) := by
  rw [plan_fmt7] at hp; cases hp; exact ⟨rfl, rfl⟩

/-- Too few byte lists for the plan: `argsPt` is `False`. -/
theorem fmt7_argsPt_short {p : CallPlan}
    (hp : plan {} fmt7Args (some (.integer 4)) 3 true = .ok p) (fr : Frame) (b : List Byte)
    (h : XFrag) :
    ¬ argsPt fr p [b] h := by
  rw [plan_fmt7] at hp; cases hp
  rintro ⟨_, _, _, _, _, hf⟩
  exact hf

/-! ### Non-vacuity and mutation probes (review)

`chunksPt` is satisfiable on concrete fragments (two GP chunks; SSE+SSEUP halves sharing one
XMM register), rejects a fragment whose register disagrees with one object byte, and is
`False` on x87 chunks. -/

/-- Register values for the probes: `rdi` holds bytes 1..8, every other GP register 9..16. -/
def probeRegs : Reg → Word := fun r => if r = .rdi then 0x0807060504030201 else 0x100f0e0d0c0b0a09
/-- The object bytes 1..16. -/
def probeBytes : List Byte := (List.range 16).map fun i => BitVec.ofNat 8 (i + 1)
/-- Every XMM register holds bytes 1..16. -/
def probeXmm : XReg → Silmaril.X86.Sse9.Xmm := fun _ => 0x100f0e0d0c0b0a090807060504030201

theorem pair_chunksPt_sat : chunksPt probeBytes [⟨0, 8, .gp .rdi⟩, ⟨8, 8, .gp .rsi⟩]
    (regsFrag [.rdi, .rsi] probeRegs, xmmsMap [] fun _ => 0) := by
  refine ⟨probeRegs, fun _ => 0, rfl, ?_⟩
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

theorem pair_chunksPt_mutated : ¬ chunksPt (probeBytes.set 3 0)
    [⟨0, 8, .gp .rdi⟩, ⟨8, 8, .gp .rsi⟩]
    (regsFrag [.rdi, .rsi] probeRegs, xmmsMap [] fun _ => 0) := by
  rintro ⟨g, v, he, hall⟩
  have h1 := congrFun (congrArg Prod.fst he) (.reg .rdi)
  simp [regsFrag, gpRegs] at h1
  have := (hall ⟨0, 8, .gp .rdi⟩ (by simp)).2.2
  simp only at this
  rw [← h1] at this
  revert this; decide

theorem sseup_chunksPt_sat : chunksPt probeBytes [⟨0, 8, .vector 0 0⟩, ⟨8, 8, .vector 0 8⟩]
    (regsFrag [] fun _ => 0, xmmsMap [xregOfIdx 0, xregOfIdx 0] probeXmm) := by
  refine ⟨fun _ => 0, probeXmm, rfl, ?_⟩
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

theorem x87_chunksPt_false (h : XFrag) : ¬ chunksPt probeBytes [⟨0, 8, .x87 0⟩] h := by
  rintro ⟨_, _, _, hall⟩
  exact absurd (hall ⟨0, 8, .x87 0⟩ (by simp)).1 (by decide)

end Examples

end Silmaril.Proofs.X86.Sep.Plan
