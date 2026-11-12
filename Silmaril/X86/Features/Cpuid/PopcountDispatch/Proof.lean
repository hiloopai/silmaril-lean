module

public import Silmaril.X86.Features.Cpuid.SegVC
public import Silmaril.X86.Features.Cpuid.PopcountDispatch.Code
public import Silmaril.X86.Ext.Store

/-!
# `popcount_dispatch` is correct on every consistent processor

`popcount_dispatch(x)` executes CPUID leaf 1 (ECX = 0), tests ECX bit 23 (POPCNT),
and returns `popcnt x` or the SWAR popcount of `x`. On every consistent x86-64
profile `p` (`Profile.Consistent`, `baseline64 ⊆ p.features`), from the entry
with the image loaded, `rdi = x` and an eight-byte writable, readable stack slot
below `rsp` apart from the code, the machine of `p` (`Profile.isa p exit`: the
feature-gated machine with CPUID answering as `p`) reaches one of the two RETs
with `rax = popcount x`, `rsp` and `rbx` restored (`reaches_ret`).

The proof is one `seg_vc` over the whole function: CPUID is the summary
`cpuidSub`, and on the POPCNT branch the side condition of `popcnt` (its feature
check) is discharged by the branch condition through `Profile.popcnt_test`.
-/

@[expose] public section

namespace Silmaril.X86.Features.Cpuid.PopcountDispatch

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

open Silmaril.X86 (Word Byte Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.X86.Features

/-! ## Push and pop in the VCs -/

/-- A PUSH whose success is not yet known: the VC asks for the write permission and
continues from every memory the push may produce. -/
theorem onOk_retire_pushWord {P : X86.State → Memory → Prop} {next : Word} {s : X86.State}
    {memory : Memory} {v : Word} :
    onOk P (retire next (X86.pushWord s memory v)) ↔
      memory.Permitted .write (s.read .rsp - 8#64).toNat 8 ∧
        ∀ after, X86.pushWord s memory v = some (s.write .rsp (s.read .rsp - 8#64), after) →
          P { s.write .rsp (s.read .rsp - 8#64) with rip := next } after := by
  constructor
  · intro h
    cases hp : X86.pushWord s memory v with
    | none => rw [hp] at h; exact h.elim
    | some r =>
      obtain ⟨t, after⟩ := r
      have ht := X86.pushWord_state hp
      subst ht
      refine ⟨?_, fun after' h' => ?_⟩
      · by_contra hn
        rw [(X86.pushWord_eq_none_iff s memory v).mpr hn] at hp
        cases hp
      · cases h'
        rw [hp] at h
        exact h
  · rintro ⟨hw, h⟩
    have hp := X86.pushWord_eq_some (value := v) hw
    rw [hp]
    exact h _ hp

/-- A POP of the slot a PUSH filled. -/
theorem popWord_slot {u : X86.State} {after : Memory} {sp v : Word}
    (hr : after.readBytes (sp - 8#64).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v]))
    (hu : u.read .rsp = sp - 8#64) :
    X86.popWord u after = some (v, u.write .rsp (u.read .rsp + 8#64)) :=
  X86.popWord_of_readBytes (by rw [hu]; exact hr)

/-! ## The extended state in the VCs -/

theorem setCore_core (s : State) (c : X86.State) : (s.setCore c).core = c := rfl

theorem setCore_setCore (s : State) (c d : X86.State) : (s.setCore c).setCore d = s.setCore d :=
  rfl

/-! ## The segment -/

/-- The caller's side of the contract. -/
structure Entry (base x rbx0 sp : Word) (s : MState) : Prop where
  rdi : s.state.core.read .rdi = x
  rbx : s.state.core.read .rbx = rbx0
  rsp : s.state.core.read .rsp = sp
  slotW : s.memory.Permitted .write (sp - 8#64).toNat 8
  slotR : s.memory.Permitted .read (sp - 8#64).toNat 8
  apart : (sp - 8#64).toNat + 8 ≤ base.toNat ∨ base.toNat + code.length ≤ (sp - 8#64).toNat

/-- At a RET: the popcount in `rax`, `rsp` and `rbx` restored. -/
def Done (x rbx0 sp : Word) (s : MState) : Prop :=
  s.state.core.read .rax = BitVec.ofNat 64 (popcntN x) ∧ s.state.core.read .rsp = sp ∧
    s.state.core.read .rbx = rbx0

def stops (x rbx0 sp : Word) : List (Nat × (MState → Prop)) :=
  [(0x72, Done x rbx0 sp), (0x7e, Done x rbx0 sp)]

set_option maxRecDepth 8000 in
def subs (p : Profile) (exit base : Word) : List (Nat × Nat × Call (p.isa exit)) :=
  [(8, 10, cpuidSub p exit base code 8 code_cpuid (by rw [code_length]; decide))]

theorem listing_valid (p : Profile) (exit : Word) :
    Listing.valid (p.isa exit) code listing = true :=
  listing_decodes

/-- After the PUSH: `rbx` saved in the slot below the caller's `rsp`. -/
structure Mid (x rbx0 sp : Word) (s : MState) : Prop where
  rdi : s.state.core.read .rdi = x
  rsp : s.state.core.read .rsp = sp - 8#64
  slot : s.memory.readBytes (sp - 8#64).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [rbx0])

/-- At the POPCNT branch: the feature was observed. -/
def AtPopcnt (p : Profile) (x rbx0 sp : Word) (s : MState) : Prop :=
  Mid x rbx0 sp s ∧ Feature.popcnt ∈ p.features

/-- Segment A, from after the PUSH to the two branch targets. -/
def stopsA (p : Profile) (x rbx0 sp : Word) : List (Nat × (MState → Prop)) :=
  [(0x12, Mid x rbx0 sp), (0x78, AtPopcnt p x rbx0 sp)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vcA (p : Profile) (hp : p.Consistent) (hb : FeatureSet.baseline64 ⊆ p.features)
    (exit base x rbx0 sp : Word) :
    ∀ s : MState, True → Loaded s.memory base code → s.state.core.rip = base + BitVec.ofNat 64 1 →
      Mid x rbx0 sp s →
      wpN (p.isa exit) code listing [] (stopsA p x rbx0 sp) [] (subs p exit base) base none 8 1 s := by
  intro s _ hl hrip hM
  seg_vc [listing, stopsA, subs, hrip, hl, hM.rsp, hM.rdi,
    setCore_core, setCore_setCore, baseCheck, baseRequirement, cpuidSub, cpuidNext, forall_eq',
    forall_eq, Ext.Wire.cpuidState, Profile.platform, State.advance, State.setRip, State.rip]
  simp only [false_and, not_false_eq_true, true_and]
  refine ⟨fun hbit => ⟨⟨?_, ?_, hM.slot⟩, (Profile.popcnt_test hp hb).mp (by simpa using hbit)⟩,
    fun _ => ⟨?_, ?_, hM.slot⟩⟩ <;> simp only [setCore_core] <;> seg_read [hM.rdi, hM.rsp]

def stopsB (x rbx0 sp : Word) : List (Nat × (MState → Prop)) := [(0x72, Done x rbx0 sp)]

def stopsC (x rbx0 sp : Word) : List (Nat × (MState → Prop)) := [(0x7e, Done x rbx0 sp)]

/-- `rbx` and `rsp` restored (after the fallback's POP). -/
def Restored (rbx0 sp : Word) (s : MState) : Prop :=
  s.state.core.read .rsp = sp ∧ s.state.core.read .rbx = rbx0

def At36 (x rbx0 sp : Word) (s : MState) : Prop :=
  Restored rbx0 sp s ∧ s.state.core.read .rax = swarA x ∧
    s.state.core.read .rcx = 0x3333333333333333#64

def At50 (x rbx0 sp : Word) (s : MState) : Prop :=
  Restored rbx0 sp s ∧ s.state.core.read .rdx = swarB x ∧
    s.state.core.read .rcx = 0x0F0F0F0F0F0F0F0F#64

def At6a (x rbx0 sp : Word) (s : MState) : Prop :=
  Restored rbx0 sp s ∧ s.state.core.read .rax = swarC x ∧
    s.state.core.read .rdx = 0x0101010101010101#64

def At6e (x rbx0 sp : Word) (s : MState) : Prop :=
  Restored rbx0 sp s ∧ s.state.core.read .rax = swarC x * 0x0101010101010101#64

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Segment B1: `0x12` to `0x36`, the POP and the first SWAR level. -/
theorem vcB1 (p : Profile) (exit base x rbx0 sp : Word) :
    ∀ s : MState, True → Loaded s.memory base code → s.state.core.rip = base + BitVec.ofNat 64 0x12 →
      Mid x rbx0 sp s →
      wpN (p.isa exit) code listing [] [(0x36, At36 x rbx0 sp)] [] [] base none 9 0x12 s := by
  intro s _ hl hrip hM
  seg_vc [listing, hrip, hl, hM.rsp, hM.rdi, popWord_slot hM.slot,
    setCore_core, setCore_setCore, baseCheck, baseRequirement, Count.raw, ShiftOp.result]
  simp only [false_and, not_false_eq_true, true_and, At36, Restored, setCore_core]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> seg_read [BitVec.sub_add_cancel] <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Segment B2: `0x36` to `0x50`, the second level. -/
theorem vcB2 (p : Profile) (exit base x rbx0 sp : Word) :
    ∀ s : MState, True → Loaded s.memory base code → s.state.core.rip = base + BitVec.ofNat 64 0x36 →
      At36 x rbx0 sp s →
      wpN (p.isa exit) code listing [] [(0x50, At50 x rbx0 sp)] [] [] base none 7 0x36 s := by
  intro s _ hl hrip ⟨⟨hsp, hbx⟩, hax, hcx⟩
  seg_vc [listing, hrip, hl, hsp, hbx, hax, hcx,
    setCore_core, setCore_setCore, baseCheck, baseRequirement, Count.raw, ShiftOp.result]
  simp only [false_and, not_false_eq_true, true_and, At50, Restored, setCore_core]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> seg_read [hsp, hbx] <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Segment B3a: `0x50` to the IMUL at `0x6a`, the third level. -/
theorem vcB3a (p : Profile) (exit base x rbx0 sp : Word) :
    ∀ s : MState, True → Loaded s.memory base code → s.state.core.rip = base + BitVec.ofNat 64 0x50 →
      At50 x rbx0 sp s →
      wpN (p.isa exit) code listing [] [(0x6a, At6a x rbx0 sp)] [] [] base none 7 0x50 s := by
  intro s _ hl hrip ⟨⟨hsp, hbx⟩, hdx, hcx⟩
  seg_vc [listing, hrip, hl, hsp, hbx, hdx, hcx,
    setCore_core, setCore_setCore, baseCheck, baseRequirement, Count.raw, ShiftOp.result]
  simp only [false_and, not_false_eq_true, true_and, At6a, Restored, setCore_core]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> seg_read [hsp, hbx] <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Segment B3b: the IMUL (on its own: its flags are expensive to carry further). -/
theorem vcB3b (p : Profile) (exit base x rbx0 sp : Word) :
    ∀ s : MState, True → Loaded s.memory base code → s.state.core.rip = base + BitVec.ofNat 64 0x6a →
      At6a x rbx0 sp s →
      wpN (p.isa exit) code listing [] [(0x6e, At6e x rbx0 sp)] [] [] base none 2 0x6a s := by
  intro s _ hl hrip ⟨⟨hsp, hbx⟩, hax, hdx⟩
  seg_vc [listing, hrip, hl, hsp, hbx, hax, hdx,
    setCore_core, setCore_setCore, baseCheck, baseRequirement]
  simp only [false_and, not_false_eq_true, true_and, At6e, Restored, setCore_core]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> seg_read [hsp, hbx]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Segment B3c: the final shift, to the RET at `0x72`. -/
theorem vcB3c (p : Profile) (exit base x rbx0 sp : Word) :
    ∀ s : MState, True → Loaded s.memory base code → s.state.core.rip = base + BitVec.ofNat 64 0x6e →
      At6e x rbx0 sp s →
      wpN (p.isa exit) code listing [] (stopsB x rbx0 sp) [] [] base none 2 0x6e s := by
  intro s _ hl hrip ⟨⟨hsp, hbx⟩, hax⟩
  seg_vc [listing, stopsB, hrip, hl, hsp, hbx, hax,
    setCore_core, setCore_setCore, baseCheck, baseRequirement, Count.raw, ShiftOp.result]
  simp only [false_and, not_false_eq_true, true_and, Done, setCore_core]
  refine ⟨?_, ?_, ?_⟩ <;> seg_read [hsp, hbx]
  exact swar_eq_popcnt x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Segment C, POPCNT: its feature check is discharged by the branch condition. -/
theorem vcC (p : Profile) (exit base x rbx0 sp : Word) :
    ∀ s : MState, True → Loaded s.memory base code → s.state.core.rip = base + BitVec.ofNat 64 0x78 →
      AtPopcnt p x rbx0 sp s →
      wpN (p.isa exit) code listing [] (stopsC x rbx0 sp) [] [] base none 3 0x78 s := by
  intro s _ hl hrip ⟨hM, hpop⟩
  seg_vc [listing, stopsC, hrip, hl, hM.rsp, hM.rdi, popWord_slot hM.slot,
    setCore_core, setCore_setCore, baseCheck, baseRequirement, hpop]
  have hpop' : p.features.has Feature.popcnt = true := hpop
  simp only [hpop', ite_true, false_and, not_false_eq_true, and_true, true_and, Done, setCore_core]
  refine ⟨?_, ?_, ?_⟩ <;> seg_read [BitVec.sub_add_cancel]; rfl

/-! ## The PUSH, and the composition -/

set_option maxRecDepth 8000 in
/-- The PUSH at the entry. -/
theorem push_step (p : Profile) (exit base x rbx0 sp : Word) (s : MState)
    (hl : Loaded s.memory base code) (hrip : s.state.core.rip = base)
    (hE : Entry base x rbx0 sp s) :
    ∃ s1, stepOpt p.features [sysExt p] exit s = some s1 ∧ Loaded s1.memory base code ∧
      s1.state.core.rip = base + BitVec.ofNat 64 1 ∧ Mid x rbx0 sp s1 := by
  have hw : s.memory.Permitted .write (s.state.core.read .rsp - 8#64).toNat 8 := by
    rw [hE.rsp]; exact hE.slotW
  obtain ⟨M, hpush⟩ : ∃ M, X86.pushWord s.state.core s.memory rbx0 =
      some (s.state.core.write .rsp (s.state.core.read .rsp - 8#64), M) :=
    ⟨_, X86.pushWord_eq_some hw⟩
  have hx : Ext.exec (.push .rbx) s.state.core s.memory 1 =
      .ok { s.state.core.write .rsp (s.state.core.read .rsp - 8#64) with
        rip := s.state.core.rip + BitVec.ofNat 64 1 } M := by
    simp only [Ext.exec, hE.rbx, hpush, retire]
  have hS := Stored.of_pushWord hpush
  rw [hE.rsp] at hS
  refine ⟨_, stepOpt_of_loaded (o := 0) (l := 1) hl (by rw [hrip]; simp) (by decide)
    (by decide) hx rfl (by simp), Loaded.of_stored hl hS (by
      rw [X86.length_encodeWords_singleton]; have := hE.apart; omega), ?_, ?_, ?_, ?_⟩
  · show s.state.core.rip + BitVec.ofNat 64 1 = _
    rw [hrip]
  · simp only [setCore_core]
    seg_read [hE.rdi]
  · simp only [setCore_core]
    seg_read [hE.rsp]
  · have := X86.pushWord_readBytes hpush (by rw [hE.rsp]; exact hE.slotR)
    rw [hE.rsp] at this
    exact this

/-- A segment with one stop and no cut points, as a run. -/
theorem seg {p : Profile} {exit base : Word} {o entry K : Nat} {q pre : MState → Prop}
    {subs' : List (Nat × Nat × Call (p.isa exit))}
    (hvc : ∀ s : MState, True → Loaded s.memory base code →
      s.state.core.rip = base + BitVec.ofNat 64 entry → pre s →
      wpN (p.isa exit) code listing [] [(o, q)] [] subs' base none K entry s)
    (s : MState) (hl : Loaded s.memory base code)
    (hrip : s.state.core.rip = base + BitVec.ofNat 64 entry) (hpre : pre s) :
    ∃ t, Machine.Execution.Reaches (stepOpt p.features [sysExt p] exit) s t ∧ q t ∧
      t.state.core.rip = base + BitVec.ofNat 64 o ∧ Loaded t.memory base code := by
  obtain ⟨t, hr, hq, hrip', hl', -⟩ := sound_one (I := p.isa exit) (listing_valid p exit)
    (cuts := []) (calls := []) (subs := subs') ⟨hvc, fun _ h => nomatch h⟩ s trivial hl hrip hpre
  exact ⟨t, hr, hq, hrip', hl'⟩

/-- Segment A as a run: to `0x12` (no POPCNT) or `0x78` (POPCNT observed). -/
theorem segA (p : Profile) (hp : p.Consistent) (hb : FeatureSet.baseline64 ⊆ p.features)
    (exit base x rbx0 sp : Word) (s : MState) (hl : Loaded s.memory base code)
    (hrip : s.state.core.rip = base + BitVec.ofNat 64 1) (hM : Mid x rbx0 sp s) :
    ∃ t, Machine.Execution.Reaches (stepOpt p.features [sysExt p] exit) s t ∧
      Loaded t.memory base code ∧
      ((t.state.core.rip = base + BitVec.ofNat 64 0x12 ∧ Mid x rbx0 sp t) ∨
        (t.state.core.rip = base + BitVec.ofNat 64 0x78 ∧ AtPopcnt p x rbx0 sp t)) := by
  obtain ⟨o, q, t, hq, ht, hr, hrip', hl', -⟩ := sound (I := p.isa exit) (listing_valid p exit)
    (cuts := []) (calls := []) (subs := subs p exit base)
    (stops := stopsA p x rbx0 sp) (pre := Mid x rbx0 sp)
    ⟨vcA p hp hb exit base x rbx0 sp, fun _ h => nomatch h⟩ s trivial hl hrip hM
  refine ⟨t, hr, hl', ?_⟩
  simp only [stopsA, List.lookup_cons, List.lookup_nil] at hq
  split at hq
  · rename_i h; cases hq
    have : o = 0x12 := by simpa using h
    subst this; exact .inl ⟨hrip', ht⟩
  · split at hq
    · rename_i _ h; cases hq
      have : o = 0x78 := by simpa using h
      subst this; exact .inr ⟨hrip', ht⟩
    · cases hq

/-- **VERIFIED.** On every consistent x86-64 profile, `popcount_dispatch` runs from its
entry to one of its RETs with `rax = popcount x` and `rsp`, `rbx` restored. -/
theorem reaches_ret (p : Profile) (hp : p.Consistent) (hb : FeatureSet.baseline64 ⊆ p.features)
    (exit base x rbx0 sp : Word) (s : MState) (hl : Loaded s.memory base code)
    (hrip : s.state.core.rip = base) (hE : Entry base x rbx0 sp s) :
    ∃ t, Machine.Execution.Reaches (stepOpt p.features [sysExt p] exit) s t ∧
      Done x rbx0 sp t ∧ Loaded t.memory base code ∧
      (t.state.core.rip = base + BitVec.ofNat 64 0x72 ∨
        t.state.core.rip = base + BitVec.ofNat 64 0x7e) := by
  obtain ⟨s1, h1, hl1, hrip1, hM1⟩ := push_step p exit base x rbx0 sp s hl hrip hE
  have r1 : Machine.Execution.Reaches (stepOpt p.features [sysExt p] exit) s s1 :=
    reaches_head (I := p.isa exit) h1
  obtain ⟨s2, r2, hl2, h2⟩ := segA p hp hb exit base x rbx0 sp s1 hl1 hrip1 hM1
  rcases h2 with ⟨hrip2, hM2⟩ | ⟨hrip2, hP2⟩
  · obtain ⟨s3, r3, h3, hrip3, hl3⟩ := seg (vcB1 p exit base x rbx0 sp) s2 hl2 hrip2 hM2
    obtain ⟨s4, r4, h4, hrip4, hl4⟩ := seg (vcB2 p exit base x rbx0 sp) s3 hl3 hrip3 h3
    obtain ⟨s5, r5, h5, hrip5, hl5⟩ := seg (vcB3a p exit base x rbx0 sp) s4 hl4 hrip4 h4
    obtain ⟨s6, r6, h6, hrip6, hl6⟩ := seg (vcB3b p exit base x rbx0 sp) s5 hl5 hrip5 h5
    obtain ⟨s7, r7, h7, hrip7, hl7⟩ := seg (vcB3c p exit base x rbx0 sp) s6 hl6 hrip6 h6
    exact ⟨s7, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans r7))))), h7, hl7,
      .inl hrip7⟩
  · obtain ⟨s3, r3, h3, hrip3, hl3⟩ := seg (vcC p exit base x rbx0 sp) s2 hl2 hrip2 hP2
    exact ⟨s3, r1.trans (r2.trans r3), h3, hl3, .inr hrip3⟩

end Silmaril.X86.Features.Cpuid.PopcountDispatch
