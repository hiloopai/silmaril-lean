module

public import Silmaril.Machine.RiscV.Lir.Check.Defs
/-!
# Frames on the machine stack

Relations between a Lir frame and the machine: `RegsAt` (live registers of the
current frame are in their assigned RV64 registers), `SlotsAt` (slots below `N`
are 8-byte words at `sp + slotOff n`) and `SavedAt` (registers of a suspended
frame are in its save area). The lemmas describe the effect of the frame code
emitted by `Emit`: `saveAll`, `restoreAll`, `loadLocsFrom` (locations to
`a0 …`) and `storeLocsFrom` (`a0 …` to locations, with `Frame.writeAll`'s
left-to-right order).
-/

@[expose] public section

namespace Silmaril.RiscV.Backend

open Silmaril.Process (Memory)
open Silmaril.RiscV.Ext (Compute MState)
open Machine.Lir (Prog Func Block Point Loc Op Term Frame)

/-! ## Write frames -/

/-- `mem'` differs from `mem` only in bytes whose address lies in `[lo, hi)`. -/
def WritesIn (mem mem' : Memory) (lo hi : Nat) : Prop :=
  mem'.regions = mem.regions ∧ ∀ q, (q < lo ∨ hi ≤ q) → mem'.bytes.get? q = mem.bytes.get? q

theorem WritesIn.refl (mem : Memory) (lo hi : Nat) : WritesIn mem mem lo hi :=
  ⟨rfl, fun _ _ => rfl⟩

theorem WritesIn.trans {a b c : Memory} {lo hi : Nat} (h₁ : WritesIn a b lo hi)
    (h₂ : WritesIn b c lo hi) : WritesIn a c lo hi :=
  ⟨h₂.1.trans h₁.1, fun q hq => (h₂.2 q hq).trans (h₁.2 q hq)⟩

theorem WritesIn.mono {a b : Memory} {lo hi lo' hi' : Nat} (h : WritesIn a b lo hi)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : WritesIn a b lo' hi' :=
  ⟨h.1, fun q hq => h.2 q (by omega)⟩

theorem WritesIn.wordAt {mem mem' : Memory} {lo hi b : Nat} {x : Word} (h : WritesIn mem mem' lo hi)
    (hd : b + 8 ≤ lo ∨ hi ≤ b) (hw : WordAt mem b x) : WordAt mem' b x := by
  unfold WordAt Memory.readBytes at *
  rw [readWith_congr h.1 .read (fun k hk => h.2 _ (by omega))]
  exact hw

theorem writesIn_of_writeBytes {mem mem' : Memory} {a : Nat} {bs : List Process.Byte}
    (hw : mem.writeBytes a bs = some mem') : WritesIn mem mem' a (a + bs.length) := by
  have := Memory.writeBytes_writesOnly hw
  exact ⟨this.1, fun q hq => this.2 q hq⟩

/-! ## Frame placement -/

structure FrameAt (S : Space) (N B : Nat) : Prop where
  align : B % 16 = 0
  lo : S.stackLo ≤ B
  hi : B + frameSize N ≤ S.stackHi
  small : frameSize N ≤ 2032

theorem readBacking_isSome {b : Process.ByteMemory} :
    ∀ {a len : Nat}, (∀ k < len, (b.get? (a + k)).isSome = true) →
      ∃ bs, Memory.readBacking b a len = some bs
  | _, 0, _ => ⟨[], rfl⟩
  | a, len + 1, h => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h 0 (by omega))
    obtain ⟨bs, hbs⟩ := readBacking_isSome (a := a + 1) (len := len) fun k hk => by
      have := h (k + 1) (by omega); rwa [Nat.add_assoc, Nat.add_comm 1 k]
    simp only [Nat.add_zero, Std.ExtHashMap.get?_eq_getElem?] at hx
    exact ⟨x :: bs, by simp [Memory.readBacking, hx, hbs]⟩

theorem stack_readable {S : Space} {n : Nat} (hv : S.Valid n) {m : MState}
    (hr : m.memory.regions = S.regions n)
    (hb : ∀ a, S.InStack a → (m.memory.bytes.get? a).isSome = true)
    {a : Nat} (lo : S.stackLo ≤ a) (hi : a + 8 ≤ S.stackHi) :
    ∃ bs, m.memory.readBytes a 8 = some bs := by
  have hp := permitted_stack hr hv .read (by decide) lo hi
  obtain ⟨bs, hbs⟩ := readBacking_isSome (b := m.memory.bytes) (a := a) (len := 8)
    fun k hk => hb (a + k) ⟨by omega, by omega⟩
  refine ⟨bs, ?_⟩
  unfold Memory.readBytes Memory.readWith
  simp only [show m.memory.checkSpan .read a 8 = true from hp, ↓reduceIte, hbs]

/-! ## Single frame accesses -/

section Access

variable {S : Space} {n : Nat} (hv : S.Valid n) {N B : Nat} (hfr : FrameAt S N B)
include hv hfr

theorem frame_sd {r : Reg} {off : Nat} (hoff : off % 8 = 0) (hlt : off + 8 ≤ frameSize N)
    {rest : List Ext.Instr} {m : MState} (hr : m.memory.regions = S.regions n)
    (hsp : m.core.read sp = BitVec.ofNat 64 B) :
    ∃ mem', runSeq (sdI sp r off :: rest) m = runSeq rest ⟨{ m.core with pc := m.core.pc + 4 }, mem'⟩ ∧
      WordAt mem' (B + off) (m.core.read r) ∧ WritesIn m.memory mem' (B + off) (B + off + 8) := by
  have := hfr.hi; have := hfr.small; have := hv.stack_end; have := hfr.align
  have hp : m.memory.Permitted .write (B + off) 8 :=
    permitted_stack hr hv .write (by decide) (by have := hfr.lo; omega) (by omega)
  obtain ⟨mem', hw, hrun⟩ := runSeq_sd (rs := r) (rest := rest) hsp (by omega) (by omega) (by omega) hp
  refine ⟨mem', hrun, ?_, ?_⟩
  · exact wordAt_write hw (permitted_stack hr hv .read (by decide) (by have := hfr.lo; omega) (by omega))
  · simpa using writesIn_of_writeBytes hw

theorem frame_ld {rd : Reg} {off : Nat} (hoff : off % 8 = 0) (hlt : off + 8 ≤ frameSize N)
    {rest : List Ext.Instr} {m : MState} (hsp : m.core.read sp = BitVec.ofNat 64 B) {x : Word}
    (hw : WordAt m.memory (B + off) x) :
    runSeq (ldI rd sp off :: rest) m =
      runSeq rest ⟨{ m.core.write rd x with pc := m.core.pc + 4 }, m.memory⟩ := by
  have := hfr.hi; have := hfr.small; have := hv.stack_end; have := hfr.align
  exact runSeq_ld hsp (by omega) (by omega) (by omega) hw

end Access

/-! ## Frame relations -/

variable {P : Type} (A : Assign P)

def RegsAt (fr : Frame P) (core : State) : Prop :=
  ∀ r x, fr.regs r = some x → core.read (A.reg r) = x

def SlotsAt (N : Nat) (mem : Memory) (B : Nat) (fr : Frame P) : Prop :=
  ∀ n x, n < N → fr.slots n = some x → WordAt mem (B + slotOff n) x

def SavedAt (mem : Memory) (B : Nat) (fr : Frame P) : Prop :=
  ∀ r x, fr.regs r = some x → WordAt mem (B + 8 * (A.idx r).val) x

theorem SlotsAt.of_writesIn {N : Nat} {mem mem' : Memory} {B lo hi : Nat} {fr : Frame P}
    (h : SlotsAt N mem B fr) (hw : WritesIn mem mem' lo hi)
    (hd : ∀ k < N, B + slotOff k + 8 ≤ lo ∨ hi ≤ B + slotOff k) : SlotsAt N mem' B fr :=
  fun k x hk hx => hw.wordAt (hd k hk) (h k x hk hx)

theorem SavedAt.of_writesIn {mem mem' : Memory} {B lo hi : Nat} {fr : Frame P}
    (h : SavedAt A mem B fr) (hw : WritesIn mem mem' lo hi)
    (hd : ∀ i : Fin 14, B + 8 * i.val + 8 ≤ lo ∨ hi ≤ B + 8 * i.val) : SavedAt A mem' B fr :=
  fun r x hx => hw.wordAt (hd _) (h r x hx)

theorem RegsAt.congr {fr : Frame P} {c c' : State} (h : RegsAt A fr c)
    (hc : ∀ p, c'.read (A.reg p) = c.read (A.reg p)) : RegsAt A fr c' :=
  fun r x hx => (hc r).trans (h r x hx)

theorem wordAt_of_bytes {mem mem' : Memory} {b : Nat} {x : Word} (hreg : mem'.regions = mem.regions)
    (hb : ∀ k < 8, mem'.bytes.get? (b + k) = mem.bytes.get? (b + k)) (hw : WordAt mem b x) :
    WordAt mem' b x := by
  unfold WordAt Memory.readBytes at *
  rw [readWith_congr hreg .read hb]
  exact hw

theorem frameSize_ge (N : Nat) : 128 ≤ frameSize N := by unfold frameSize; omega

/-! ## Saving and restoring the allocatable registers -/

section SaveRestore

variable {S : Space} {n : Nat} (hv : S.Valid n) {N B : Nat} (hfr : FrameAt S N B)
include hv hfr

theorem sds_spec :
    ∀ (L : List (Fin 14)) (m : MState), L.Nodup → m.memory.regions = S.regions n →
    m.core.read sp = BitVec.ofNat 64 B →
    ∃ m', runSeq (L.map fun i => sdI sp (allocReg i) (8 * i.val)) m = some m' ∧
      (∀ r, m'.core.read r = m.core.read r) ∧ m'.memory.regions = m.memory.regions ∧
      (∀ q, (∀ i ∈ L, q < B + 8 * i.val ∨ B + 8 * i.val + 8 ≤ q) →
        m'.memory.bytes.get? q = m.memory.bytes.get? q) ∧
      ∀ i ∈ L, WordAt m'.memory (B + 8 * i.val) (m.core.read (allocReg i))
  | [], m, _, _, _ => ⟨m, rfl, fun _ => rfl, rfl, fun _ _ => rfl, fun _ h => by cases h⟩
  | i :: L, m, hnd, hr, hsp => by
    have hfs := frameSize_ge N
    obtain ⟨mem₁, hrun, hw₁, hwi₁⟩ := frame_sd hv hfr (r := allocReg i) (off := 8 * i.val)
      (rest := L.map fun i => sdI sp (allocReg i) (8 * i.val)) (m := m) (by omega) (by omega) hr hsp
    set m₁ : MState := ⟨{ m.core with pc := m.core.pc + 4 }, mem₁⟩
    have hr₁ : m₁.memory.regions = S.regions n := hwi₁.1.trans hr
    obtain ⟨m', h', regs', reg', bytes', words'⟩ :=
      sds_spec L m₁ (List.nodup_cons.mp hnd).2 hr₁ (by rw [State.read_setPc]; exact hsp)
    have hni : i ∉ L := (List.nodup_cons.mp hnd).1
    refine ⟨m', by simp only [List.map_cons]; rw [hrun]; exact h', fun r => ?_, reg'.trans hwi₁.1,
      fun q hq => ?_, fun i' hi' => ?_⟩
    · rw [regs' r]; rfl
    · rw [bytes' q (fun i' hi' => hq i' (List.mem_cons_of_mem _ hi'))]
      exact hwi₁.2 q (hq i List.mem_cons_self)
    · rcases List.mem_cons.mp hi' with rfl | hi'
      · apply wordAt_of_bytes reg' _ hw₁
        intro k hk
        apply bytes'
        intro j hj
        have : j ≠ i' := fun e => hni (e ▸ hj)
        have : j.val ≠ i'.val := fun e => this (Fin.ext e)
        omega
      · exact words' i' hi'

theorem saveAll_spec (m : MState) (hr : m.memory.regions = S.regions n)
    (hsp : m.core.read sp = BitVec.ofNat 64 B) :
    ∃ m', runSeq saveAll m = some m' ∧ (∀ r, m'.core.read r = m.core.read r) ∧
      WritesIn m.memory m'.memory B (B + 112) ∧
      ∀ i : Fin 14, WordAt m'.memory (B + 8 * i.val) (m.core.read (allocReg i)) := by
  obtain ⟨m', h, regs, reg, bytes, words⟩ :=
    sds_spec hv hfr (List.finRange 14) m (List.nodup_finRange 14) hr hsp
  refine ⟨m', h, regs, ⟨reg, fun q hq => bytes q fun i _ => by omega⟩, fun i => words i (by simp)⟩

theorem lds_spec :
    ∀ (L : List (Fin 14)) (m : MState), L.Nodup → m.memory.regions = S.regions n →
    (∀ a, S.InStack a → (m.memory.bytes.get? a).isSome = true) →
    m.core.read sp = BitVec.ofNat 64 B →
    ∃ m', runSeq (L.map fun i => ldI (allocReg i) sp (8 * i.val)) m = some m' ∧
      m'.memory = m.memory ∧
      (∀ r, (∀ i ∈ L, r ≠ allocReg i) → m'.core.read r = m.core.read r) ∧
      ∀ i ∈ L, ∀ x, WordAt m.memory (B + 8 * i.val) x → m'.core.read (allocReg i) = x
  | [], m, _, _, _, _ => ⟨m, rfl, rfl, fun _ _ => rfl, fun _ h => by cases h⟩
  | i :: L, m, hnd, hr, hbk, hsp => by
    have hfs := frameSize_ge N
    have := hfr.hi; have := hfr.lo; have := hfr.small; have := hv.stack_end; have := hfr.align
    obtain ⟨bs, hbs⟩ := stack_readable hv hr hbk (a := B + 8 * i.val) (by omega) (by omega)
    have e := ea_toNat hsp (show 8 * i.val < 2048 by omega) (show B + 8 * i.val < 2 ^ 64 by omega)
    have hrun := runSeq_load_cons (op := .ld) (rd := allocReg i) (rest := L.map fun i => ldI (allocReg i) sp (8 * i.val))
      (m := m) (bytes := bs) (by rw [e]; show (B + 8 * i.val) % 8 = 0; omega) (by rw [e]; exact hbs)
    set m₁ : MState := ⟨{ m.core.write (allocReg i) (Ext.LoadOp.ld.value bs) with pc := m.core.pc + 4 },
      m.memory⟩
    have hsp₁ : m₁.core.read sp = BitVec.ofNat 64 B := by
      simp only [m₁, State.read_setPc]
      rw [State.read_write_other _ _ _ _ (allocReg_ne_sp i).symm]; exact hsp
    obtain ⟨m', h', mem', regs', vals'⟩ :=
      lds_spec L m₁ (List.nodup_cons.mp hnd).2 hr hbk hsp₁
    have hni : i ∉ L := (List.nodup_cons.mp hnd).1
    refine ⟨m', hrun.trans h', mem', fun r hr' => ?_,
      fun i' hi' x hx => ?_⟩
    · rw [regs' r (fun i' hi' => hr' i' (List.mem_cons_of_mem _ hi'))]
      simp only [m₁, State.read_setPc]
      exact State.read_write_other _ _ _ _ (hr' i List.mem_cons_self)
    · rcases List.mem_cons.mp hi' with rfl | hi'
      · have hne : ∀ j ∈ L, allocReg i' ≠ allocReg j := by
          intro j hj e
          exact hni ((allocReg_injective e) ▸ hj)
        rw [regs' _ hne]
        simp only [m₁, State.read_setPc]
        rw [State.read_write_same _ _ _ (allocReg_ne_zero i')]
        rw [hx] at hbs
        cases hbs
        exact Ext.ld_value_leBytes x
      · exact vals' i' hi' x hx

theorem restoreAll_spec (m : MState) (hr : m.memory.regions = S.regions n)
    (hbk : ∀ a, S.InStack a → (m.memory.bytes.get? a).isSome = true)
    (hsp : m.core.read sp = BitVec.ofNat 64 B) :
    ∃ m', runSeq restoreAll m = some m' ∧ m'.memory = m.memory ∧
      (∀ r, (∀ i, r ≠ allocReg i) → m'.core.read r = m.core.read r) ∧
      ∀ i : Fin 14, ∀ x, WordAt m.memory (B + 8 * i.val) x → m'.core.read (allocReg i) = x := by
  obtain ⟨m', h, mem, regs, vals⟩ :=
    lds_spec hv hfr (List.finRange 14) m (List.nodup_finRange 14) hr hbk hsp
  exact ⟨m', h, mem, fun r hr' => regs r fun i _ => hr' i, fun i => vals i (by simp)⟩

end SaveRestore

/-! ## Argument registers -/

theorem argRegN_ne_alloc {j : Nat} (hj : j < 8) (i : Fin 14) : argRegN j ≠ allocReg i :=
  fun e => allocReg_ne_arg i ⟨j, hj⟩ (e.symm.trans (argRegN_eq hj))

theorem argRegN_ne {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) : argRegN j ≠ argRegN k := by
  intro e
  rw [argRegN_eq hj, argRegN_eq hk] at e
  exact h (congrArg Fin.val (argReg_injective e))

theorem argRegN_ne_sp {j : Nat} (hj : j < 8) : argRegN j ≠ sp := by
  rw [argRegN_eq hj]; exact argReg_ne_sp _
theorem argRegN_ne_s10 {j : Nat} (hj : j < 8) : argRegN j ≠ s10 := by
  rw [argRegN_eq hj]; exact argReg_ne_s10 _
theorem argRegN_ne_s11 {j : Nat} (hj : j < 8) : argRegN j ≠ s11 := by
  rw [argRegN_eq hj]; exact argReg_ne_s11 _
theorem argRegN_ne_ra {j : Nat} (hj : j < 8) : argRegN j ≠ ra := by
  rw [argRegN_eq hj]; exact argReg_ne_ra _
theorem argRegN_ne_zero {j : Nat} (hj : j < 8) : argRegN j ≠ 0#5 := by
  rw [argRegN_eq hj]; exact argReg_ne_zero _

theorem writeAll_length {P : Type} [DecidableEq P] :
    ∀ {locs : List (Loc P)} {vals : List Word} {fr fr' : Frame P},
    fr.writeAll locs vals = some fr' → locs.length = vals.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | _ :: _, _ :: _, _, _, h => by
    simp only [Frame.writeAll] at h
    simp [writeAll_length h]

theorem readAll_cons {P : Type} {fr : Frame P} {l : Loc P} {ls : List (Loc P)} {vals : List Word}
    (h : fr.readAll (l :: ls) = some vals) :
    ∃ x xs, fr.read l = some x ∧ fr.readAll ls = some xs ∧ vals = x :: xs := by
  unfold Frame.readAll at h
  rw [List.mapM_cons] at h
  cases hx : fr.read l with
  | none => simp [hx] at h
  | some x =>
    cases hxs : ls.mapM fr.read with
    | none => simp [hx, hxs] at h
    | some xs =>
      simp [hx, hxs] at h
      exact ⟨x, xs, rfl, hxs, h.symm⟩

theorem mvI_step (rd rs : Reg) (rest : List Ext.Instr) (m : MState) :
    runSeq (mvI rd rs :: rest) m =
      runSeq rest ⟨Compute.step (.base (.imm .add rd rs 0#12)) m.core, m.memory⟩ :=
  runSeq_compute_cons _ _ _

theorem mvI_read (rd rs q : Reg) (s : State) :
    (Compute.step (.base (.imm .add rd rs 0#12)) s).read q =
      if q = rd ∧ rd ≠ 0#5 then s.read rs else s.read q := by
  simp [RiscV.Instr.dest, RiscV.Instr.value, RiscV.ImmOp.eval]

/-! ## Loading locations into argument registers -/

section Locs

variable {S : Space} {n : Nat} (hv : S.Valid n) {N B : Nat} (hfr : FrameAt S N B)
include hv hfr

theorem loadLocsFrom_spec {fr : Frame P} :
    ∀ (locs : List (Loc P)) (j : Nat) (vals : List Word) (m : MState),
    fr.readAll locs = some vals → locsBelow N locs = true → j + locs.length ≤ 8 →
    RegsAt A fr m.core → SlotsAt N m.memory B fr → m.core.read sp = BitVec.ofNat 64 B →
    ∃ m', runSeq (loadLocsFrom A.reg j locs) m = some m' ∧ m'.memory = m.memory ∧
      (∀ k (h : k < vals.length), m'.core.read (argRegN (j + k)) = vals[k]) ∧
      (∀ r, (∀ k < locs.length, r ≠ argRegN (j + k)) → m'.core.read r = m.core.read r)
  | [], j, vals, m, h, _, _, _, _, _ => by
    simp only [Frame.readAll, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨m, rfl, rfl, fun k h => by simp at h, fun _ _ => rfl⟩
  | l :: ls, j, vals, m, h, hbel, hlen, hregs, hslots, hsp => by
    obtain ⟨x, xs, hx, hxs, rfl⟩ := readAll_cons h
    have hj : j < 8 := by simp at hlen; omega
    have hbel' : locsBelow N ls = true := by
      simp only [locsBelow, List.all_cons, Bool.and_eq_true] at hbel ⊢; exact hbel.2
    -- the first location
    obtain ⟨m₁, h₁, mem₁, v₁, fr₁⟩ : ∃ m₁, runSeq (loadLocsFrom A.reg j (l :: ls)) m =
        runSeq (loadLocsFrom A.reg (j + 1) ls) m₁ ∧ m₁.memory = m.memory ∧
        m₁.core.read (argRegN j) = x ∧ ∀ r, r ≠ argRegN j → m₁.core.read r = m.core.read r := by
      cases l with
      | reg r =>
        refine ⟨_, mvI_step _ _ _ _, rfl, ?_, fun q hq => ?_⟩
        · rw [mvI_read, ite_true_of ⟨rfl, argRegN_ne_zero hj⟩]; exact hregs r x hx
        · rw [mvI_read, ite_false_of (fun h => hq h.1)]
      | slot k =>
        have hk : k < N := locsBelow_slot hbel List.mem_cons_self
        have := slotOff_lt hk; have := raOff_lt N
        refine ⟨_, frame_ld hv hfr (by unfold slotOff; omega) (by omega) hsp (hslots k x hk hx), rfl,
          ?_, fun q hq => ?_⟩
        · simp only [State.read_setPc]; exact State.read_write_same _ _ _ (argRegN_ne_zero hj)
        · simp only [State.read_setPc]; exact State.read_write_other _ _ _ _ hq
    have hregs₁ : RegsAt A fr m₁.core := hregs.congr A fun p =>
      fr₁ _ fun e => argRegN_ne_alloc hj (A.idx p) e.symm
    obtain ⟨m', h', mem', vals', fr'⟩ := loadLocsFrom_spec ls (j + 1) xs m₁ hxs hbel'
      (by simp at hlen; omega) hregs₁ (mem₁ ▸ hslots)
      (by rw [fr₁ sp (argRegN_ne_sp hj).symm]; exact hsp)
    refine ⟨m', by rw [h₁]; exact h', mem'.trans mem₁, fun k hk => ?_, fun r hr => ?_⟩
    · cases k with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [fr' _ fun k hk' => argRegN_ne hj (by simp at hlen; omega) (by omega)]
        exact v₁
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [← vals' k (by simpa using hk)]
        congr 2; omega
    · rw [fr' r fun k hk => by
        have := hr (k + 1) (by simp; omega); rwa [show j + (k + 1) = j + 1 + k by omega] at this]
      exact fr₁ r (by have := hr 0 (by simp); simpa using this)

theorem storeLocsFrom_spec [DecidableEq P] :
    ∀ (locs : List (Loc P)) (j : Nat) (vals : List Word) (fr fr' : Frame P) (m : MState),
    fr.writeAll locs vals = some fr' → locsBelow N locs = true → j + locs.length ≤ 8 →
    (∀ k (h : k < vals.length), m.core.read (argRegN (j + k)) = vals[k]) →
    RegsAt A fr m.core → SlotsAt N m.memory B fr → m.core.read sp = BitVec.ofNat 64 B →
    m.memory.regions = S.regions n →
    ∃ m', runSeq (storeLocsFrom A.reg j locs) m = some m' ∧ RegsAt A fr' m'.core ∧
      SlotsAt N m'.memory B fr' ∧ WritesIn m.memory m'.memory (B + slotOff 0) (B + raOff N) ∧
      (∀ r, (∀ p, r ≠ A.reg p) → m'.core.read r = m.core.read r)
  | [], j, [], fr, fr', m, h, _, _, _, hregs, hslots, _, _ => by
    cases h
    exact ⟨m, rfl, hregs, hslots, WritesIn.refl _ _ _, fun _ _ => rfl⟩
  | [], _, _ :: _, _, _, _, h, _, _, _, _, _, _, _ => by cases h
  | _ :: _, _, [], _, _, _, h, _, _, _, _, _, _, _ => by cases h
  | l :: ls, j, v :: vs, fr, fr', m, h, hbel, hlen, hargs, hregs, hslots, hsp, hr => by
    simp only [Frame.writeAll] at h
    have hj : j < 8 := by simp at hlen; omega
    have hbel' : locsBelow N ls = true := by
      simp only [locsBelow, List.all_cons, Bool.and_eq_true] at hbel ⊢; exact hbel.2
    have hv0 : m.core.read (argRegN j) = v := by
      have := hargs 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at this
      exact this
    have hlv := writeAll_length h
    have hra := raOff_lt N
    obtain ⟨m₁, h₁, regs₁, slots₁, wi₁, fr₁⟩ : ∃ m₁, runSeq (storeLocsFrom A.reg j (l :: ls)) m =
        runSeq (storeLocsFrom A.reg (j + 1) ls) m₁ ∧ RegsAt A (fr.write l v) m₁.core ∧
        SlotsAt N m₁.memory B (fr.write l v) ∧
        WritesIn m.memory m₁.memory (B + slotOff 0) (B + raOff N) ∧
        ∀ r, (∀ p, r ≠ A.reg p) → m₁.core.read r = m.core.read r := by
      cases l with
      | reg r =>
        refine ⟨_, mvI_step _ _ _ _, fun r' x hx => ?_, ?_, WritesIn.refl _ _ _, fun q hq => ?_⟩
        · simp only [Frame.write, Frame.regs_set] at hx
          rw [mvI_read]
          by_cases e : r' = r
          · subst e
            simp only [ite_true, Option.some.injEq] at hx
            rw [ite_true_of ⟨rfl, A.reg_ne_zero r'⟩, hv0, hx]
          · rw [ite_false_of (fun h => e (A.reg_injective h.1))]
            simp only [e, ite_false] at hx
            exact hregs r' x hx
        · intro k x hk hx
          exact hslots k x hk (by simpa [Frame.write] using hx)
        · rw [mvI_read, ite_false_of (fun h => hq r h.1)]
      | slot k =>
        have hk : k < N := locsBelow_slot hbel List.mem_cons_self
        have := slotOff_lt hk
        obtain ⟨mem₁, hrun, hw₁, hwi₁⟩ := frame_sd hv hfr (r := argRegN j) (off := slotOff k)
          (rest := storeLocsFrom A.reg (j + 1) ls) (m := m) (by unfold slotOff; omega) (by omega) hr hsp
        refine ⟨_, hrun, fun r' x hx => ?_, fun k' x hk' hx => ?_,
          hwi₁.mono (by unfold slotOff; omega) (by omega), fun q _ => rfl⟩
        · simp only [Frame.write, Frame.regs_setSlot] at hx
          exact hregs r' x hx
        · simp only [Frame.write, Frame.slots_setSlot] at hx
          by_cases e : k' = k
          · subst e
            simp only [ite_true, Option.some.injEq] at hx
            subst hx
            rw [hv0] at hw₁; exact hw₁
          · simp only [e, ite_false] at hx
            apply hwi₁.wordAt _ (hslots k' x hk' hx)
            unfold slotOff
            have : k' ≠ k := e
            omega
    have hargs₁ : ∀ k (h : k < vs.length), m₁.core.read (argRegN (j + 1 + k)) = vs[k] := by
      intro k hk
      rw [fr₁ _ fun p e => argRegN_ne_alloc (by simp at hlen; omega) (A.idx p) e]
      have := hargs (k + 1) (by simp; omega)
      have := hargs (k + 1) (by simp; omega)
      simpa [show j + (k + 1) = j + 1 + k by omega] using this
    obtain ⟨m', h', regs', slots', wi', fr'⟩ := storeLocsFrom_spec ls (j + 1) vs (fr.write l v) fr' m₁
      h hbel' (by simp at hlen; omega) hargs₁ regs₁ slots₁
      (by rw [fr₁ sp fun p e => A.reg_ne_sp p e.symm]; exact hsp) (wi₁.1.trans hr)
    exact ⟨m', by rw [h₁]; exact h', regs', slots', wi₁.trans wi',
      fun r hr' => (fr' r hr').trans (fr₁ r hr')⟩

end Locs

end Silmaril.RiscV.Backend
