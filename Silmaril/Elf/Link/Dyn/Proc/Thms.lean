module

public import Silmaril.Elf.Link.Dyn.Proc.Defs
public import Silmaril.X86.RelIsa.Thms
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.BlockCert9.Thms
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

/-! # The process machine: proof rules

PROVED (standard axioms):

* `must_insn`: one `Open9` instruction of the executable's image, in weakest-precondition form
  (`WP` of its `Ext9.exec` result);
* `must_contract`: a library step whose contract's precondition holds;
* `extStep_gate`, `extStep_fn`, `extStep_res`: which contract applies at an address;
* `must_done`: an ended process satisfying the goal;
* `Keeps.readWith`, `Keeps.trans`, `keeps_of_writesOnly`: frames: reads of kept addresses are
  unchanged.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Proc

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.RelIsa (Res Must)
open Silmaril.X86.Ext (Loaded)

/-- The weakest precondition of an instruction's result. -/
def WP : Silmaril.X86.Ext.Result → (State → Memory → Prop) → Prop
  | .ok c m, P => P c m
  | _, _ => False

@[simp] theorem WP_ok (c : State) (m : Memory) (P : State → Memory → Prop) :
    WP (.ok c m) P = P c m := rfl

abbrev MustQ (W : World) (Q : PState → Prop) (s : PState) : Prop :=
  Must (proc W) (fun _ => True) Q s

theorem must_done {W : World} {Q : PState → Prop} {s : PState} (h : Q s) : MustQ W Q s :=
  .done h

/-- **One instruction of the executable.** -/
theorem must_insn {W : World} {Q : PState → Prop} {s : PState} {base : Word}
    {code : List Byte} {o l : Nat} {i : Silmaril.X86.Ext9.Instr} (hd : s.g.done = none)
    (hin : W.InImage s.m.core.rip.toNat) (hl : Loaded s.m.memory base code)
    (hrip : s.m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : Silmaril.X86.Open9.decode ((code.drop o).take l) = some (i, l))
    (h : WP (Silmaril.X86.Ext9.exec i s.m.core s.m.memory l)
      fun c m => MustQ W Q ⟨⟨c, m⟩, s.g⟩) : MustQ W Q s := by
  revert h
  cases e : Silmaril.X86.Ext9.exec i s.m.core s.m.memory l with
  | ok c m =>
    intro h
    have hs : Silmaril.X86.Open9.step s.m = some ⟨c, m⟩ :=
      Silmaril.X86.Open9.step_of_listed hl hrip hfit hdec e
    refine Must.step trivial ?_ ?_
    · intro hstop
      simp only [proc, step, hd, hin, ↓reduceIte, hs] at hstop
      cases hstop
    · intro t ht
      simp only [proc, step, hd, hin, ↓reduceIte, hs, Res.ok.injEq] at ht
      subst ht
      exact h
  | _ => intro h; exact h.elim

/-- **A library step under its contract's precondition.** -/
theorem must_contract {W : World} {Q : PState → Prop} {s : PState} {pre : Prop}
    {post : PState → Prop} (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hx : ∀ r, extStep W s r ↔ Contract pre post r) (hpre : pre)
    (h : ∀ t, post t → MustQ W Q t) : MustQ W Q s := by
  have hstep : ∀ r, (proc W).step s r ↔ Contract pre post r := by
    intro r
    simp only [proc, step, hd, hout, ↓reduceIte]
    exact hx r
  refine Must.step trivial ?_ ?_
  · intro hstop
    obtain ⟨t, ht, _⟩ := (hstep _).1 hstop hpre
    cases ht
  · intro t ht
    obtain ⟨t', ht', hp⟩ := (hstep _).1 ht hpre
    cases ht'
    exact h t hp

theorem extStep_gate {W : World} {s : PState} (h : s.m.core.rip = W.gate) (r : Res PState) :
    extStep W s r ↔ gateStep W s r := by
  simp [extStep, h]

theorem extStep_fn {W : World} {s : PState} {f : Fn} (hg : s.m.core.rip ≠ W.gate)
    (hres : ∀ res slots, W.lazy = some (res, slots) → s.m.core.rip ≠ res)
    (hf : W.fns.find? (·.1 == s.m.core.rip) = some (s.m.core.rip, f)) (r : Res PState) :
    extStep W s r ↔ fnStep W f s r := by
  unfold extStep
  simp only [hg, ↓reduceIte]
  cases e : W.lazy with
  | none => simp [hf]
  | some p =>
    obtain ⟨res, slots⟩ := p
    simp [hres res slots e, hf]

theorem extStep_res {W : World} {s : PState} {res : Word} {slots : List (Nat × Word)}
    (hg : s.m.core.rip ≠ W.gate) (hl : W.lazy = some (res, slots)) (h : s.m.core.rip = res)
    (r : Res PState) : extStep W s r ↔ resolveStep W slots s r := by
  unfold extStep
  simp only [hg, ↓reduceIte, hl]
  simp [h]

/-! ## Frames -/

theorem Keeps.refl (P : Nat → Prop) (m : Memory) : Keeps P m m := fun _ _ => ⟨rfl, fun _ => rfl⟩

theorem Keeps.trans {P : Nat → Prop} {m₁ m₂ m₃ : Memory} (h₁ : Keeps P m₁ m₂)
    (h₂ : Keeps P m₂ m₃) : Keeps P m₁ m₃ := fun a ha =>
  ⟨(h₂ a ha).1.trans (h₁ a ha).1, fun acc => ((h₂ a ha).2 acc).trans ((h₁ a ha).2 acc)⟩

theorem Keeps.mono {P P' : Nat → Prop} {m m' : Memory} (h : Keeps P m m')
    (hP : ∀ a, P' a → P a) : Keeps P' m m' := fun a ha => h a (hP a ha)

theorem readBacking_congr' {first second : Silmaril.Process.ByteMemory} {address length : Nat}
    (h : ∀ offset < length, first.get? (address + offset) = second.get? (address + offset)) :
    Memory.readBacking first address length = Memory.readBacking second address length :=
  Memory.readBacking_congr h

/-- A read of kept addresses is unchanged. -/
theorem Keeps.readWith {P : Nat → Prop} {m m' : Memory} (h : Keeps P m m') {acc : Access}
    {a len : Nat} (hP : ∀ k < len, P (a + k)) : m'.readWith acc a len = m.readWith acc a len := by
  unfold Memory.readWith
  have hc : m'.checkSpan acc a len = m.checkSpan acc a len := by
    unfold Memory.checkSpan
    congr 1
    simp only [List.all_eq, decide_eq_decide]
    constructor <;> intro hall k hk
    · rw [← (h (a + k) (hP k (List.mem_range.mp hk))).2 acc]; exact hall k hk
    · rw [(h (a + k) (hP k (List.mem_range.mp hk))).2 acc]; exact hall k hk
  rw [hc, Memory.readBacking_congr (fun k hk => (h (a + k) (hP k hk)).1)]

theorem Keeps.readBytes {P : Nat → Prop} {m m' : Memory} (h : Keeps P m m') {a len : Nat}
    (hP : ∀ k < len, P (a + k)) : m'.readBytes a len = m.readBytes a len := h.readWith hP

theorem Keeps.fetchBytes {P : Nat → Prop} {m m' : Memory} (h : Keeps P m m') {a len : Nat}
    (hP : ∀ k < len, P (a + k)) : m'.fetchBytes a len = m.fetchBytes a len := h.readWith hP

/-- A write elsewhere keeps `P`. -/
theorem keeps_of_writesOnly {m m' : Memory} {a len : Nat} (h : Memory.WritesOnly m m' a len)
    {P : Nat → Prop} (hP : ∀ x, P x → x < a ∨ a + len ≤ x) : Keeps P m m' := by
  intro x hx
  refine ⟨h.2 x (hP x hx), fun acc => ?_⟩
  unfold Memory.permits; rw [h.1]

/-! ## Instruction listings, addresses, the stack -/

/-- **One listed instruction** (`listingOk`), looked up by offset. -/
theorem must_listed {W : World} {Q : PState → Prop} {s : PState} {base : Word}
    {code : List Byte} {L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)} {o l : Nat}
    {i : Silmaril.X86.Ext9.Instr} (hL : listingOk code L = true) (hlk : L.lookup o = some (i, l))
    (hd : s.g.done = none)
    (hin : W.InImage s.m.core.rip.toNat) (hl : Loaded s.m.memory base code)
    (hrip : s.m.core.rip = base + BitVec.ofNat 64 o)
    (h : WP (Silmaril.X86.Ext9.exec i s.m.core s.m.memory l)
      fun c m => MustQ W Q ⟨⟨c, m⟩, s.g⟩) : MustQ W Q s := by
  have hm : (o, i, l) ∈ L := by
    clear hL h
    induction L with
    | nil => cases hlk
    | cons e L ih =>
      obtain ⟨o', x⟩ := e
      simp only [List.lookup_cons] at hlk
      by_cases he : o = o'
      · subst he; simp at hlk; subst hlk; simp
      · have : (o == o') = false := by simpa using he
        rw [this] at hlk
        exact List.mem_cons_of_mem _ (ih hlk)
  have := List.all_eq_true.mp hL _ hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact must_insn hd hin hl hrip this.2 this.1 h

@[simp] theorem ripadd (b : Word) (n m : Nat) :
    b + BitVec.ofNat 64 n + BitVec.ofNat 64 m = b + BitVec.ofNat 64 (n + m) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem perm_room {W : World} {mem : Memory} {sp : Word} (h : StackRoom W mem sp)
    {acc : Access} (hacc : acc = .read ∨ acc = .write) {a len : Nat}
    (hlo : sp.toNat - 4096 ≤ a) (hhi : a + len ≤ sp.toNat + 8) : mem.Permitted acc a len := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [Memory.Permitted, Memory.checkSpan_iff]
  simp only [Silmaril.Process.addressLimit]
  refine ⟨by omega, by omega, fun k hk => ?_⟩
  rcases hacc with rfl | rfl
  · exact (h3 (a + k) (by omega) (by omega)).1
  · exact (h3 (a + k) (by omega) (by omega)).2.1

theorem pushWord_mem {c : State} {m : Memory} {v : Word}
    (h : m.Permitted .write (c.read .rsp - 8#64).toNat 8) :
    Silmaril.X86.pushWord c m v = some (c.write .rsp (c.read .rsp - 8#64), pushMem m (c.read .rsp) v) :=
  Silmaril.X86.pushWord_eq_some h

@[simp] theorem pushMem_regions (m : Memory) (sp v : Word) : (pushMem m sp v).regions = m.regions :=
  rfl

theorem pushMem_permits (m : Memory) (sp v : Word) (acc : Access) (a : Nat) :
    (pushMem m sp v).permits acc a = m.permits acc a := rfl

theorem pushMem_keeps {m : Memory} {sp v : Word} {P : Nat → Prop}
    (hP : ∀ x, P x → x < (sp - 8#64).toNat ∨ (sp - 8#64).toNat + 8 ≤ x) :
    Keeps P m (pushMem m sp v) := by
  intro x hx
  refine ⟨?_, fun _ => rfl⟩
  simp only [pushMem]
  exact Memory.install_outside m.bytes _ _ x (by simpa using hP x hx)

theorem pushMem_read {m : Memory} {sp v : Word}
    (h : m.Permitted .read (sp - 8#64).toNat 8) (hw : m.Permitted .write (sp - 8#64).toNat 8) :
    (pushMem m sp v).readBytes (sp - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [v]) := by
  have hp := Silmaril.X86.pushWord_eq_some (s := (Silmaril.X86.State.mk (fun _ => sp) 0 ⟨none, none, none, none, none, none⟩ 0))
    (memory := m) (value := v) (by simpa [Silmaril.X86.State.read] using hw)
  have := Silmaril.X86.pushWord_readBytes hp (by simpa [Silmaril.X86.State.read] using h)
  simpa [Silmaril.X86.State.read, pushMem] using this

theorem StackRoom.pushMem {W : World} {m : Memory} {sp sp' v : Word} (h : StackRoom W m sp) :
    StackRoom W (pushMem m sp' v) sp := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun a ha hb => by simpa [pushMem_permits] using h3 a ha hb⟩

/-! ## Symbolic execution normal forms

The register file is kept as a chain of `RegisterFile.write`s on the entry core's registers,
reads are folded back to `State.read`, and rip-relative addresses become `base + offset`. -/

@[simp] theorem st_write_regs (c : State) (r : Reg) (v : Word) :
    (c.write r v).regs = c.regs.write r v := rfl

@[simp] theorem st_read_mk (R : Silmaril.Machine.RegisterFile Reg Word) (rip : Word)
    (f : Silmaril.X86.Flags) (fs : Word) (r : Reg) : State.read ⟨R, rip, f, fs⟩ r = R r := rfl

@[simp] theorem st_regs_apply (c : State) (r : Reg) : c.regs r = c.read r := rfl

theorem resultN_add {x y : Word} : Silmaril.X86.Ext.AluOp.resultN .add x y = x + y := rfl
theorem resultN_sub {x y : Word} : Silmaril.X86.Ext.AluOp.resultN .sub x y = x - y := rfl
theorem resultN_and {x y : Word} : Silmaril.X86.Ext.AluOp.resultN .and x y = x &&& y := rfl

@[simp] theorem ofRip_addr (d : BitVec 32) (c : State) (next : Word) :
    (Silmaril.X86.Ext.Mem.ofRip d).addr c next = next + d.signExtend 64 := by
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip, Silmaril.X86.Ext.Base.value]

/-- Evaluate one instruction's `WP` in the normal form above. -/
syntax "xstep" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| xstep []) => `(tactic|
      x9_simp [WP_ok, resultN_add, resultN_sub, resultN_and, BitVec.sub_add_cancel, ofRip_addr, st_write_regs, st_read_mk, st_regs_apply, ripadd,
        Silmaril.X86.Ext.Sz.bytes, Silmaril.Machine.RegisterFile.write_same])
  | `(tactic| xstep [$ls,*]) => `(tactic|
      x9_simp [$ls,*, WP_ok, resultN_add, resultN_sub, resultN_and, BitVec.sub_add_cancel, ofRip_addr, st_write_regs, st_read_mk, st_regs_apply, ripadd,
        Silmaril.X86.Ext.Sz.bytes, Silmaril.Machine.RegisterFile.write_same])

/-- `(sp - k).toNat`, without wrapping. -/
theorem sub_toNat {sp : Word} {k : Nat} (h : k ≤ sp.toNat) (hk : k < 2 ^ 64) :
    (sp - BitVec.ofNat 64 k).toNat = sp.toNat - k := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]; exact h)]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

theorem add_toNat {sp : Word} {k : Nat} (h : sp.toNat + k < 2 ^ 64) :
    (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

/-- `rsp & -16` on an aligned stack after `pop`. -/
theorem and16 {x : Word} (h : x.toNat % 16 = 0) (h8 : x.toNat + 8 < 2 ^ 64) :
    (x + 8#64) &&& 18446744073709551600#64 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have e : (x + 8#64).toNat = x.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  rw [e]
  obtain ⟨q, hq⟩ : ∃ q, x.toNat = 16 * q := ⟨x.toNat / 16, by omega⟩
  rw [hq]
  have hq' : q < 2 ^ 60 := by have := x.isLt; omega
  simp only [BitVec.toNat_ofNat]
  apply Nat.eq_of_testBit_eq
  intro i
  have h0 := Nat.testBit_two_pow_mul_add (b := 0) (i := 4) q (by norm_num) i
  rw [Nat.testBit_and, show 16 * q + 8 = 2 ^ 4 * q + 8 by norm_num, show 16 * q = 2 ^ 4 * q + 0 by norm_num,
    Nat.testBit_two_pow_mul_add _ (by norm_num : 8 < 2 ^ 4), h0]
  by_cases hi : i < 4
  · simp only [hi, ↓reduceIte, Nat.zero_testBit]
    interval_cases i <;> decide
  · simp only [hi, ↓reduceIte]
    by_cases h64 : i < 64
    · have : (18446744073709551600 % 2 ^ 64).testBit i = true := by
        interval_cases i <;> decide
      rw [this, Bool.and_true]
    · have : q.testBit (i - 4) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hq' (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [this, Bool.false_and]

/-! ## The library's steps at the gate and at entry points -/

section Gate

variable {W : World} {Q : PState → Prop} {s : PState}

theorem gate_call (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {f a1 a2 a3 : Word} {js : List Job}
    (hj : s.g.jobs = .call f a1 a2 a3 :: js)
    (k : ∀ t, Enters W s t f → t.m.core.read .rdi = a1 → t.m.core.read .rsi = a2 →
      t.m.core.read .rdx = a3 → t.g = { s.g with jobs := js } → MustQ W Q t) : MustQ W Q s :=
  must_contract hd hout (fun r => by rw [extStep_gate hrip]; simp only [gateStep, hj]) trivial
    (post := fun t => Enters W s t f ∧ t.m.core.read .rdi = a1 ∧ t.m.core.read .rsi = a2 ∧
      t.m.core.read .rdx = a3 ∧ t.g = { s.g with jobs := js })
    fun t ⟨h1, h2, h3, h4, h5⟩ => k t h1 h2 h3 h4 h5

theorem gate_call0 (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {f : Word} {js : List Job} (hj : s.g.jobs = .call0 f :: js)
    (k : ∀ t, Enters W s t f → t.g = { s.g with jobs := js } → MustQ W Q t) : MustQ W Q s :=
  must_contract hd hout (fun r => by rw [extStep_gate hrip]; simp only [gateStep, hj]) trivial
    (post := fun t => Enters W s t f ∧ t.g = { s.g with jobs := js } ∧ W.atCall t ∧ W.atGate s t)
    fun t ⟨h1, h2, _⟩ => k t h1 h2

/-- `gate_call0` with the library's guarantee at the callback's entry (`World.atCall`). -/
theorem gate_call0' (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {f : Word} {js : List Job} (hj : s.g.jobs = .call0 f :: js)
    (k : ∀ t, Enters W s t f → t.g = { s.g with jobs := js } → W.atCall t → MustQ W Q t) : MustQ W Q s :=
  must_contract hd hout (fun r => by rw [extStep_gate hrip]; simp only [gateStep, hj]) trivial
    (post := fun t => Enters W s t f ∧ t.g = { s.g with jobs := js } ∧ W.atCall t ∧ W.atGate s t)
    fun t ⟨h1, h2, h3, _⟩ => k t h1 h2 h3

/-- `gate_call0'` with the library's guarantee across the gate (`World.atGate`). -/
theorem gate_call0G (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {f : Word} {js : List Job} (hj : s.g.jobs = .call0 f :: js)
    (k : ∀ t, Enters W s t f → t.g = { s.g with jobs := js } → W.atCall t → W.atGate s t → MustQ W Q t) :
    MustQ W Q s :=
  must_contract hd hout (fun r => by rw [extStep_gate hrip]; simp only [gateStep, hj]) trivial
    (post := fun t => Enters W s t f ∧ t.g = { s.g with jobs := js } ∧ W.atCall t ∧ W.atGate s t)
    fun t ⟨h1, h2, h3, h4⟩ => k t h1 h2 h3 h4

theorem gate_main (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {f a1 a2 a3 : Word} {js : List Job}
    (hj : s.g.jobs = .main f a1 a2 a3 :: js)
    (k : ∀ t, Enters W s t f → t.m.core.read .rdi = a1 → t.m.core.read .rsi = a2 →
      t.m.core.read .rdx = a3 → t.g = { s.g with jobs := .exitRax :: js } → MustQ W Q t) :
    MustQ W Q s :=
  must_contract hd hout (fun r => by rw [extStep_gate hrip]; simp only [gateStep, hj]) trivial
    (post := fun t => Enters W s t f ∧ t.m.core.read .rdi = a1 ∧ t.m.core.read .rsi = a2 ∧
      t.m.core.read .rdx = a3 ∧ t.g = { s.g with jobs := .exitRax :: js } ∧ W.atMain t)
    fun t ⟨h1, h2, h3, h4, h5, _⟩ => k t h1 h2 h3 h4 h5

/-- `gate_main`, also passing what the library guarantees at `main`'s entry (`World.atMain`). -/
theorem gate_main' (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {f a1 a2 a3 : Word} {js : List Job}
    (hj : s.g.jobs = .main f a1 a2 a3 :: js)
    (k : ∀ t, Enters W s t f → t.m.core.read .rdi = a1 → t.m.core.read .rsi = a2 →
      t.m.core.read .rdx = a3 → t.g = { s.g with jobs := .exitRax :: js } → W.atMain t →
      MustQ W Q t) :
    MustQ W Q s :=
  must_contract hd hout (fun r => by rw [extStep_gate hrip]; simp only [gateStep, hj]) trivial
    (post := fun t => Enters W s t f ∧ t.m.core.read .rdi = a1 ∧ t.m.core.read .rsi = a2 ∧
      t.m.core.read .rdx = a3 ∧ t.g = { s.g with jobs := .exitRax :: js } ∧ W.atMain t)
    fun t ⟨h1, h2, h3, h4, h5, h6⟩ => k t h1 h2 h3 h4 h5 h6

/-- `main` has returned: the library flushes `stdout`'s pending bytes and starts `exit`. -/
theorem gate_exitRax' (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {js : List Job} (hj : s.g.jobs = .exitRax :: js)
    (k : ∀ t p, W.pending s p → AtGate W s t →
      t.g = { s.g with jobs := [.exit ((low32 (s.m.core.read .rax)).setWidth 64)], out := s.g.out ++ p } → MustQ W Q t) :
    MustQ W Q s :=
  must_contract hd hout (fun r => by rw [extStep_gate hrip]; simp only [gateStep, hj]) trivial
    (post := fun t => ∃ p, W.pending s p ∧ AtGate W s t ∧
      t.g = { s.g with jobs := [.exit ((low32 (s.m.core.read .rax)).setWidth 64)], out := s.g.out ++ p } ∧
      W.atGate s t)
    fun t ⟨p, h1, h2, h3, _⟩ => k t p h1 h2 h3

/-- `gate_exitRax'` with the library's guarantee across the gate (`World.atGate`). -/
theorem gate_exitRaxG' (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {js : List Job} (hj : s.g.jobs = .exitRax :: js)
    (k : ∀ t p, W.pending s p → AtGate W s t →
      t.g = { s.g with jobs := [.exit ((low32 (s.m.core.read .rax)).setWidth 64)], out := s.g.out ++ p } →
      W.atGate s t → MustQ W Q t) :
    MustQ W Q s :=
  must_contract hd hout (fun r => by rw [extStep_gate hrip]; simp only [gateStep, hj]) trivial
    (post := fun t => ∃ p, W.pending s p ∧ AtGate W s t ∧
      t.g = { s.g with jobs := [.exit ((low32 (s.m.core.read .rax)).setWidth 64)], out := s.g.out ++ p } ∧
      W.atGate s t)
    fun t ⟨p, h1, h2, h3, h4⟩ => k t p h1 h2 h3 h4

/-- `gate_exitRax'` for a world whose library buffers nothing (the default `pending`). -/
theorem gate_exitRax (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {js : List Job} (hj : s.g.jobs = .exitRax :: js)
    (k : ∀ t, AtGate W s t →
      t.g = { s.g with jobs := [.exit ((low32 (s.m.core.read .rax)).setWidth 64)] } → MustQ W Q t)
    (hpend : ∀ s p, W.pending s p → p = [] := by intro _ _ h; exact h) :
    MustQ W Q s :=
  gate_exitRax' hd hout hrip hj fun t p hp h1 h2 => k t h1 (by rw [hpend s p hp] at h2; simpa using h2)

/-- `gate_exitRax` with the library's guarantee across the gate (`World.atGate`). -/
theorem gate_exitRaxG (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {js : List Job} (hj : s.g.jobs = .exitRax :: js)
    (k : ∀ t, AtGate W s t →
      t.g = { s.g with jobs := [.exit ((low32 (s.m.core.read .rax)).setWidth 64)] } → W.atGate s t → MustQ W Q t)
    (hpend : ∀ s p, W.pending s p → p = [] := by intro _ _ h; exact h) :
    MustQ W Q s :=
  gate_exitRaxG' hd hout hrip hj fun t p hp h1 h2 h3 => k t h1 (by rw [hpend s p hp] at h2; simpa using h2) h3

theorem gate_exit (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {st : Word} {js : List Job} (hj : s.g.jobs = .exit st :: js)
    (k : ∀ t, AtGate W s t → t.g = { s.g with jobs := exitJobs W s.g st, atexit := [] } → MustQ W Q t) :
    MustQ W Q s :=
  must_contract hd hout (fun r => by rw [extStep_gate hrip]; simp only [gateStep, hj]) trivial
    (post := fun t => AtGate W s t ∧ t.g = { s.g with jobs := exitJobs W s.g st, atexit := [] } ∧ W.atGate s t)
    fun t ⟨h1, h2, _⟩ => k t h1 h2

/-- `gate_exit` with the library's guarantee across the gate (`World.atGate`). -/
theorem gate_exitG (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {st : Word} {js : List Job} (hj : s.g.jobs = .exit st :: js)
    (k : ∀ t, AtGate W s t → t.g = { s.g with jobs := exitJobs W s.g st, atexit := [] } → W.atGate s t →
      MustQ W Q t) :
    MustQ W Q s :=
  must_contract hd hout (fun r => by rw [extStep_gate hrip]; simp only [gateStep, hj]) trivial
    (post := fun t => AtGate W s t ∧ t.g = { s.g with jobs := exitJobs W s.g st, atexit := [] } ∧ W.atGate s t)
    fun t ⟨h1, h2, h3⟩ => k t h1 h2 h3

theorem gate_halt (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hrip : s.m.core.rip = W.gate) {st : Word} {js : List Job} (hj : s.g.jobs = .halt st :: js)
    (k : ∀ t w, w <+: s.g.out → (W.reliable = true → w = s.g.out) →
      t.g = { s.g with jobs := [], done := some (st.toNat % 256, w) } → MustQ W Q t) :
    MustQ W Q s :=
  must_contract hd hout (fun r => by rw [extStep_gate hrip]; simp only [gateStep, hj]) trivial
    (post := fun t => ∃ w, w <+: s.g.out ∧ (W.reliable = true → w = s.g.out) ∧
      t.g = { s.g with jobs := [], done := some (st.toNat % 256, w) })
    fun t ⟨w, h1, h2, h3⟩ => k t w h1 h2 h3

theorem must_fn (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hg : s.m.core.rip ≠ W.gate) (hlz : W.lazy = none) {f : Fn}
    (hf : W.fns.find? (·.1 == s.m.core.rip) = some (s.m.core.rip, f)) {pre : Prop}
    {post : PState → Prop} (hx : ∀ r, fnStep W f s r ↔ Contract pre post r) (hpre : pre)
    (k : ∀ t, post t → MustQ W Q t) : MustQ W Q s :=
  must_contract hd hout (fun r => by
    rw [extStep_fn hg (fun res slots h => by rw [hlz] at h; cases h) hf]; exact hx r) hpre k

theorem must_fn' (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hg : s.m.core.rip ≠ W.gate) (hres : ∀ res slots, W.lazy = some (res, slots) → s.m.core.rip ≠ res)
    {f : Fn} (hf : W.fns.find? (·.1 == s.m.core.rip) = some (s.m.core.rip, f)) {pre : Prop}
    {post : PState → Prop} (hx : ∀ r, fnStep W f s r ↔ Contract pre post r) (hpre : pre)
    (k : ∀ t, post t → MustQ W Q t) : MustQ W Q s :=
  must_contract hd hout (fun r => by rw [extStep_fn hg hres hf]; exact hx r) hpre k

/-- **The lazy-binding resolver** for an executable with one `JUMP_SLOT`, entered from `PLT0`
with relocation index 0. -/
theorem must_resolve (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hg : s.m.core.rip ≠ W.gate) {res : Word} {e : Nat × Word} (hl : W.lazy = some (res, [e]))
    (hrip : s.m.core.rip = res)
    (hj : Silmaril.X86.Ext.loadN s.m.memory (s.m.core.read .rsp + 8#64) 8 = some 0#64)
    (hpre : SlotRW W e s) (k : ∀ t, ResPost W e s t → MustQ W Q t) : MustQ W Q s := by
  refine must_contract hd hout (pre := SlotRW W e s) (post := ResPost W e s) (fun r => ?_) hpre k
  rw [extStep_res hg hl hrip]
  constructor
  · intro h; exact h 0 (by simpa using hj) e rfl
  · intro h j hj' e' he'
    have hj0 : j = 0 := by
      cases j with
      | zero => rfl
      | succ n => simp at he'
    subst hj0
    simp at he'
    subst he'
    exact h

end Gate

/-- `je`/`jne` after `cmp x, y`. -/
theorem eval_e_sub {n : Nat} (x y : BitVec n) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN x y) .e = some (decide (x - y = 0#n)) := by
  by_cases h : x - y = 0#n <;>
    simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.isZeroN, h]

theorem eval_ne_sub {n : Nat} (x y : BitVec n) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN x y) .ne = some (!decide (x - y = 0#n)) := by
  by_cases h : x - y = 0#n <;>
    simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.isZeroN, h,
      Silmaril.X86.Ext.kNot]

/-- The memory after a permitted `storeN`. -/
def storeMem (m : Memory) (a : Word) (k : Nat) (v : Word) : Memory :=
  ⟨m.regions, Memory.install m.bytes a.toNat (Silmaril.X86.Ext.leBytes v k)⟩

theorem storeN_ok {m : Memory} {a : Word} {k : Nat} {v : Word}
    (h : m.Permitted .write a.toNat k) :
    Silmaril.X86.Ext.storeN m a k v = some (storeMem m a k v) := by
  unfold Silmaril.X86.Ext.storeN Memory.writeBytes
  have hc : m.checkSpan .write a.toNat (Silmaril.X86.Ext.leBytes v k).length = true := by
    rw [Silmaril.X86.Ext.length_leBytes]; exact h
  simp only [hc, ↓reduceIte]
  rfl

theorem storeMem_keeps {m : Memory} {a : Word} {k : Nat} {v : Word} {P : Nat → Prop}
    (hP : ∀ x, P x → x < a.toNat ∨ a.toNat + k ≤ x) : Keeps P m (storeMem m a k v) := by
  intro x hx
  refine ⟨?_, fun _ => rfl⟩
  simp only [storeMem]
  exact Memory.install_outside m.bytes _ _ x (by simpa using hP x hx)

theorem Keeps.permitted {P : Nat → Prop} {m m' : Memory} (h : Keeps P m m') {acc : Access}
    {a len : Nat} (hP : ∀ k < len, P (a + k)) : m'.Permitted acc a len ↔ m.Permitted acc a len := by
  unfold Memory.Permitted Memory.checkSpan
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun k hk => by rw [← (h (a + k) (hP k hk)).2]; exact h2 k hk⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun k hk => by rw [(h (a + k) (hP k hk)).2]; exact h2 k hk⟩

theorem pushMem_permitted {m : Memory} {sp v : Word} {acc : Access} {a len : Nat} :
    (pushMem m sp v).Permitted acc a len ↔ m.Permitted acc a len := Iff.rfl

theorem storeMem_permitted {m : Memory} {a' : Word} {k : Nat} {v : Word} {acc : Access}
    {a len : Nat} : (storeMem m a' k v).Permitted acc a len ↔ m.Permitted acc a len := Iff.rfl

theorem keeps_img {W : World} {m m' : Memory} (h : Keeps W.Kept m m') : Keeps W.InImage m m' :=
  h.mono fun _ h => Or.inl h

/-- A C string at an address is unique. -/
theorem cstr_le {m : Memory} {a : Word} {s1 s2 : List Byte} (h1 : CStr m a s1) (h2 : CStr m a s2)
    (hl : s1.length ≤ s2.length) : s1 = s2 := by
  obtain ⟨z1, r1⟩ := h1
  obtain ⟨z2, r2⟩ := h2
  have hsub := Memory.readBytes_sub_range r2 (offset := 0) (len := s1.length + 1) (by omega) (by omega)
  simp only [Nat.add_zero, List.drop_zero] at hsub
  rw [r1] at hsub
  simp only [Option.some.injEq] at hsub
  by_cases he : s1.length = s2.length
  · have := congrArg (List.take s1.length) hsub
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_take, List.take_of_length_le (by simp)] at this
    rw [this, Nat.min_eq_left (by omega), he, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  · exfalso
    have hlt : s1.length < s2.length := by omega
    have := congrArg (fun l => l[s1.length]?) hsub
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
      List.getElem?_take, show s1.length < s1.length + 1 by omega, ↓reduceIte,
      List.getElem?_append_left hlt] at this
    exact z2 _ (List.mem_of_getElem? this.symm) rfl

theorem cstr_unique {m : Memory} {a : Word} {s1 s2 : List Byte} (h1 : CStr m a s1) (h2 : CStr m a s2) :
    s1 = s2 := by
  rcases Nat.le_total s1.length s2.length with h | h
  · exact cstr_le h1 h2 h
  · exact (cstr_le h2 h1 h).symm

end Silmaril.Elf.Link.Dyn.Proc
