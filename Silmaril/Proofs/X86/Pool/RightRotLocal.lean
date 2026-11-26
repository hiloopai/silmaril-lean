module

public import Silmaril.Proofs.X86.Pool.RightRot
public import Silmaril.Proofs.X86.Pool.Fetch
public import Silmaril.X86.Decompile.RightRot.Defs
public import Silmaril.X86.Ext.Lemmas
public import Silmaril.X86.Sep.List.Thms

/-!
# Proofs: `right_rot` as a footprint triple (`Task.rightRotLocal`)

`rightRotLocal`: the `clang -O0` leaf `right_rot` (fifteen instructions, 37 bytes) meets
`LTripleEv openEv` with its code as the read-only context, owning `RightRot.pre` without
the code (`rrPre`), for every step index.

`run_stable` replays the run from one entry state; a footprint triple quantifies the
unowned memory again at **every** step, so the run is replayed here one instruction at a time
on an arbitrary memory that agrees with the owned fragment and the code. The cores of the run
are explicit (`k1` … `k15`, functions of the entry core, as in `run_stable`); `Inv j c h`
says that the thread is at step `j` (`c = core j`), that `h` has the domain of the entry
fragment, and which frame bytes `h` holds (`HIn`, a part of `h` satisfying an assertion).

* `lsafe_chain`: an `LSafeEv` from per-step facts, for any machine.
* `base_step`: one `Ext` instruction of `openEv`: the fetch is stable (`openFetch_stable`), the
  step is `Ext.exec`, and the footprint is `ChangesWithin` (`ext_local`).
* `fetch_at`: the fetch at an offset of the code, from the read-only code fragment.
* `step0` … `step14`, `final`; `rightRotLocal`.

The execution facts (`Ext.exec_*`, the frame arithmetic, the count lemmas, `or_shifts_eq`)
are those of `run_stable` (`Silmaril/Proofs/X86/Safe/Stable/RightRotRun.lean`), restated
for an arbitrary memory: loads read the bytes the owned fragment holds.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Pool.RightRotLocal

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Sz Count ShiftOp)
open Silmaril.Process (Memory addressLimit Permissions)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86.Decompile (Image)
open Silmaril.X86.Decompile.RightRot (code rightRotSpec)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.X86.MemEvent (ChangesWithin CoreWithin openFetch extAccesses readSet writeSet)
open Silmaril.X86.Pool
open Silmaril.Proofs.X86.Pool
open Silmaril.Proofs.X86.Pool.Example (HoldsIn bytesAt_in retFin)
open Silmaril.Proofs.X86.Pool.RightRotPool (rrPre rrPost RightRotLocal blockAny_in)

/-! ## Generic parts -/

/-- **`LSafeEv` from a chain of per-step facts** with an invariant indexed by the step. -/
theorem lsafe_chain {M : EvMachine} {Fin : State → Prop} {Q : SProp} {r : Frag}
    (Inv : Nat → State → Frag → Prop) (N : Nat)
    (hstep : ∀ j < N, ∀ c h mem, Inv j c h → Le (union h r) (toFrag ⟨c, mem⟩) →
      ¬ Fin c ∧ ∃ i k m', M.fetch mem c.rip.toNat = some (i, k) ∧
        FetchStable M mem c.rip.toNat i k ∧ InFootprint h r c.rip.toNat k (M.accesses i c k) ∧
        M.step ⟨c, mem⟩ = some m' ∧ ChangesWithin h ⟨c, mem⟩ m' ∧
        Inv (j + 1) m'.core (reval h (toFrag m')))
    (hfin : ∀ c h mem, Inv N c h → Le (union h r) (toFrag ⟨c, mem⟩) → Fin c ∧ Q h) :
    ∀ n j c h, j ≤ N → Inv j c h → LSafeEv M Fin Q r n c h
  | 0, _, _, _, _, _ => trivial
  | n + 1, j, c, h, hj, hi => fun mem hle => by
    rcases Nat.lt_or_ge j N with hlt | hge
    · obtain ⟨hnf, i, k, m', a, b, d, e, f, g⟩ := hstep j hlt c h mem hi hle
      exact .inr ⟨hnf, i, k, m', a, b, d, e, f, lsafe_chain Inv N hstep hfin n (j + 1) _ _ hlt g⟩
    · have : j = N := by omega
      subst this
      exact .inl (hfin c h mem hi hle)

/-- **One `Ext` instruction of `openEv`**: from the fetch, the footprint, the execution and the
registers it changes, the facts `LSafeEv` asks of a step. -/
theorem base_step {c c' : State} {mem mem' : Memory} {h r : Frag} {i : Silmaril.X86.Ext.Instr}
    (hf : openFetch mem c.rip.toNat = some (.base i, i.length))
    (hfoot : InFootprint h r c.rip.toNat i.length (extAccesses i c i.length))
    (hx : Silmaril.X86.Ext.exec i c mem = .ok c' mem') (hcw : CoreWithin h c c') :
    openEv.fetch mem c.rip.toNat = some (.base i, i.length) ∧
      FetchStable openEv mem c.rip.toNat (.base i) i.length ∧
      InFootprint h r c.rip.toNat i.length (openEv.accesses (.base i) c i.length) ∧
      openEv.step ⟨c, mem⟩ = some ⟨c', mem'⟩ ∧ ChangesWithin h ⟨c, mem⟩ ⟨c', mem'⟩ := by
  refine ⟨hf, openFetch_stable hf, hfoot, ?_, ?_⟩
  · show (openFetch mem c.rip.toNat).bind _ = _
    rw [hf]
    show Silmaril.X86.Open.ofResult (Silmaril.X86.Ext.exec i c mem i.length) = _
    rw [hx]; rfl
  · have hl := Silmaril.X86.MemEvent.ext_local i c i.length
    have hp := Silmaril.X86.MemEvent.Local.frame hl (m := mem) (m₁ := mem') (a := c')
      (by show Silmaril.X86.MemEvent.extView (Silmaril.X86.Ext.exec i c mem) = _; rw [hx]; rfl)
    exact Silmaril.X86.MemEvent.changesWithin_of_patched (m := ⟨c, mem⟩) (m' := ⟨c', mem'⟩)
      hp hfoot.2.2 hcw

/-- **The fetch at an offset of the code**: the canonical encoding of `i` at offset `off`. -/
theorem fetch_at {mem : Memory} {e : Word} (himg : Image code e mem) (off : Nat)
    (i : Silmaril.X86.Ext.Instr)
    (hcode : (code.drop off).take (Silmaril.X86.Ext.encode i).length = Silmaril.X86.Ext.encode i)
    (hb : off + (Silmaril.X86.Ext.encode i).length ≤ code.length) :
    openFetch mem (e.toNat + off) = some (.base i, i.length) := by
  have f := himg.slice off i hcode hb
  have hx : Silmaril.X86.Ext.fetch mem (e.toNat + off) =
      .decoded i (Silmaril.X86.Ext.encode i).length :=
    Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr ⟨_, f, Silmaril.X86.Ext.decode_encode i⟩
  have h8 := Silmaril.X86.Ext8.fetch_of_ne_undecodable (memory := mem) (address := e.toNat + off)
    (by rw [hx]; simp)
  simp only [openFetch, h8, hx]

/-! ## Parts of a fragment -/

/-- `P` holds of a part of `h`. -/
def HIn (P : SProp) (h : Frag) : Prop := ∃ f, P f ∧ Le f h

theorem HIn.le {P : SProp} {h s : Frag} (hp : HIn P h) (hl : Le h s) : HIn P s := by
  obtain ⟨f, hf, hfl⟩ := hp
  exact ⟨f, hf, fun l v e => hl l v (hfl l v e)⟩

theorem bytesAt_sub {need : Permissions → Prop} :
    ∀ {a : Nat} {bs : List Byte} {f : Frag}, bytesAt need a bs f →
      ∀ l, (f l).isSome → ∃ i < bs.length, l = .mem (a + i)
  | _, [], f, hf, l, hl => by
    have : f = Frag.empty := hf
    subst this; simp [Frag.empty] at hl
  | a, b :: bs, f, hf, l, hl => by
    obtain ⟨f₁, f₂, -, rfl, ⟨-, p, -, rfl⟩, h₂⟩ := hf
    simp only [Frag.union] at hl
    cases e : Frag.single (.mem a) (.cell ⟨some b, p⟩) l with
    | some v =>
      have := Example.single_dom l (by rw [e]; rfl)
      exact ⟨0, by simp, by rw [this]; simp⟩
    | none =>
      rw [e] at hl
      obtain ⟨i, hi, rfl⟩ := bytesAt_sub h₂ l hl
      exact ⟨i + 1, by simp; omega, by simp; omega⟩

theorem blockAny_sub : ∀ {a n : Nat} {f : Frag}, blockAny a n f →
    ∀ l, (f l).isSome → ∃ i < n, l = .mem (a + i)
  | _, 0, f, hf, l, hl => by
    have : f = Frag.empty := hf
    subst this; simp [Frag.empty] at hl
  | a, n + 1, f, hf, l, hl => by
    obtain ⟨f₁, f₂, -, rfl, ⟨-, c, -, rfl⟩, h₂⟩ := hf
    simp only [Frag.union] at hl
    cases e : Frag.single (.mem a) (.cell c) l with
    | some v =>
      have := Example.single_dom l (by rw [e]; rfl)
      exact ⟨0, by omega, by rw [this]; simp⟩
    | none =>
      rw [e] at hl
      obtain ⟨i, hi, rfl⟩ := blockAny_sub h₂ l hl
      exact ⟨i + 1, by omega, by simp; omega⟩

theorem permsAt_congr {m m' : Memory} (hr : m'.regions = m.regions) (x : Nat) :
    permsAt m' x = permsAt m x := by
  simp [permsAt, Memory.permits, hr]

/-- **A part over unchanged bytes survives a step**: re-valued at the successor, the fragment
still has a part satisfying `P`, if `P`'s parts are byte cells in `S` and the step keeps the
mapping list and the bytes of `S`. -/
theorem hin_carry {P : SProp} {h : Frag} {c c' : State} {mem mem' : Memory} (S : Nat → Prop)
    (hP : HIn P h) (hsub : ∀ f, P f → ∀ l, (f l).isSome → ∃ a, l = .mem a ∧ S a)
    (hle : Le h (toFrag ⟨c, mem⟩)) (hS : ∀ a, S a → mem'.bytes.get? a = mem.bytes.get? a)
    (hreg : mem'.regions = mem.regions) : HIn P (reval h (toFrag ⟨c', mem'⟩)) := by
  obtain ⟨f, hf, hfl⟩ := hP
  refine ⟨f, hf, fun l v e => ?_⟩
  obtain ⟨a, rfl, ha⟩ := hsub f hf l (by rw [e]; rfl)
  have hh := hfl _ v e
  have ht := hle _ v hh
  simp only [reval, hh, Option.isSome_some, ite_true]
  rw [← ht]
  simp only [toFrag, hS a ha, permsAt_congr hreg]

/-- **A part over newly written bytes**: bytes the successor's memory holds, owned by `h`. -/
theorem hin_new {need : Permissions → Prop} {h : Frag} {c' : State} {mem' : Memory}
    (a : Nat) (bs : List Byte)
    (hb : ∀ i (hi : i < bs.length), a + i < addressLimit ∧ mem'.bytes.get? (a + i) = some bs[i] ∧
      need (permsAt mem' (a + i)))
    (hdom : ∀ i < bs.length, (h (.mem (a + i))).isSome) :
    HIn (bytesAt need a bs) (reval h (toFrag ⟨c', mem'⟩)) := by
  obtain ⟨f, hf, hfl, hD⟩ := bytesAt_in ⟨c', mem'⟩ a bs hb
  refine ⟨f, hf, fun l v e => ?_⟩
  obtain ⟨i, hi, rfl⟩ := hD l (by rw [e]; rfl)
  simp only [reval, hdom i hi, ite_true]
  exact hfl _ v e

theorem reval_isSome {h s : Frag} (hs : ∀ l, (s l).isSome) (l : Loc) :
    (reval h s l).isSome = (h l).isSome := by
  unfold reval; cases e : h l <;> simp [hs l]

/-! ## The run -/

/-- The fifteen instructions, as in `run_stable`. -/
abbrev I0 : Silmaril.X86.Ext.Instr := .push .rbp
abbrev I1 : Silmaril.X86.Ext.Instr := .mov .q (.reg .rbp) .rsp
abbrev I2 : Silmaril.X86.Ext.Instr := .mov .d (.mem (Silmaril.X86.Decompile.RightRot.frame 0xFFFFFFFC)) .rdi
abbrev I3 : Silmaril.X86.Ext.Instr := .mov .d (.mem (Silmaril.X86.Decompile.RightRot.frame 0xFFFFFFF8)) .rsi
abbrev I4 : Silmaril.X86.Ext.Instr := .load .d .rax (Silmaril.X86.Decompile.RightRot.frame 0xFFFFFFFC)
abbrev I5 : Silmaril.X86.Ext.Instr := .load .d .rcx (Silmaril.X86.Decompile.RightRot.frame 0xFFFFFFF8)
abbrev I6 : Silmaril.X86.Ext.Instr := .shift .d .shr (.reg .rax) .cl
abbrev I7 : Silmaril.X86.Ext.Instr := .load .d .rdx (Silmaril.X86.Decompile.RightRot.frame 0xFFFFFFFC)
abbrev I8 : Silmaril.X86.Ext.Instr := .movI32 .rcx 0x20
abbrev I9 : Silmaril.X86.Ext.Instr :=
  .aluR .d .sub .rcx (.mem (Silmaril.X86.Decompile.RightRot.frame 0xFFFFFFF8))
abbrev I10 : Silmaril.X86.Ext.Instr := .shift .d .shl (.reg .rdx) .cl
abbrev I11 : Silmaril.X86.Ext.Instr := .mov .d (.reg .rcx) .rdx
abbrev I12 : Silmaril.X86.Ext.Instr := .alu .d .or (.reg .rax) .rcx
abbrev I13 : Silmaril.X86.Ext.Instr := .pop .rbp
abbrev I14 : Silmaril.X86.Ext.Instr := .ret

section Run
variable (c₀ : State) (ret : Word)

def k1 : State := { c₀.write .rsp (c₀.read .rsp - 8#64) with
  rip := c₀.rip + BitVec.ofNat 64 (Silmaril.X86.Insn.push Reg.rbp).length }
def k2 : State := { Sz.q.write (k1 c₀) .rbp (Sz.q.read (k1 c₀) .rsp) with
  rip := (k1 c₀).rip + BitVec.ofNat 64 I1.length }
def k3 : State := { k2 c₀ with rip := (k2 c₀).rip + BitVec.ofNat 64 I2.length }
def k4 : State := { k3 c₀ with rip := (k3 c₀).rip + BitVec.ofNat 64 I3.length }
def k5 : State := { Sz.d.write (k4 c₀) .rax (Sz.d.read c₀ .rdi) with
  rip := (k4 c₀).rip + BitVec.ofNat 64 I4.length }
def k6 : State := { Sz.d.write (k5 c₀) .rcx (Sz.d.read c₀ .rsi) with
  rip := (k5 c₀).rip + BitVec.ofNat 64 I5.length }
def k7 : State :=
  { Sz.d.write (k6 c₀) .rax (ShiftOp.shr.result (Sz.d.read (k6 c₀) .rax)
      ((Count.cl.raw (k6 c₀)).toNat % Sz.d.bits)) with
    flags := ShiftOp.shr.flags (Sz.d.read (k6 c₀) .rax) ((Count.cl.raw (k6 c₀)).toNat % Sz.d.bits)
      (k6 c₀).flags
    rip := (k6 c₀).rip + BitVec.ofNat 64 I6.length }
def k8 : State := { Sz.d.write (k7 c₀) .rdx (Sz.d.read c₀ .rdi) with
  rip := (k7 c₀).rip + BitVec.ofNat 64 I7.length }
def k9 : State := { (k8 c₀).write .rcx ((0x20 : BitVec 32).setWidth 64) with
  rip := (k8 c₀).rip + BitVec.ofNat 64 I8.length }
def k10 : State :=
  { Sz.d.write (k9 c₀) .rcx
      (Silmaril.X86.Ext.AluOp.resultN .sub (Sz.d.read (k9 c₀) .rcx) (Sz.d.read c₀ .rsi)) with
    flags := Silmaril.X86.Ext.AluOp.flagsN .sub (Sz.d.read (k9 c₀) .rcx) (Sz.d.read c₀ .rsi)
    rip := (k9 c₀).rip + BitVec.ofNat 64 I9.length }
def k11 : State :=
  { Sz.d.write (k10 c₀) .rdx (ShiftOp.shl.result (Sz.d.read (k10 c₀) .rdx)
      ((Count.cl.raw (k10 c₀)).toNat % Sz.d.bits)) with
    flags := ShiftOp.shl.flags (Sz.d.read (k10 c₀) .rdx)
      ((Count.cl.raw (k10 c₀)).toNat % Sz.d.bits) (k10 c₀).flags
    rip := (k10 c₀).rip + BitVec.ofNat 64 I10.length }
def k12 : State := { Sz.d.write (k11 c₀) .rcx (Sz.d.read (k11 c₀) .rdx) with
  rip := (k11 c₀).rip + BitVec.ofNat 64 I11.length }
def k13 : State :=
  { Sz.d.write (k12 c₀) .rax
      (Silmaril.X86.Ext.AluOp.resultN .or (Sz.d.read (k12 c₀) .rax) (Sz.d.read (k12 c₀) .rcx)) with
    flags := Silmaril.X86.Ext.AluOp.flagsN .or (Sz.d.read (k12 c₀) .rax) (Sz.d.read (k12 c₀) .rcx)
    rip := (k12 c₀).rip + BitVec.ofNat 64 I12.length }
def k14 : State := { ((k13 c₀).write .rsp ((k13 c₀).read .rsp + 8#64)).write .rbp (c₀.read .rbp) with
  rip := (k13 c₀).rip + BitVec.ofNat 64 (Silmaril.X86.Insn.pop Reg.rbp).length }
def k15 : State := { (k14 c₀).write .rsp ((k14 c₀).read .rsp + 8#64) with rip := ret }

/-- The core at step `j`. -/
def core : Nat → State
  | 0 => c₀ | 1 => k1 c₀ | 2 => k2 c₀ | 3 => k3 c₀ | 4 => k4 c₀ | 5 => k5 c₀ | 6 => k6 c₀
  | 7 => k7 c₀ | 8 => k8 c₀ | 9 => k9 c₀ | 10 => k10 c₀ | 11 => k11 c₀ | 12 => k12 c₀
  | 13 => k13 c₀ | 14 => k14 c₀ | _ => k15 c₀ ret

end Run

/-! ## The context and the invariant -/

/-- The locations the thread writes or reads: `rip`, the flags, the five registers the body
writes, and the sixteen frame bytes and the return slot. -/
def OwnLoc (sp : Word) (l : Loc) : Prop :=
  l = .rip ∨ l = .flags ∨ l = .reg .rsp ∨ l = .reg .rbp ∨ l = .reg .rax ∨ l = .reg .rcx ∨
    l = .reg .rdx ∨ ∃ i < 24, l = .mem (sp.toNat - 16 + i)

/-- The facts of the entry state, the code fragment and the owned fragment. -/
structure Ctx (e ret sp : Word) (c₀ : State) (h₀ r : Frag) : Prop where
  code : codePt e.toNat code r
  disj : Disjoint h₀ r
  own : ∀ l, OwnLoc sp l → (h₀ l).isSome
  rip0 : c₀.rip = e
  rsp0 : c₀.read .rsp = sp
  spLow : 16 ≤ sp.toNat
  spHigh : sp.toNat + 8 ≤ 2 ^ 64
  codeHigh : e.toNat + 37 ≤ 2 ^ 64
  retOut : ret.toNat < e.toNat ∨ e.toNat + 37 ≤ ret.toNat
  cpos : 0 < (Sz.d.read c₀ .rsi).toNat
  clt : (Sz.d.read c₀ .rsi).toNat < 32

/-- The four bytes `mov %edi,-0x4(%rbp)` stores. -/
def edi4 (c₀ : State) : List Byte := Silmaril.X86.Ext.leBytes ((Sz.d.read c₀ .rdi).setWidth 64) 4
/-- The four bytes `mov %esi,-0x8(%rbp)` stores. -/
def esi4 (c₀ : State) : List Byte := Silmaril.X86.Ext.leBytes ((Sz.d.read c₀ .rsi).setWidth 64) 4

/-- **The invariant at step `j`**: the core of the run, the entry fragment's domain, and the
frame bytes the fragment holds. -/
def Inv (ret sp : Word) (c₀ : State) (h₀ : Frag) (j : Nat) (c : State) (h : Frag) : Prop :=
  c = core c₀ ret j ∧ (∀ l, (h l).isSome = (h₀ l).isSome) ∧
  HIn (blockAny (sp.toNat - 16) 16) h ∧ HIn (wordPt sp.toNat ret) h ∧
  (1 ≤ j → HIn (wordPt (sp.toNat - 8) (c₀.read .rbp)) h) ∧
  (3 ≤ j → HIn (bytesPt (sp.toNat - 12) (edi4 c₀)) h) ∧
  (4 ≤ j → HIn (bytesPt (sp.toNat - 16) (esi4 c₀)) h)

/-- What `LSafeEv` asks of the step from `(c, mem)` at step `j`. -/
def StepOK (ret sp : Word) (c₀ : State) (h₀ r : Frag) (j : Nat) (c : State) (h : Frag)
    (mem : Memory) : Prop :=
  ¬ retFin ret c ∧ ∃ i k m', openEv.fetch mem c.rip.toNat = some (i, k) ∧
    FetchStable openEv mem c.rip.toNat i k ∧ InFootprint h r c.rip.toNat k (openEv.accesses i c k) ∧
    openEv.step ⟨c, mem⟩ = some m' ∧ ChangesWithin h ⟨c, mem⟩ m' ∧
    Inv ret sp c₀ h₀ (j + 1) m'.core (reval h (toFrag m'))

section Ctx
variable {e ret sp : Word} {c₀ : State} {h₀ r : Frag}

theorem Ctx.own_frame (hc : Ctx e ret sp c₀ h₀ r) {a : Nat} (h1 : sp.toNat - 16 ≤ a)
    (h2 : a < sp.toNat + 8) : (h₀ (.mem a)).isSome :=
  hc.own _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨a - (sp.toNat - 16), by omega,
    by congr 1; omega⟩)))))))

/-- What the thread reads off a state consistent with its fragment and the code. -/
theorem reads (hc : Ctx e ret sp c₀ h₀ r) {j : Nat} {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ j c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    Le h (toFrag ⟨c, mem⟩) ∧ Disjoint h r ∧ Image code e mem ∧
      mem.Permitted .write (sp.toNat - 16) 16 ∧ mem.Permitted .read (sp.toNat - 16) 16 ∧
      (∀ i < 16, RW (permsAt mem (sp.toNat - 16 + i))) ∧
      mem.readBytes sp.toNat 8 = some (encodeWords [ret]) := by
  obtain ⟨-, hdom, ⟨fb, hfb, hfbl⟩, ⟨fw, hfw, hfwl⟩, -⟩ := hi
  have hd : Disjoint h r := by
    intro l
    rcases hc.disj l with e1 | e1
    · left
      have := hdom l
      rw [e1] at this
      cases e2 : h l
      · rfl
      · rw [e2] at this; cases this
    · exact .inr e1
  have hlh : Le h (toFrag ⟨c, mem⟩) := Frag.le_of_union_left hle
  have hlr : Le r (toFrag ⟨c, mem⟩) := Frag.le_of_union_right hd hle
  have hbl : Le fb (toFrag ⟨c, mem⟩) := fun l v e => hlh l v (hfbl l v e)
  have hwl : Le fw (toFrag ⟨c, mem⟩) := fun l v e => hlh l v (hfwl l v e)
  refine ⟨hlh, hd, fetchBytes_of_codePt (by decide) hc.code hlr,
    permitted_of_blockAny (.inr rfl) (by decide) hfb hbl,
    permitted_of_blockAny (.inl rfl) (by decide) hfb hbl,
    fun i hi => (blockAny_le hfb hbl i hi).2, readBytes_of_wordPt hfw hwl⟩

/-- The footprint of an instruction at offset `off` of the code whose events lie in the frame
and the return slot. -/
theorem foot (hc : Ctx e ret sp c₀ h₀ r) {h : Frag} (hdom : ∀ l, (h l).isSome = (h₀ l).isSome)
    {off len : Nat} (hoff : off + len ≤ 37) (es : List Silmaril.X86.MemEvent.Event)
    (hes : ∀ ev ∈ es, ∀ a, ev.Covers a → sp.toNat - 16 ≤ a ∧ a < sp.toNat + 8) :
    InFootprint h r (e.toNat + off) len es := by
  have hown : ∀ a, sp.toNat - 16 ≤ a → a < sp.toNat + 8 → (h (.mem a)).isSome := by
    intro a h1 h2; rw [hdom]; exact hc.own_frame h1 h2
  refine ⟨fun j hj => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · have := bytesAt_dom hc.code (off + j) (by rw [show code.length = 37 by decide]; omega)
    rw [← Nat.add_assoc] at this
    exact Example.union_isSome_right this
  · obtain ⟨ev, hev, -, hcov⟩ := ha
    obtain ⟨h1, h2⟩ := hes ev hev a hcov
    exact Example.union_isSome_left (hown a h1 h2)
  · obtain ⟨ev, hev, -, hcov⟩ := ha
    obtain ⟨h1, h2⟩ := hes ev hev a hcov
    exact hown a h1 h2

/-- The registers an instruction may change are owned. -/
theorem coreWithin_of (hc : Ctx e ret sp c₀ h₀ r) {h : Frag}
    (hdom : ∀ l, (h l).isSome = (h₀ l).isSome) {c c' : State}
    (hregs : ∀ q : Reg, q ≠ .rsp → q ≠ .rbp → q ≠ .rax → q ≠ .rcx → q ≠ .rdx →
      c'.read q = c.read q) : CoreWithin h c c' := by
  have ho : ∀ l, OwnLoc sp l → (h l).isSome := fun l hl => by rw [hdom]; exact hc.own l hl
  refine ⟨fun q hq => ?_, fun _ => ho _ (.inl rfl), fun _ => ho _ (.inr (.inl rfl))⟩
  by_cases e1 : q = .rsp
  · subst e1; exact ho _ (.inr (.inr (.inl rfl)))
  by_cases e2 : q = .rbp
  · subst e2; exact ho _ (.inr (.inr (.inr (.inl rfl))))
  by_cases e3 : q = .rax
  · subst e3; exact ho _ (.inr (.inr (.inr (.inr (.inl rfl)))))
  by_cases e4 : q = .rcx
  · subst e4; exact ho _ (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  by_cases e5 : q = .rdx
  · subst e5; exact ho _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
  exact absurd (hregs q e1 e2 e3 e4 e5) hq

/-- **Packaging one step.** -/
theorem stepOK_of (hc : Ctx e ret sp c₀ h₀ r) {j : Nat} {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ j c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩))
    {i : Silmaril.X86.Ext.Instr} {off : Nat} {c' : State} {mem' : Memory}
    (hrip : c.rip.toNat = e.toNat + off)
    (hcode : (code.drop off).take (Silmaril.X86.Ext.encode i).length = Silmaril.X86.Ext.encode i)
    (hb : off + (Silmaril.X86.Ext.encode i).length ≤ 37)
    (hes : ∀ ev ∈ extAccesses i c i.length, ∀ a, ev.Covers a →
      sp.toNat - 16 ≤ a ∧ a < sp.toNat + 8)
    (hx : Silmaril.X86.Ext.exec i c mem = .ok c' mem')
    (hregs : ∀ q : Reg, q ≠ .rsp → q ≠ .rbp → q ≠ .rax → q ≠ .rcx → q ≠ .rdx →
      c'.read q = c.read q)
    (hinv : (∀ l, (h l).isSome = (h₀ l).isSome) →
      Inv ret sp c₀ h₀ (j + 1) c' (reval h (toFrag ⟨c', mem'⟩))) :
    StepOK ret sp c₀ h₀ r j c h mem := by
  have hdom := hi.2.1
  obtain ⟨-, -, himg, -⟩ := reads hc hi hle
  have hf : openFetch mem c.rip.toNat = some (.base i, i.length) := by
    rw [hrip]; exact fetch_at himg off i hcode (by rw [show code.length = 37 by decide]; exact hb)
  have hfoot : InFootprint h r c.rip.toNat i.length (extAccesses i c i.length) := by
    rw [hrip]; exact foot hc hdom hb _ hes
  obtain ⟨a1, a2, a3, a4, a5⟩ := base_step hf hfoot hx (coreWithin_of hc hdom hregs)
  refine ⟨fun hfin => ?_, _, _, _, a1, a2, a3, a4, a5, hinv hdom⟩
  have : c.rip.toNat = ret.toNat := by rw [hfin]
  have hlen : (Silmaril.X86.Ext.encode i).length > 0 :=
    (Silmaril.X86.Ext.decode_length (Silmaril.X86.Ext.decode_encode i)).2.1
  rcases hc.retOut with h1 | h1 <;> omega

/-- Domain of a re-valued fragment. -/
theorem dom_reval {h : Frag} (hdom : ∀ l, (h l).isSome = (h₀ l).isSome) (m : MState) :
    ∀ l, (reval h (toFrag m) l).isSome = (h₀ l).isSome := fun l => by
  rw [reval_isSome (toFrag_isSome m)]; exact hdom l

/-- The sixteen frame bytes stay readable and writable. -/
theorem hin_block {h : Frag} {c' : State} {mem' : Memory} (hc : Ctx e ret sp c₀ h₀ r)
    (hdom : ∀ l, (h l).isSome = (h₀ l).isSome)
    (hrw : ∀ i < 16, RW (permsAt mem' (sp.toNat - 16 + i))) :
    HIn (blockAny (sp.toNat - 16) 16) (reval h (toFrag ⟨c', mem'⟩)) := by
  obtain ⟨f, hf, hfl, hD⟩ := blockAny_in ⟨c', mem'⟩ (sp.toNat - 16) 16 (fun i hi =>
    ⟨by have := hc.spHigh; simp only [addressLimit]; omega, hrw i hi⟩)
  refine ⟨f, hf, fun l v e => ?_⟩
  obtain ⟨i, hi, rfl⟩ := hD l (by rw [e]; rfl)
  have : (h (.mem (sp.toNat - 16 + i))).isSome := by
    have := hc.spLow
    rw [hdom]; exact hc.own_frame (by omega) (by omega)
  simp only [reval, this, ite_true]
  exact hfl _ v e

end Ctx

/-! ## Registers along the run -/

section Regs
variable (c₀ : State) (ret : Word)
open Silmaril.X86.Decompile

theorem r1 (q : Reg) (hq : q ≠ .rsp) : (k1 c₀).read q = c₀.read q := by simp [k1, hq]
theorem r2 (q : Reg) (hq : q ≠ .rbp) : (k2 c₀).read q = (k1 c₀).read q := by
  unfold k2; rw [Silmaril.X86.Decompile.read_setRip]; exact Silmaril.X86.Ext.Sz.read_write_other _ _ _ _ _ hq
theorem r3 (q : Reg) : (k3 c₀).read q = (k2 c₀).read q := rfl
theorem r4 (q : Reg) : (k4 c₀).read q = (k3 c₀).read q := rfl
theorem r5 (q : Reg) (hq : q ≠ .rax) : (k5 c₀).read q = (k4 c₀).read q := by
  unfold k5; rw [Silmaril.X86.Decompile.read_setRip]; exact Silmaril.X86.Ext.Sz.read_write_other _ _ _ _ _ hq
theorem r6 (q : Reg) (hq : q ≠ .rcx) : (k6 c₀).read q = (k5 c₀).read q := by
  unfold k6; rw [Silmaril.X86.Decompile.read_setRip]; exact Silmaril.X86.Ext.Sz.read_write_other _ _ _ _ _ hq
theorem r7 (q : Reg) (hq : q ≠ .rax) : (k7 c₀).read q = (k6 c₀).read q := by
  unfold k7; rw [Silmaril.X86.Decompile.read_setFlagsRip]; exact Silmaril.X86.Ext.Sz.read_write_other _ _ _ _ _ hq
theorem r8 (q : Reg) (hq : q ≠ .rdx) : (k8 c₀).read q = (k7 c₀).read q := by
  unfold k8; rw [Silmaril.X86.Decompile.read_setRip]; exact Silmaril.X86.Ext.Sz.read_write_other _ _ _ _ _ hq
theorem r9 (q : Reg) (hq : q ≠ .rcx) : (k9 c₀).read q = (k8 c₀).read q := by simp [k9, hq]
theorem r10 (q : Reg) (hq : q ≠ .rcx) : (k10 c₀).read q = (k9 c₀).read q := by
  unfold k10; rw [Silmaril.X86.Decompile.read_setFlagsRip]; exact Silmaril.X86.Ext.Sz.read_write_other _ _ _ _ _ hq
theorem r11 (q : Reg) (hq : q ≠ .rdx) : (k11 c₀).read q = (k10 c₀).read q := by
  unfold k11; rw [Silmaril.X86.Decompile.read_setFlagsRip]; exact Silmaril.X86.Ext.Sz.read_write_other _ _ _ _ _ hq
theorem r12 (q : Reg) (hq : q ≠ .rcx) : (k12 c₀).read q = (k11 c₀).read q := by
  unfold k12; rw [Silmaril.X86.Decompile.read_setRip]; exact Silmaril.X86.Ext.Sz.read_write_other _ _ _ _ _ hq
theorem r13 (q : Reg) (hq : q ≠ .rax) : (k13 c₀).read q = (k12 c₀).read q := by
  unfold k13; rw [Silmaril.X86.Decompile.read_setFlagsRip]; exact Silmaril.X86.Ext.Sz.read_write_other _ _ _ _ _ hq
theorem r14 (q : Reg) (h1 : q ≠ .rsp) (h2 : q ≠ .rbp) : (k14 c₀).read q = (k13 c₀).read q := by
  simp [k14, h1, h2]
theorem r15 (q : Reg) (hq : q ≠ .rsp) : (k15 c₀ ret).read q = (k14 c₀).read q := by
  simp [k15, hq]

/-- `rsp` and `rbp` in the body: the post-push stack pointer. -/
theorem rsp_body (j : Nat) (h1 : 1 ≤ j) (h2 : j ≤ 13) :
    (core c₀ ret j).read .rsp = c₀.read .rsp - 8#64 := by
  have a1 : (k1 c₀).read .rsp = c₀.read .rsp - 8#64 := by simp [k1]
  have a2 := (r2 c₀ .rsp (by decide)).trans a1
  have a3 := (r3 c₀ .rsp).trans a2
  have a4 := (r4 c₀ .rsp).trans a3
  have a5 := (r5 c₀ .rsp (by decide)).trans a4
  have a6 := (r6 c₀ .rsp (by decide)).trans a5
  have a7 := (r7 c₀ .rsp (by decide)).trans a6
  have a8 := (r8 c₀ .rsp (by decide)).trans a7
  have a9 := (r9 c₀ .rsp (by decide)).trans a8
  have a10 := (r10 c₀ .rsp (by decide)).trans a9
  have a11 := (r11 c₀ .rsp (by decide)).trans a10
  have a12 := (r12 c₀ .rsp (by decide)).trans a11
  have a13 := (r13 c₀ .rsp (by decide)).trans a12
  match j, h1, h2 with
  | 1, _, _ => exact a1 | 2, _, _ => exact a2 | 3, _, _ => exact a3 | 4, _, _ => exact a4
  | 5, _, _ => exact a5 | 6, _, _ => exact a6 | 7, _, _ => exact a7 | 8, _, _ => exact a8
  | 9, _, _ => exact a9 | 10, _, _ => exact a10 | 11, _, _ => exact a11
  | 12, _, _ => exact a12 | 13, _, _ => exact a13

theorem rbp_body (j : Nat) (h1 : 2 ≤ j) (h2 : j ≤ 13) :
    (core c₀ ret j).read .rbp = c₀.read .rsp - 8#64 := by
  have a2 : (k2 c₀).read .rbp = c₀.read .rsp - 8#64 := by simp [k2, k1, Sz.read]
  have a3 := (r3 c₀ .rbp).trans a2
  have a4 := (r4 c₀ .rbp).trans a3
  have a5 := (r5 c₀ .rbp (by decide)).trans a4
  have a6 := (r6 c₀ .rbp (by decide)).trans a5
  have a7 := (r7 c₀ .rbp (by decide)).trans a6
  have a8 := (r8 c₀ .rbp (by decide)).trans a7
  have a9 := (r9 c₀ .rbp (by decide)).trans a8
  have a10 := (r10 c₀ .rbp (by decide)).trans a9
  have a11 := (r11 c₀ .rbp (by decide)).trans a10
  have a12 := (r12 c₀ .rbp (by decide)).trans a11
  have a13 := (r13 c₀ .rbp (by decide)).trans a12
  match j, h1, h2 with
  | 2, _, _ => exact a2 | 3, _, _ => exact a3 | 4, _, _ => exact a4
  | 5, _, _ => exact a5 | 6, _, _ => exact a6 | 7, _, _ => exact a7 | 8, _, _ => exact a8
  | 9, _, _ => exact a9 | 10, _, _ => exact a10 | 11, _, _ => exact a11
  | 12, _, _ => exact a12 | 13, _, _ => exact a13

/-- The registers the body never writes keep their entry values. -/
theorem saved (j : Nat) (q : Reg) (h1 : q ≠ .rsp) (h2 : q ≠ .rbp) (h3 : q ≠ .rax)
    (h4 : q ≠ .rcx) (h5 : q ≠ .rdx) : (core c₀ ret j).read q = c₀.read q := by
  have a1 := r1 c₀ q h1
  have a2 := (r2 c₀ q h2).trans a1
  have a3 := (r3 c₀ q).trans a2
  have a4 := (r4 c₀ q).trans a3
  have a5 := (r5 c₀ q h3).trans a4
  have a6 := (r6 c₀ q h4).trans a5
  have a7 := (r7 c₀ q h3).trans a6
  have a8 := (r8 c₀ q h5).trans a7
  have a9 := (r9 c₀ q h4).trans a8
  have a10 := (r10 c₀ q h4).trans a9
  have a11 := (r11 c₀ q h5).trans a10
  have a12 := (r12 c₀ q h4).trans a11
  have a13 := (r13 c₀ q h3).trans a12
  have a14 := (r14 c₀ q h1 h2).trans a13
  have a15 := (r15 c₀ ret q h1).trans a14
  match j with
  | 0 => rfl | 1 => exact a1 | 2 => exact a2 | 3 => exact a3 | 4 => exact a4
  | 5 => exact a5 | 6 => exact a6 | 7 => exact a7 | 8 => exact a8
  | 9 => exact a9 | 10 => exact a10 | 11 => exact a11
  | 12 => exact a12 | 13 => exact a13 | 14 => exact a14 | _ + 15 => exact a15

theorem rsp14 : (k14 c₀).read .rsp = c₀.read .rsp := by
  have := rsp_body c₀ 0 13 (by omega) (by omega)
  simp only [core] at this
  simp only [k14, read_setRip, State.read_write_other _ _ _ _ (by decide : Reg.rsp ≠ Reg.rbp),
    State.read_write_same, this]
  exact Silmaril.X86.Decompile.RightRot.sp_restore _

theorem rbp14 : (k14 c₀).read .rbp = c₀.read .rbp := by simp [k14]

end Regs

/-! ## The steps -/

section Steps
variable {e ret sp : Word} {c₀ : State} {h₀ r : Frag}
open Silmaril.X86.Decompile
open Silmaril.X86.Decompile.RightRot (frame frame_addr addr4 addr8 L0 L1 L2 L3 L4 L5 L6 L7 L8
  L9 L10 L11 L12 L13)
open Silmaril.X86.MemEvent (memEv rmEv pushEv popEv)

theorem hin_same {P : SProp} {h : Frag} {c c' : State} {mem : Memory} (hP : HIn P h)
    (hsub : ∀ f, P f → ∀ l, (f l).isSome → ∃ a, l = .mem a) (hle : Le h (toFrag ⟨c, mem⟩)) :
    HIn P (reval h (toFrag ⟨c', mem⟩)) :=
  hin_carry (fun _ => True) hP (fun f hf l hl => by
    obtain ⟨a, rfl⟩ := hsub f hf l hl; exact ⟨a, rfl, trivial⟩) hle (fun _ _ => rfl) rfl

theorem bytes_mem {need : Permissions → Prop} {a : Nat} {bs : List Byte} :
    ∀ f, bytesAt need a bs f → ∀ l, (f l).isSome → ∃ x, l = .mem x := fun f hf l hl => by
  obtain ⟨i, -, rfl⟩ := bytesAt_sub hf l hl; exact ⟨_, rfl⟩

theorem block_mem {a n : Nat} : ∀ f, blockAny a n f → ∀ l, (f l).isSome → ∃ x, l = .mem x :=
  fun f hf l hl => by obtain ⟨i, -, rfl⟩ := blockAny_sub hf l hl; exact ⟨_, rfl⟩

/-- **A step that keeps the memory** keeps every frame fact. -/
theorem inv_carry {j : Nat} {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ j c h) (hlh : Le h (toFrag ⟨c, mem⟩)) {c' : State}
    (hc' : c' = core c₀ ret (j + 1)) (h1 : j + 1 ≠ 1) (h3 : j + 1 ≠ 3) (h4 : j + 1 ≠ 4) :
    Inv ret sp c₀ h₀ (j + 1) c' (reval h (toFrag ⟨c', mem⟩)) := by
  obtain ⟨-, hdom, hb, hw, hbp, hdi, hsi⟩ := hi
  refine ⟨hc', dom_reval hdom _, hin_same hb block_mem hlh, hin_same hw bytes_mem hlh,
    fun hj => hin_same (hbp (by omega)) bytes_mem hlh,
    fun hj => hin_same (hdi (by omega)) bytes_mem hlh,
    fun hj => hin_same (hsi (by omega)) bytes_mem hlh⟩

theorem frame4 {t : State} {nxt x : Word} (ht : t.read .rbp = x - 8#64) :
    (frame 0xFFFFFFFC).addr t nxt = x - 12#64 := by rw [frame_addr, ht, addr4]

theorem frame8 {t : State} {nxt x : Word} (ht : t.read .rbp = x - 8#64) :
    (frame 0xFFFFFFF8).addr t nxt = x - 16#64 := by rw [frame_addr, ht, addr8]

theorem sub_toNat (hc : Ctx e ret sp c₀ h₀ r) {k : Nat} (hk : k ≤ 16) :
    (sp - BitVec.ofNat 64 k).toNat = sp.toNat - k :=
  toNat_sub_lit (by have := hc.spLow; omega) (by omega)

/-- The bytes a part of the fragment holds, read off a consistent memory. -/
theorem read_part {a : Nat} {bs : List Byte} {h : Frag} {c : State} {mem : Memory}
    (hne : bs ≠ []) (hP : HIn (bytesPt a bs) h) (hlh : Le h (toFrag ⟨c, mem⟩)) :
    mem.readBytes a bs.length = some bs := by
  obtain ⟨f, hf, hfl⟩ := hP
  exact readBytes_of_bytesPt (m := ⟨c, mem⟩) hne hf (fun l v e => hlh l v (hfl l v e))

theorem load_part {a : Word} {v : Word} {h : Frag} {c : State} {mem : Memory}
    (hP : HIn (bytesPt a.toNat (Silmaril.X86.Ext.leBytes v 4)) h) (hlh : Le h (toFrag ⟨c, mem⟩)) :
    Silmaril.X86.Ext.loadN mem a 4 = some (BitVec.ofNat 64 (v.toNat % 2 ^ (8 * 4))) := by
  have := read_part (by simp [Silmaril.X86.Ext.leBytes]) hP hlh
  rw [Silmaril.X86.Ext.length_leBytes] at this
  rw [Silmaril.X86.Ext.loadN_of_readBytes this, Silmaril.X86.Ext.leValue_leBytes]

/-- A part over freshly written bytes, from a `readBytes` fact. -/
theorem hin_read (hc : Ctx e ret sp c₀ h₀ r) {h : Frag} {c' : State} {mem mem' : Memory}
    (hdom : ∀ l, (h l).isSome = (h₀ l).isSome) (hreg : mem'.regions = mem.regions)
    (hrw : ∀ i < 16, RW (permsAt mem (sp.toNat - 16 + i))) {a : Nat} {bs : List Byte}
    (hrd : mem'.readBytes a bs.length = some bs) (ha : sp.toNat - 16 ≤ a)
    (hab : a + bs.length ≤ sp.toNat) :
    HIn (bytesPt a bs) (reval h (toFrag ⟨c', mem'⟩)) := by
  refine hin_new a bs (fun i hi => ⟨?_, Memory.readWith_get hrd i hi, ?_⟩) (fun i hi => ?_)
  · have := hc.spHigh; simp only [addressLimit]; omega
  · rw [permsAt_congr hreg]
    have := hrw (a + i - (sp.toNat - 16)) (by omega)
    rwa [show sp.toNat - 16 + (a + i - (sp.toNat - 16)) = a + i by omega] at this
  · rw [hdom]; exact hc.own_frame (by omega) (by have := hc.spHigh; omega)

theorem rips (hc : Ctx e ret sp c₀ h₀ r) :
    (k1 c₀).rip.toNat = e.toNat + 1 ∧ (k2 c₀).rip.toNat = e.toNat + 4 ∧
    (k3 c₀).rip.toNat = e.toNat + 7 ∧ (k4 c₀).rip.toNat = e.toNat + 10 ∧
    (k5 c₀).rip.toNat = e.toNat + 13 ∧ (k6 c₀).rip.toNat = e.toNat + 16 ∧
    (k7 c₀).rip.toNat = e.toNat + 18 ∧ (k8 c₀).rip.toNat = e.toNat + 21 ∧
    (k9 c₀).rip.toNat = e.toNat + 26 ∧ (k10 c₀).rip.toNat = e.toNat + 29 ∧
    (k11 c₀).rip.toNat = e.toNat + 31 ∧ (k12 c₀).rip.toNat = e.toNat + 33 ∧
    (k13 c₀).rip.toNat = e.toNat + 35 ∧ (k14 c₀).rip.toNat = e.toNat + 36 := by
  have hb := hc.codeHigh
  have a1 : (k1 c₀).rip.toNat = e.toNat + 1 := by
    show (c₀.rip + BitVec.ofNat 64 (Silmaril.X86.Insn.push Reg.rbp).length).toNat = _
    rw [L0]; exact rip_step (off := 0) (by rw [hc.rip0]; rfl) (by omega)
  have a2 : (k2 c₀).rip.toNat = e.toNat + 4 := by
    show ((k1 c₀).rip + BitVec.ofNat 64 I1.length).toNat = _
    rw [show I1.length = 3 from L1]; exact rip_step (off := 1) a1 (by omega)
  have a3 : (k3 c₀).rip.toNat = e.toNat + 7 := by
    show ((k2 c₀).rip + BitVec.ofNat 64 I2.length).toNat = _
    rw [show I2.length = 3 from L2]; exact rip_step (off := 4) a2 (by omega)
  have a4 : (k4 c₀).rip.toNat = e.toNat + 10 := by
    show ((k3 c₀).rip + BitVec.ofNat 64 I3.length).toNat = _
    rw [show I3.length = 3 from L3]; exact rip_step (off := 7) a3 (by omega)
  have a5 : (k5 c₀).rip.toNat = e.toNat + 13 := by
    show ((k4 c₀).rip + BitVec.ofNat 64 I4.length).toNat = _
    rw [show I4.length = 3 from L4]; exact rip_step (off := 10) a4 (by omega)
  have a6 : (k6 c₀).rip.toNat = e.toNat + 16 := by
    show ((k5 c₀).rip + BitVec.ofNat 64 I5.length).toNat = _
    rw [show I5.length = 3 from L5]; exact rip_step (off := 13) a5 (by omega)
  have a7 : (k7 c₀).rip.toNat = e.toNat + 18 := by
    show ((k6 c₀).rip + BitVec.ofNat 64 I6.length).toNat = _
    rw [show I6.length = 2 from L6]; exact rip_step (off := 16) a6 (by omega)
  have a8 : (k8 c₀).rip.toNat = e.toNat + 21 := by
    show ((k7 c₀).rip + BitVec.ofNat 64 I7.length).toNat = _
    rw [show I7.length = 3 from L7]; exact rip_step (off := 18) a7 (by omega)
  have a9 : (k9 c₀).rip.toNat = e.toNat + 26 := by
    show ((k8 c₀).rip + BitVec.ofNat 64 I8.length).toNat = _
    rw [show I8.length = 5 from L8]; exact rip_step (off := 21) a8 (by omega)
  have a10 : (k10 c₀).rip.toNat = e.toNat + 29 := by
    show ((k9 c₀).rip + BitVec.ofNat 64 I9.length).toNat = _
    rw [show I9.length = 3 from L9]; exact rip_step (off := 26) a9 (by omega)
  have a11 : (k11 c₀).rip.toNat = e.toNat + 31 := by
    show ((k10 c₀).rip + BitVec.ofNat 64 I10.length).toNat = _
    rw [show I10.length = 2 from L10]; exact rip_step (off := 29) a10 (by omega)
  have a12 : (k12 c₀).rip.toNat = e.toNat + 33 := by
    show ((k11 c₀).rip + BitVec.ofNat 64 I11.length).toNat = _
    rw [show I11.length = 2 from L11]; exact rip_step (off := 31) a11 (by omega)
  have a13 : (k13 c₀).rip.toNat = e.toNat + 35 := by
    show ((k12 c₀).rip + BitVec.ofNat 64 I12.length).toNat = _
    rw [show I12.length = 2 from L12]; exact rip_step (off := 33) a12 (by omega)
  have a14 : (k14 c₀).rip.toNat = e.toNat + 36 := by
    show ((k13 c₀).rip + BitVec.ofNat 64 (Silmaril.X86.Insn.pop Reg.rbp).length).toNat = _
    rw [L13]; exact rip_step (off := 35) a13 (by omega)
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩

/-- `push %rbp`. -/
theorem step0 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 0 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 0 c h mem := by
  obtain ⟨hlh, -, -, hW, hR, hrw, -⟩ := reads hc hi hle
  obtain rfl : c = c₀ := hi.1
  have hS := hc.spLow
  have hsp8 : (c.read .rsp - 8#64).toNat = sp.toNat - 8 := by
    rw [hc.rsp0]; exact sub_toNat hc (k := 8) (by omega)
  have hpW : mem.Permitted .write (c.read .rsp - 8#64).toNat 8 := by
    rw [hsp8]
    have hs := permitted_sub hW (off := 8) (count := 8) (by omega) (by omega)
    rwa [show sp.toNat - 16 + 8 = sp.toNat - 8 by omega] at hs
  have hpR : mem.Permitted .read (c.read .rsp - 8#64).toNat 8 := by
    rw [hsp8]
    have hs := permitted_sub hR (off := 8) (count := 8) (by omega) (by omega)
    rwa [show sp.toNat - 16 + 8 = sp.toNat - 8 by omega] at hs
  obtain ⟨mem₁, hmem₁⟩ : ∃ mm : Memory, Silmaril.X86.pushWord c mem (c.read .rbp) =
      some (c.write .rsp (c.read .rsp - 8#64), mm) := ⟨_, Silmaril.X86.pushWord_eq_some hpW⟩
  have hx : Silmaril.X86.Ext.exec I0 c mem = .ok (k1 c) mem₁ := by
    rw [Silmaril.X86.Ext.exec_push]
    simp only [Silmaril.X86.Insn.exec, hmem₁, Option.map_some]
    rfl
  have hwo := Silmaril.X86.pushWord_writesOnly hmem₁
  have hrb := Silmaril.X86.pushWord_readBytes hmem₁ hpR
  rw [hsp8] at hwo hrb
  refine stepOK_of hc hi hle (off := 0) (by rw [hc.rip0]; rfl) (by decide) (by decide) ?_ hx
    (fun q h1 _ _ _ _ => r1 c q h1) (fun hdom => ?_)
  · intro ev hev a hcov
    simp only [extAccesses, pushEv, List.mem_singleton] at hev
    subst hev
    obtain ⟨h1, h2⟩ := hcov
    simp only [hsp8] at h1 h2
    omega
  · refine ⟨rfl, dom_reval hdom _,
      hin_block hc hdom (fun i hj => by rw [permsAt_congr hwo.1]; exact hrw i hj), ?_,
      fun _ => ?_, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · exact hin_carry (fun a => sp.toNat ≤ a) hi.2.2.2.1 (fun f hf l hl => by
        obtain ⟨i, -, rfl⟩ := bytesAt_sub hf l hl; exact ⟨_, rfl, by omega⟩) hlh
        (fun a ha => hwo.2 a (.inr (by omega))) hwo.1
    · exact hin_read hc hdom hwo.1 hrw (by simpa using hrb) (by omega) (by simp; omega)

/-- `mov %rsp,%rbp`. -/
theorem step1 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 1 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 1 c h mem := by
  obtain ⟨hlh, -⟩ := reads hc hi hle
  obtain rfl : c = k1 c₀ := hi.1
  refine stepOK_of hc hi hle (off := 1) (rips hc).1 (by decide) (by decide) ?_
    (Silmaril.X86.Ext.exec_mov_reg _ mem .q .rbp .rsp)
    (fun q _ h2 _ _ _ => r2 c₀ q h2) (fun _ => inv_carry hi hlh rfl (by omega) (by omega)
      (by omega))
  intro ev hev; simp [extAccesses, rmEv] at hev

theorem szd_saved (j : Nat) (q : Reg) (h1 : q ≠ .rsp) (h2 : q ≠ .rbp) (h3 : q ≠ .rax)
    (h4 : q ≠ .rcx) (h5 : q ≠ .rdx) : Sz.d.read (core c₀ ret j) q = Sz.d.read c₀ q := by
  simp only [Sz.read, saved c₀ ret j q h1 h2 h3 h4 h5]

/-- A store of four bytes into the frame, at `[sp - k]`. -/
theorem store_frame (hc : Ctx e ret sp c₀ h₀ r) {mem : Memory} {k : Nat} (hk1 : 8 < k)
    (hk2 : k ≤ 16) (hW : mem.Permitted .write (sp.toNat - 16) 16) (v : Word) :
    ∃ mem', Silmaril.X86.Ext.storeN mem (sp - BitVec.ofNat 64 k) 4 v = some mem' := by
  have hS := hc.spLow
  apply storeN_isSome
  rw [sub_toNat hc hk2]
  have hs := permitted_sub hW (off := 16 - k) (count := 4) (by omega) (by omega)
  rwa [show sp.toNat - 16 + (16 - k) = sp.toNat - k by omega] at hs

theorem store_read {mem mem' : Memory} {a : Word} {v : Word}
    (hst : Silmaril.X86.Ext.storeN mem a 4 v = some mem')
    (hR : mem.Permitted .read a.toNat 4) :
    mem'.readBytes a.toNat (Silmaril.X86.Ext.leBytes v 4).length =
      some (Silmaril.X86.Ext.leBytes v 4) := by
  have hwo := Silmaril.X86.Ext.storeN_writesOnly hst
  refine Memory.readWith_eq _ _ _ _ ?_ (fun i hi => Memory.writeBytes_get hst i hi)
  rw [Silmaril.X86.Ext.length_leBytes]
  exact permitted_congr hwo.1.symm hR

/-- The event of a frame access at `[rbp - 4]` or `[rbp - 8]` lies in the frame. -/
theorem frame_events (hc : Ctx e ret sp c₀ h₀ r) {k : Nat} (hk1 : 8 < k) (hk2 : k ≤ 16)
    {ev : Silmaril.X86.MemEvent.Event} (hev : ev.addr = sp.toNat - k)
    (hsz : ev.size = 4) (a : Nat) (hcov : ev.Covers a) :
    sp.toNat - 16 ≤ a ∧ a < sp.toNat + 8 := by
  obtain ⟨h1, h2⟩ := hcov
  rw [hev] at h1 h2
  rw [hsz] at h2
  have := hc.spLow
  omega

theorem sp12 (hc : Ctx e ret sp c₀ h₀ r) : (sp - 12#64).toNat = sp.toNat - 12 :=
  sub_toNat hc (k := 12) (by omega)

theorem sp16 (hc : Ctx e ret sp c₀ h₀ r) : (sp - 16#64).toNat = sp.toNat - 16 :=
  sub_toNat hc (k := 16) (by omega)

/-- `mov %edi,-0x4(%rbp)`. -/
theorem step2 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 2 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 2 c h mem := by
  obtain ⟨hlh, -, -, hW, hR, hrw, -⟩ := reads hc hi hle
  obtain rfl : c = k2 c₀ := hi.1
  have hS := hc.spLow
  have hrbp : (k2 c₀).read .rbp = sp - 8#64 := by
    rw [← hc.rsp0]; exact rbp_body c₀ ret 2 (by omega) (by omega)
  have h12 := sub_toNat hc (k := 12) (by omega)
  obtain ⟨mem', hst⟩ := store_frame hc (k := 12) (by omega) (by omega) hW
    ((Sz.d.read c₀ .rdi).setWidth 64)
  have hx : Silmaril.X86.Ext.exec I2 (k2 c₀) mem = .ok (k3 c₀) mem' := by
    have hv : Sz.d.read (k2 c₀) .rdi = Sz.d.read c₀ .rdi :=
      szd_saved (ret := ret) 2 .rdi (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [Silmaril.X86.Ext.exec_store, frame4 hrbp, show Sz.d.bytes = 4 from rfl, hv, hst]
    rfl
  have hwo := Silmaril.X86.Ext.storeN_writesOnly hst
  have hrd := store_read hst (by
    rw [h12]
    have hs := permitted_sub hR (off := 4) (count := 4) (by omega) (by omega)
    rwa [show sp.toNat - 16 + 4 = sp.toNat - 12 by omega] at hs)
  rw [h12] at hwo hrd
  refine stepOK_of hc hi hle (off := 4) (rips hc).2.1 (by decide) (by decide) ?_ hx
    (fun q _ _ _ _ _ => r3 c₀ q) (fun hdom => ?_)
  · intro ev hev a hcov
    simp only [extAccesses, rmEv, memEv, List.mem_singleton] at hev
    subst hev
    exact frame_events hc (k := 12) (by omega) (by omega) (by show BitVec.toNat _ = _; rw [frame4 hrbp]; exact sp12 hc) rfl
      a hcov
  · have hout : ∀ a, (a < sp.toNat - 12 ∨ sp.toNat - 12 + 4 ≤ a) →
        mem'.bytes.get? a = mem.bytes.get? a := fun a ha => hwo.2 a ha
    refine ⟨rfl, dom_reval hdom _,
      hin_block hc hdom (fun i hj => by rw [permsAt_congr hwo.1]; exact hrw i hj), ?_,
      fun _ => ?_, fun _ => ?_, fun h => absurd h (by omega)⟩
    · exact hin_carry (fun a => sp.toNat ≤ a) hi.2.2.2.1 (fun f hf l hl => by
        obtain ⟨i, -, rfl⟩ := bytesAt_sub hf l hl; exact ⟨_, rfl, by omega⟩) hlh
        (fun a ha => hout a (.inr (by omega))) hwo.1
    · exact hin_carry (fun a => sp.toNat - 8 ≤ a) (hi.2.2.2.2.1 (by omega)) (fun f hf l hl => by
        obtain ⟨i, -, rfl⟩ := bytesAt_sub hf l hl; exact ⟨_, rfl, by omega⟩) hlh
        (fun a ha => hout a (.inr (by omega))) hwo.1
    · exact hin_read hc hdom hwo.1 hrw hrd (by omega)
        (by simp only [edi4, Silmaril.X86.Ext.length_leBytes]; omega)

/-- `mov %esi,-0x8(%rbp)`. -/
theorem step3 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 3 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 3 c h mem := by
  obtain ⟨hlh, -, -, hW, hR, hrw, -⟩ := reads hc hi hle
  obtain rfl : c = k3 c₀ := hi.1
  have hS := hc.spLow
  have hrbp : (k3 c₀).read .rbp = sp - 8#64 := by
    rw [← hc.rsp0]; exact rbp_body c₀ ret 3 (by omega) (by omega)
  have h16 := sub_toNat hc (k := 16) (by omega)
  obtain ⟨mem', hst⟩ := store_frame hc (k := 16) (by omega) (by omega) hW
    ((Sz.d.read c₀ .rsi).setWidth 64)
  have hx : Silmaril.X86.Ext.exec I3 (k3 c₀) mem = .ok (k4 c₀) mem' := by
    have hv : Sz.d.read (k3 c₀) .rsi = Sz.d.read c₀ .rsi :=
      szd_saved (ret := ret) 3 .rsi (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [Silmaril.X86.Ext.exec_store, frame8 hrbp, show Sz.d.bytes = 4 from rfl, hv, hst]
    rfl
  have hwo := Silmaril.X86.Ext.storeN_writesOnly hst
  have hrd := store_read hst (by
    rw [h16]
    have hs := permitted_sub hR (off := 0) (count := 4) (by omega) (by omega)
    rwa [Nat.add_zero] at hs)
  rw [h16] at hwo hrd
  refine stepOK_of hc hi hle (off := 7) (rips hc).2.2.1 (by decide) (by decide) ?_ hx
    (fun q _ _ _ _ _ => r4 c₀ q) (fun hdom => ?_)
  · intro ev hev a hcov
    simp only [extAccesses, rmEv, memEv, List.mem_singleton] at hev
    subst hev
    exact frame_events hc (k := 16) (by omega) (by omega) (by show BitVec.toNat _ = _; rw [frame8 hrbp]; exact sp16 hc) rfl
      a hcov
  · have hout : ∀ a, (a < sp.toNat - 16 ∨ sp.toNat - 16 + 4 ≤ a) →
        mem'.bytes.get? a = mem.bytes.get? a := fun a ha => hwo.2 a ha
    refine ⟨rfl, dom_reval hdom _,
      hin_block hc hdom (fun i hj => by rw [permsAt_congr hwo.1]; exact hrw i hj), ?_,
      fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact hin_carry (fun a => sp.toNat ≤ a) hi.2.2.2.1 (fun f hf l hl => by
        obtain ⟨i, -, rfl⟩ := bytesAt_sub hf l hl; exact ⟨_, rfl, by omega⟩) hlh
        (fun a ha => hout a (.inr (by omega))) hwo.1
    · exact hin_carry (fun a => sp.toNat - 8 ≤ a) (hi.2.2.2.2.1 (by omega)) (fun f hf l hl => by
        obtain ⟨i, -, rfl⟩ := bytesAt_sub hf l hl; exact ⟨_, rfl, by omega⟩) hlh
        (fun a ha => hout a (.inr (by omega))) hwo.1
    · exact hin_carry (fun a => sp.toNat - 12 ≤ a) (hi.2.2.2.2.2.1 (by omega))
        (fun f hf l hl => by
          obtain ⟨i, -, rfl⟩ := bytesAt_sub hf l hl; exact ⟨_, rfl, by omega⟩) hlh
        (fun a ha => hout a (.inr (by omega))) hwo.1
    · exact hin_read hc hdom hwo.1 hrw hrd (by omega)
        (by simp only [esi4, Silmaril.X86.Ext.length_leBytes]; omega)

/-- The spilled `edi`, reloaded. -/
theorem load12 (hc : Ctx e ret sp c₀ h₀ r) {j : Nat} {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ j c h) (hj : 3 ≤ j) (hlh : Le h (toFrag ⟨c, mem⟩)) :
    Silmaril.X86.Ext.loadN mem (sp - 12#64) 4 =
      some (BitVec.ofNat 64 (((Sz.d.read c₀ .rdi).setWidth 64).toNat % 2 ^ (8 * 4))) := by
  have h12 := sub_toNat hc (k := 12) (by omega)
  have := hi.2.2.2.2.2.1 hj
  rw [← h12] at this
  exact load_part this hlh

/-- The spilled `esi`, reloaded. -/
theorem load16 (hc : Ctx e ret sp c₀ h₀ r) {j : Nat} {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ j c h) (hj : 4 ≤ j) (hlh : Le h (toFrag ⟨c, mem⟩)) :
    Silmaril.X86.Ext.loadN mem (sp - 16#64) 4 =
      some (BitVec.ofNat 64 (((Sz.d.read c₀ .rsi).setWidth 64).toNat % 2 ^ (8 * 4))) := by
  have h16 := sub_toNat hc (k := 16) (by omega)
  have := hi.2.2.2.2.2.2 hj
  rw [← h16] at this
  exact load_part this hlh

theorem rbpj (hc : Ctx e ret sp c₀ h₀ r) (j : Nat) (h1 : 2 ≤ j) (h2 : j ≤ 13) :
    (core c₀ ret j).read .rbp = sp - 8#64 := by
  rw [← hc.rsp0]; exact rbp_body c₀ ret j h1 h2

/-- `mov -0x4(%rbp),%eax`. -/
theorem step4 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 4 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 4 c h mem := by
  obtain ⟨hlh, -⟩ := reads hc hi hle
  obtain rfl : c = k4 c₀ := hi.1
  have hrbp : (k4 c₀).read .rbp = sp - 8#64 := rbpj hc 4 (by omega) (by omega)
  have hx : Silmaril.X86.Ext.exec I4 (k4 c₀) mem = .ok (k5 c₀) mem := by
    rw [Silmaril.X86.Ext.exec_load, frame4 hrbp, show Sz.d.bytes = 4 from rfl,
      load12 hc hi (by omega) hlh]
    simp only [Silmaril.X86.Decompile.RightRot.reload_setWidth]
    rfl
  refine stepOK_of hc hi hle (off := 10) (rips hc).2.2.2.1 (by decide) (by decide) ?_ hx
    (fun q _ _ h3 _ _ => r5 c₀ q h3) (fun _ => inv_carry hi hlh rfl (by omega) (by omega)
      (by omega))
  intro ev hev a hcov
  simp only [extAccesses, memEv, List.mem_singleton] at hev
  subst hev
  exact frame_events hc (k := 12) (by omega) (by omega) (by show BitVec.toNat _ = _; rw [frame4 hrbp]; exact sp12 hc) rfl a hcov

/-- `mov -0x8(%rbp),%ecx`. -/
theorem step5 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 5 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 5 c h mem := by
  obtain ⟨hlh, -⟩ := reads hc hi hle
  obtain rfl : c = k5 c₀ := hi.1
  have hrbp : (k5 c₀).read .rbp = sp - 8#64 := rbpj hc 5 (by omega) (by omega)
  have hx : Silmaril.X86.Ext.exec I5 (k5 c₀) mem = .ok (k6 c₀) mem := by
    rw [Silmaril.X86.Ext.exec_load, frame8 hrbp, show Sz.d.bytes = 4 from rfl,
      load16 hc hi (by omega) hlh]
    simp only [Silmaril.X86.Decompile.RightRot.reload_setWidth]
    rfl
  refine stepOK_of hc hi hle (off := 13) (rips hc).2.2.2.2.1 (by decide) (by decide) ?_ hx
    (fun q _ _ _ h4 _ => r6 c₀ q h4) (fun _ => inv_carry hi hlh rfl (by omega) (by omega)
      (by omega))
  intro ev hev a hcov
  simp only [extAccesses, memEv, List.mem_singleton] at hev
  subst hev
  exact frame_events hc (k := 16) (by omega) (by omega) (by show BitVec.toNat _ = _; rw [frame8 hrbp]; exact sp16 hc) rfl a hcov

/-- `shr %cl,%eax`. -/
theorem step6 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 6 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 6 c h mem := by
  obtain ⟨hlh, -⟩ := reads hc hi hle
  obtain rfl : c = k6 c₀ := hi.1
  refine stepOK_of hc hi hle (off := 16) (rips hc).2.2.2.2.2.1 (by decide) (by decide) ?_
    (Silmaril.X86.Ext.exec_shift_reg _ mem .d .shr .rax .cl)
    (fun q _ _ h3 _ _ => r7 c₀ q h3) (fun _ => inv_carry hi hlh rfl (by omega) (by omega)
      (by omega))
  intro ev hev; simp [extAccesses, rmEv] at hev

/-- `mov -0x4(%rbp),%edx`. -/
theorem step7 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 7 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 7 c h mem := by
  obtain ⟨hlh, -⟩ := reads hc hi hle
  obtain rfl : c = k7 c₀ := hi.1
  have hrbp : (k7 c₀).read .rbp = sp - 8#64 := rbpj hc 7 (by omega) (by omega)
  have hx : Silmaril.X86.Ext.exec I7 (k7 c₀) mem = .ok (k8 c₀) mem := by
    rw [Silmaril.X86.Ext.exec_load, frame4 hrbp, show Sz.d.bytes = 4 from rfl,
      load12 hc hi (by omega) hlh]
    simp only [Silmaril.X86.Decompile.RightRot.reload_setWidth]
    rfl
  refine stepOK_of hc hi hle (off := 18) (rips hc).2.2.2.2.2.2.1 (by decide) (by decide) ?_ hx
    (fun q _ _ _ _ h5 => r8 c₀ q h5) (fun _ => inv_carry hi hlh rfl (by omega) (by omega)
      (by omega))
  intro ev hev a hcov
  simp only [extAccesses, memEv, List.mem_singleton] at hev
  subst hev
  exact frame_events hc (k := 12) (by omega) (by omega) (by show BitVec.toNat _ = _; rw [frame4 hrbp]; exact sp12 hc) rfl a hcov

/-- `mov $0x20,%ecx`. -/
theorem step8 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 8 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 8 c h mem := by
  obtain ⟨hlh, -⟩ := reads hc hi hle
  obtain rfl : c = k8 c₀ := hi.1
  refine stepOK_of hc hi hle (off := 21) (rips hc).2.2.2.2.2.2.2.1 (by decide) (by decide) ?_
    (Silmaril.X86.Ext.exec_movI32 _ mem .rcx 0x20)
    (fun q _ _ _ h4 _ => r9 c₀ q h4) (fun _ => inv_carry hi hlh rfl (by omega) (by omega)
      (by omega))
  intro ev hev; simp [extAccesses] at hev

/-- `sub -0x8(%rbp),%ecx`. -/
theorem step9 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 9 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 9 c h mem := by
  obtain ⟨hlh, -⟩ := reads hc hi hle
  obtain rfl : c = k9 c₀ := hi.1
  have hrbp : (k9 c₀).read .rbp = sp - 8#64 := rbpj hc 9 (by omega) (by omega)
  have hrm : ∀ nxt : Word, Silmaril.X86.Ext.readRM .d (.mem (frame 0xFFFFFFF8)) (k9 c₀) mem nxt =
      some (Sz.d.read c₀ .rsi) := by
    intro nxt
    simp only [Silmaril.X86.Ext.readRM, frame8 hrbp, show Sz.d.bytes = 4 from rfl,
      load16 hc hi (by omega) hlh, Option.map_some,
      Silmaril.X86.Decompile.RightRot.reload_setWidth]
  have hx : Silmaril.X86.Ext.exec I9 (k9 c₀) mem = .ok (k10 c₀) mem :=
    exec_aluR_mem .d .sub .rcx (frame 0xFFFFFFF8) (k9 c₀) mem (by decide) (hrm _)
  refine stepOK_of hc hi hle (off := 26) (rips hc).2.2.2.2.2.2.2.2.1 (by decide) (by decide) ?_
    hx (fun q _ _ _ h4 _ => r10 c₀ q h4) (fun _ => inv_carry hi hlh rfl (by omega) (by omega)
      (by omega))
  intro ev hev a hcov
  simp only [extAccesses, rmEv, memEv, List.mem_singleton] at hev
  subst hev
  exact frame_events hc (k := 16) (by omega) (by omega) (by show BitVec.toNat _ = _; rw [frame8 hrbp]; exact sp16 hc) rfl a hcov

/-- `shl %cl,%edx`. -/
theorem step10 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 10 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 10 c h mem := by
  obtain ⟨hlh, -⟩ := reads hc hi hle
  obtain rfl : c = k10 c₀ := hi.1
  refine stepOK_of hc hi hle (off := 29) (rips hc).2.2.2.2.2.2.2.2.2.1 (by decide) (by decide)
    ?_ (Silmaril.X86.Ext.exec_shift_reg _ mem .d .shl .rdx .cl)
    (fun q _ _ _ _ h5 => r11 c₀ q h5) (fun _ => inv_carry hi hlh rfl (by omega) (by omega)
      (by omega))
  intro ev hev; simp [extAccesses, rmEv] at hev

/-- `mov %edx,%ecx`. -/
theorem step11 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 11 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 11 c h mem := by
  obtain ⟨hlh, -⟩ := reads hc hi hle
  obtain rfl : c = k11 c₀ := hi.1
  refine stepOK_of hc hi hle (off := 31) (rips hc).2.2.2.2.2.2.2.2.2.2.1 (by decide) (by decide)
    ?_ (Silmaril.X86.Ext.exec_mov_reg _ mem .d .rcx .rdx)
    (fun q _ _ _ h4 _ => r12 c₀ q h4) (fun _ => inv_carry hi hlh rfl (by omega) (by omega)
      (by omega))
  intro ev hev; simp [extAccesses, rmEv] at hev

/-- `or %ecx,%eax`. -/
theorem step12 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 12 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 12 c h mem := by
  obtain ⟨hlh, -⟩ := reads hc hi hle
  obtain rfl : c = k12 c₀ := hi.1
  refine stepOK_of hc hi hle (off := 33) (rips hc).2.2.2.2.2.2.2.2.2.2.2.1 (by decide)
    (by decide) ?_ (Silmaril.X86.Ext.exec_alu_reg _ mem .d .or .rax .rcx (by decide))
    (fun q _ _ h3 _ _ => r13 c₀ q h3) (fun _ => inv_carry hi hlh rfl (by omega) (by omega)
      (by omega))
  intro ev hev; simp [extAccesses, rmEv] at hev

/-- `pop %rbp`. -/
theorem step13 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 13 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 13 c h mem := by
  obtain ⟨hlh, -⟩ := reads hc hi hle
  obtain rfl : c = k13 c₀ := hi.1
  have hS := hc.spLow
  have hrsp : (k13 c₀).read .rsp = sp - 8#64 := by
    rw [← hc.rsp0]; exact rsp_body c₀ ret 13 (by omega) (by omega)
  have h8 := sub_toNat hc (k := 8) (by omega)
  have hrd : mem.readBytes ((k13 c₀).read .rsp).toNat 8 = some (encodeWords [c₀.read .rbp]) := by
    rw [hrsp, h8]
    obtain ⟨f, hf, hfl⟩ := hi.2.2.2.2.1 (by omega)
    exact readBytes_of_wordPt (m := ⟨k13 c₀, mem⟩) hf (fun l v e => hlh l v (hfl l v e))
  have hpop := Silmaril.X86.popWord_of_readBytes hrd
  have hx : Silmaril.X86.Ext.exec I13 (k13 c₀) mem = .ok (k14 c₀) mem := by
    rw [Silmaril.X86.Ext.exec_pop]
    simp only [Silmaril.X86.Insn.exec, hpop, Option.map_some]
    rfl
  refine stepOK_of hc hi hle (off := 35) (rips hc).2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)
    (by decide) ?_ hx (fun q h1 h2 _ _ _ => r14 c₀ q h1 h2)
    (fun _ => inv_carry hi hlh rfl (by omega) (by omega) (by omega))
  intro ev hev a hcov
  simp only [extAccesses, popEv, List.mem_singleton] at hev
  subst hev
  obtain ⟨h1, h2⟩ := hcov
  simp only [hrsp, h8] at h1 h2
  omega

/-- `ret`. -/
theorem step14 (hc : Ctx e ret sp c₀ h₀ r) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 14 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    StepOK ret sp c₀ h₀ r 14 c h mem := by
  obtain ⟨hlh, -, -, -, -, -, hslot⟩ := reads hc hi hle
  obtain rfl : c = k14 c₀ := hi.1
  have hrsp : (k14 c₀).read .rsp = sp := (rsp14 c₀).trans hc.rsp0
  have hpop := Silmaril.X86.popWord_of_readBytes (s := k14 c₀) (by rw [hrsp]; exact hslot)
  have hx : Silmaril.X86.Ext.exec I14 (k14 c₀) mem = .ok (k15 c₀ ret) mem := by
    rw [Silmaril.X86.Ext.exec_ret]
    simp only [Silmaril.X86.Insn.exec, hpop, Option.map_some]
    rfl
  refine stepOK_of hc hi hle (off := 36) (rips hc).2.2.2.2.2.2.2.2.2.2.2.2.2 (by decide)
    (by decide) ?_ hx (fun q h1 _ _ _ _ => r15 c₀ ret q h1)
    (fun _ => inv_carry hi hlh rfl (by omega) (by omega) (by omega))
  intro ev hev a hcov
  simp only [extAccesses, popEv, List.mem_singleton] at hev
  subst hev
  obtain ⟨h1, h2⟩ := hcov
  simp only [hrsp] at h1 h2
  omega

end Steps

/-! ## The value and the postcondition -/

section Final
variable {e ret sp : Word} {c₀ : State} {h₀ r : Frag}
open Silmaril.X86.Decompile
open Silmaril.X86.Decompile.RightRot (masked_count sub_from_32 or_shifts_eq)
open Silmaril.X86.Safe.RightRot (sep_reval_split ripPt_reval' regAny_reval flagsAny_reval
  raxLow32)

theorem szr {a b : State} {q : Reg} (hh : a.read q = b.read q) : Sz.d.read a q = Sz.d.read b q := by
  simp only [Sz.read, hh]

/-- **`eax` holds the decompiled function** after the `or` (as in `run_stable`). -/
theorem rax13 (hpos : 0 < (Sz.d.read c₀ .rsi).toNat) (hlt : (Sz.d.read c₀ .rsi).toNat < 32) :
    Sz.d.read (k13 c₀) .rax = rightRotSpec (Sz.d.read c₀ .rdi) (Sz.d.read c₀ .rsi).toNat := by
  have hv5 : Sz.d.read (k5 c₀) .rax = Sz.d.read c₀ .rdi := by
    simp only [k5, szRead_setRip, Silmaril.X86.Ext.Sz.read_write]
  have hv6 : Sz.d.read (k6 c₀) .rax = Sz.d.read c₀ .rdi := (szr (r6 c₀ .rax (by decide))).trans hv5
  have hcnt6 : (Count.cl.raw (k6 c₀)).toNat % Sz.d.bits = (Sz.d.read c₀ .rsi).toNat := by
    have hrcx : (k6 c₀).read .rcx = (Sz.d.read c₀ .rsi).setWidth 64 := by
      simp only [k6, read_setRip, read_szWrite_same]
    simp only [Count.raw, hrcx]
    exact masked_count _ hlt
  have hshr : Sz.d.read (k7 c₀) .rax =
      ShiftOp.shr.result (Sz.d.read c₀ .rdi) (Sz.d.read c₀ .rsi).toNat := by
    simp only [k7, szRead_setFlagsRip, Silmaril.X86.Ext.Sz.read_write, hv6, hcnt6]
  have hv8 : Sz.d.read (k8 c₀) .rdx = Sz.d.read c₀ .rdi := by
    simp only [k8, szRead_setRip, Silmaril.X86.Ext.Sz.read_write]
  have hv9rcx : Sz.d.read (k9 c₀) .rcx = (0x20 : BitVec Sz.d.bits) := by
    simp only [k9, Sz.read, read_setRip, Silmaril.X86.State.read_write_same]
    decide
  have hcnt10 : (Count.cl.raw (k10 c₀)).toNat % Sz.d.bits = 32 - (Sz.d.read c₀ .rsi).toNat := by
    have hrcx : (k10 c₀).read .rcx =
        ((0x20 : BitVec Sz.d.bits) - Sz.d.read c₀ .rsi).setWidth 64 := by
      simp only [k10, read_setFlagsRip, read_szWrite_same, hv9rcx,
        Silmaril.X86.Ext.AluOp.resultN]
    simp only [Count.raw, hrcx]
    rw [masked_count _ (by rw [sub_from_32 _ hpos hlt]; omega)]
    exact sub_from_32 _ hpos hlt
  have hv10rdx : Sz.d.read (k10 c₀) .rdx = Sz.d.read c₀ .rdi :=
    (szr (r10 c₀ .rdx (by decide))).trans ((szr (r9 c₀ .rdx (by decide))).trans hv8)
  have hshl : Sz.d.read (k11 c₀) .rdx =
      ShiftOp.shl.result (Sz.d.read c₀ .rdi) (32 - (Sz.d.read c₀ .rsi).toNat) := by
    simp only [k11, szRead_setFlagsRip, Silmaril.X86.Ext.Sz.read_write, hv10rdx, hcnt10]
  have hv12rcx : Sz.d.read (k12 c₀) .rcx =
      ShiftOp.shl.result (Sz.d.read c₀ .rdi) (32 - (Sz.d.read c₀ .rsi).toNat) := by
    simp only [k12, szRead_setRip, Silmaril.X86.Ext.Sz.read_write, hshl]
  have hv12rax : Sz.d.read (k12 c₀) .rax =
      ShiftOp.shr.result (Sz.d.read c₀ .rdi) (Sz.d.read c₀ .rsi).toNat :=
    (szr (r12 c₀ .rax (by decide))).trans ((szr (r11 c₀ .rax (by decide))).trans
      ((szr (r10 c₀ .rax (by decide))).trans ((szr (r9 c₀ .rax (by decide))).trans
        ((szr (r8 c₀ .rax (by decide))).trans hshr))))
  simp only [k13, szRead_setFlagsRip, Silmaril.X86.Ext.Sz.read_write, hv12rax, hv12rcx,
    Silmaril.X86.Ext.AluOp.resultN]
  exact or_shifts_eq _ _

/-- A fragment with the entry fragment's domain, inside a total fragment, is the entry fragment
re-valued. -/
theorem eq_reval {h s : Frag} (hdom : ∀ l, (h l).isSome = (h₀ l).isSome) (hl : Le h s) :
    h = reval h₀ s := by
  funext l
  have := hdom l
  unfold reval
  cases e₀ : h₀ l with
  | none => rw [e₀] at this; cases e : h l; · rfl
            · rw [e] at this; cases this
  | some v =>
    rw [e₀] at this
    simp only [Option.isSome_some, ite_true]
    cases e : h l with
    | none => rw [e] at this; cases this
    | some w => exact (hl l w e).symm

/-- **The postcondition at the return.** -/
theorem final (hc : Ctx e ret sp c₀ h₀ r) {bp vdi vsi : Word}
    (hpre : rrPre e ret sp bp vdi vsi h₀) (hbp : c₀.read .rbp = bp) (hdi : c₀.read .rdi = vdi)
    (hsi : c₀.read .rsi = vsi) {c : State} {h : Frag} {mem : Memory}
    (hi : Inv ret sp c₀ h₀ 15 c h) (hle : Le (union h r) (toFrag ⟨c, mem⟩)) :
    retFin ret c ∧ rrPost ret sp bp vdi vsi h := by
  obtain ⟨hlh, -, -, -, -, hrw, -⟩ := reads hc hi hle
  have hslot := hi.2.2.2.1
  obtain rfl : c = k15 c₀ ret := hi.1
  have hfin : (k15 c₀ ret).rip = ret := by unfold k15; rfl
  refine ⟨hfin, ?_⟩
  rw [eq_reval hi.2.1 hlh]
  obtain ⟨h1, r1, hd1, rfl, hrip, r1P⟩ := hpre
  obtain ⟨h2, r2, hd2, rfl, hrsp, r2P⟩ := r1P
  obtain ⟨h3, r3, hd3, rfl, hrbp, r3P⟩ := r2P
  obtain ⟨h4, r4, hd4, rfl, hrdi, r4P⟩ := r3P
  obtain ⟨h5, r5, hd5, rfl, hrsi, r5P⟩ := r4P
  obtain ⟨h6, r6, hd6, rfl, hrax, r6P⟩ := r5P
  obtain ⟨h7, r7, hd7, rfl, hrcx, r7P⟩ := r6P
  obtain ⟨h8, r8, hd8, rfl, hrdx, r8P⟩ := r7P
  obtain ⟨h9, r9, hd9, rfl, hfl, r9P⟩ := r8P
  obtain ⟨h10, h11, hd10, rfl, hblk, hword⟩ := r9P
  let m : MState := ⟨k15 c₀ ret, mem⟩
  have hrsp15 : (k15 c₀ ret).read .rsp = sp + 8#64 := by
    unfold k15
    rw [read_setRip, Silmaril.X86.State.read_write_same, rsp14, hc.rsp0]
  have hrbp15 : (k15 c₀ ret).read .rbp = bp :=
    ((r15 c₀ ret .rbp (by decide)).trans (rbp14 c₀)).trans hbp
  have hrdi15 : (k15 c₀ ret).read .rdi = vdi :=
    (saved c₀ ret 15 .rdi (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdi
  have hrsi15 : (k15 c₀ ret).read .rsi = vsi :=
    (saved c₀ ret 15 .rsi (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsi
  have hrax15 : Sz.d.read (k15 c₀ ret) .rax =
      rightRotSpec (vdi.setWidth 32) (vsi.setWidth 32).toNat := by
    rw [szr ((r15 c₀ ret .rax (by decide)).trans (r14 c₀ .rax (by decide) (by decide))),
      rax13 hc.cpos hc.clt]
    simp only [Sz.read, hdi, hsi]
    rfl
  obtain ⟨fw, hfw, hfwl⟩ := hslot
  refine sep_reval_split hd1 ?_ (sep_reval_split hd2 ?_ (sep_reval_split hd3 ?_
    (sep_reval_split hd4 ?_ (sep_reval_split hd5 ?_ (sep_reval_split hd6 ?_
    (sep_reval_split hd7 ?_ (sep_reval_split hd8 ?_ (sep_reval_split hd9 ?_
    (sep_reval_split hd10 ?_ ?_)))))))))
  · exact ripPt_reval' m hrip
  · have := regPt_reval m hrsp; rwa [show m.core.read .rsp = sp + 8#64 from hrsp15] at this
  · have := regPt_reval m hrbp; rwa [show m.core.read .rbp = bp from hrbp15] at this
  · have := regPt_reval m hrdi; rwa [show m.core.read .rdi = vdi from hrdi15] at this
  · have := regPt_reval m hrsi; rwa [show m.core.read .rsi = vsi from hrsi15] at this
  · obtain ⟨v, hv⟩ := hrax
    exact ⟨m.core.read .rax, hrax15, regPt_reval m hv⟩
  · exact regAny_reval m hrcx
  · exact regAny_reval m hrdx
  · exact Silmaril.X86.Sep.flagsAny_reval m hfl
  · exact blockAny_reval hblk fun i hi => hrw i hi
  · refine bytesAt_reval (need := RW) hword rfl fun i hi => ?_
    have := bytesAt_le (m := m) hfw (fun l v e => hlh l v (hfwl l v e)) i hi
    exact ⟨this.2.1, this.2.2⟩

end Final

/-! ## The triple -/

open Silmaril.X86.Decompile in
/-- **`Task.rightRotLocal` holds**: `right_rot` meets the footprint triple on `openEv` with its
code as the read-only context, for every step index. -/
theorem rightRotLocal : RightRotLocal := by
  intro e ret sp bp vdi vsi hsp _hapart hpos hlt hret n c h r hr hp hd
  cases n with
  | zero => trivial
  | succ n =>
    intro mem hle
    have hlh : Le h (toFrag ⟨c, mem⟩) := Frag.le_of_union_left hle
    have hlr : Le r (toFrag ⟨c, mem⟩) := Frag.le_of_union_right hd hle
    have hrefl : Le h h := fun _ _ e => e
    obtain ⟨h1, r1, hrip, r1P, l1, lr1, -, rfl⟩ := sep_le hp hrefl
    obtain ⟨h2, r2, hrsp, r2P, l2, lr2, -, rfl⟩ := sep_le r1P lr1
    obtain ⟨h3, r3, hrbp, r3P, l3, lr3, -, rfl⟩ := sep_le r2P lr2
    obtain ⟨h4, r4, hrdi, r4P, l4, lr4, -, rfl⟩ := sep_le r3P lr3
    obtain ⟨h5, r5, hrsi, r5P, l5, lr5, -, rfl⟩ := sep_le r4P lr4
    obtain ⟨h6, r6, hrax, r6P, l6, lr6, -, rfl⟩ := sep_le r5P lr5
    obtain ⟨h7, r7, hrcx, r7P, l7, lr7, -, rfl⟩ := sep_le r6P lr6
    obtain ⟨h8, r8, hrdx, r8P, l8, lr8, -, rfl⟩ := sep_le r7P lr7
    obtain ⟨h9, r9, hfl, r9P, l9, lr9, -, rfl⟩ := sep_le r8P lr8
    obtain ⟨h10, h11, hblk, hword, l10, l11, -, rfl⟩ := sep_le r9P lr9
    set H := union h1 (union h2 (union h3 (union h4 (union h5 (union h6 (union h7 (union h8
      (union h9 (union h10 h11))))))))) with hH
    have tr : ∀ {a : Frag}, Le a H → Le a (toFrag ⟨c, mem⟩) :=
      fun ha l v e => hlh l v (ha l v e)
    have own : ∀ {a : Frag} {l : Loc}, Le a H → (a l).isSome → (H l).isSome := by
      intro a l ha e
      cases e' : a l with
      | none => rw [e'] at e; cases e
      | some v => rw [ha l v e']; rfl
    have dsome : ∀ {l : Loc} {v : Val} {f : Frag}, f = Frag.single l v → (f l).isSome := by
      intro l v f e; subst e; simp [Frag.single]
    have erip : c.rip = e := ripPt_le (m := ⟨c, mem⟩) hrip (tr l1)
    have ersp : c.read .rsp = sp := regPt_le (m := ⟨c, mem⟩) hrsp (tr l2)
    have erbp : c.read .rbp = bp := regPt_le (m := ⟨c, mem⟩) hrbp (tr l3)
    have erdi : c.read .rdi = vdi := regPt_le (m := ⟨c, mem⟩) hrdi (tr l4)
    have ersi : c.read .rsi = vsi := regPt_le (m := ⟨c, mem⟩) hrsi (tr l5)
    have hcode := bytesAt_le (m := ⟨c, mem⟩) hr hlr 36 (by decide)
    have hslot := bytesAt_le (m := ⟨c, mem⟩) hword (tr l11) 7 (by simp)
    obtain ⟨v6, hv6⟩ := hrax
    obtain ⟨v7, hv7⟩ := hrcx
    obtain ⟨v8, hv8⟩ := hrdx
    obtain ⟨f9, hf9⟩ := hfl
    have hc : Ctx e ret sp c H r :=
      { code := hr
        disj := hd
        own := by
          intro l hl
          rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, hi, rfl⟩
          · exact own l1 (dsome hrip)
          · exact own l9 (dsome hf9)
          · exact own l2 (dsome hrsp)
          · exact own l3 (dsome hrbp)
          · exact own l6 (dsome hv6)
          · exact own l7 (dsome hv7)
          · exact own l8 (dsome hv8)
          · by_cases h16 : i < 16
            · exact own l10 (blockAny_dom hblk i h16)
            · have := bytesAt_dom hword (i - 16) (by simp; omega)
              rw [show sp.toNat + (i - 16) = sp.toNat - 16 + i by omega] at this
              exact own l11 this
        rip0 := erip
        rsp0 := ersp
        spLow := hsp
        spHigh := by have := hslot.1; simp only [addressLimit] at this; omega
        codeHigh := by have := hcode.1; simp only [addressLimit] at this; omega
        retOut := by omega
        cpos := by simp only [Sz.read, ersi]; exact hpos
        clt := by simp only [Sz.read, ersi]; exact hlt }
    have hinv : Inv ret sp c H 0 c H :=
      ⟨rfl, fun _ => rfl, ⟨h10, hblk, l10⟩, ⟨h11, hword, l11⟩, fun h => absurd h (by omega),
        fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    have hstep : ∀ j < 15, ∀ c' h' mem', Inv ret sp c H j c' h' →
        Le (union h' r) (toFrag ⟨c', mem'⟩) → StepOK ret sp c H r j c' h' mem' := by
      intro j hj c' h' mem' hi hle'
      match j, hj, hi with
      | 0, _, hi => exact step0 hc hi hle'
      | 1, _, hi => exact step1 hc hi hle'
      | 2, _, hi => exact step2 hc hi hle'
      | 3, _, hi => exact step3 hc hi hle'
      | 4, _, hi => exact step4 hc hi hle'
      | 5, _, hi => exact step5 hc hi hle'
      | 6, _, hi => exact step6 hc hi hle'
      | 7, _, hi => exact step7 hc hi hle'
      | 8, _, hi => exact step8 hc hi hle'
      | 9, _, hi => exact step9 hc hi hle'
      | 10, _, hi => exact step10 hc hi hle'
      | 11, _, hi => exact step11 hc hi hle'
      | 12, _, hi => exact step12 hc hi hle'
      | 13, _, hi => exact step13 hc hi hle'
      | 14, _, hi => exact step14 hc hi hle'
      | _ + 15, h, _ => exact absurd h (by omega)
    have hs : LSafeEv openEv (retFin ret) (rrPost ret sp bp vdi vsi) r (n + 1) c H :=
      lsafe_chain (Inv ret sp c H) 15 hstep
        (fun c' h' mem' hi hle' => final hc hp erbp erdi ersi hi hle') (n + 1) 0 c H
        (Nat.zero_le _) hinv
    exact hs mem hle

end Silmaril.Proofs.X86.Pool.RightRotLocal
