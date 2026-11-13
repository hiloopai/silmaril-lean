module

public import Silmaril.Machine.X86.Cert.Thms
public import Silmaril.Machine.X86.BlockCert.Store.Thms
public import Silmaril.Machine.X86.BlockCert.Ext8.Thms
public import Silmaril.Machine.X86.BlockCert9.Thms

/-!
# The block bridges, inside the code

Each existing block bridge (`BlockCert.runL_open`, `BlockCert.runLW_open`,
`BlockCert8.run8_open`, `BlockCert9.Code.run_open9`) concludes
`Reaches`. The generic certificate needs the stronger `RunsIn I (InCode I base len)`: every
step of a checked block is taken from a state whose program counter lies inside the code.
The proofs follow the existing bridges, using only exported lemmas (`Open.step_of_listed`,
`Open9.step_of_listed`, `BlockCert.exec_rip`/`exec_mem`,
`BlockCert9.execNew_rip`/`execNew_mem`), plus the fact that a decoded instruction has positive
length (each decoder rejects `[]`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Cert.Kinds

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded RM)
open Silmaril.X86.Lift.Bir (LInstr XState execBlock liftR)
open Silmaril.Process (Memory)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.FnContract (RunsIn InCode runsIn_map)
open Silmaril.Machine.X86.BlockCert

/-! ## Positive lengths -/

theorem ext_decode_nil : Silmaril.X86.Ext.decode [] = none := by decide
theorem open_decode_nil : Open.decode [] = none := by decide
theorem open9_decode_nil : Open9.decode [] = none := by decide

theorem len_pos {α : Type} {dec : List Byte → Option (α × Nat)} (h0 : dec [] = none)
    {code : List Byte} {o l : Nat} {a : α} (h : dec ((code.drop o).take l) = some (a, l)) :
    0 < l := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    simp [h0] at h
  · exact hl

theorem inCode_of {m : MState} {base : Word} {o l len : Nat}
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ len) (hl : 0 < l) :
    InCode Open.isa base len m :=
  ⟨o, by omega, hrip⟩

theorem execL_toExt {i : LInstr} {e : Silmaril.X86.Ext.Instr} (h : toExt i = some e)
    (s : XState) (mem : Memory) (len : Nat) :
    i.exec s mem len = liftR s.xmm (Silmaril.X86.Ext.exec e s.core mem len) := by
  unfold toExt at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h

theorem open_decode {bytes : List Byte} {e : Silmaril.X86.Ext.Instr} {l : Nat}
    (h : Silmaril.X86.Ext.decode bytes = some (e, l)) :
    Open.decode bytes = some (.base e, l) := by
  simp [Open.decode, Silmaril.X86.Ext8.decode_of_ext h]

/-! ## Bir listings that write no memory (`BlockCert.listingAt`) -/

theorem execBlock_within {code : List Byte} {base : Word} :
    ∀ (L : List (LInstr × Nat)) (o : Nat) (c : State) (x : Silmaril.X86.Lift.Bir.Xmm)
      (mem : Memory) (s' : XState) (mem' : Memory),
      listingAt code o L = true → Loaded mem base code → c.rip = base + BitVec.ofNat 64 o →
      execBlock L ⟨c, x⟩ mem = .ok s' mem' →
      RunsIn Open.isa (InCode Open.isa base code.length) ⟨c, mem⟩ ⟨s'.core, mem'⟩ ∧ mem' = mem
  | [], _, c, x, mem, s', mem', _, _, _, h => by
    simp only [execBlock] at h
    cases h
    exact ⟨.refl _, rfl⟩
  | (i, l) :: rest, o, c, x, mem, s', mem', hok, hl, hrip, h => by
    simp only [listingAt] at hok
    split at hok
    · cases hok
    rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hdec, hfit⟩, hnw⟩, hft⟩, hrest⟩ := hok
    have hin : InCode Open.isa base code.length (⟨c, mem⟩ : MState) :=
      inCode_of (m := ⟨c, mem⟩) hrip hfit (len_pos ext_decode_nil hdec)
    simp only [execBlock] at h
    rw [execL_toExt he] at h
    cases hx : Silmaril.X86.Ext.exec e c mem l with
    | ok c1 m1 =>
      rw [hx] at h
      simp only [liftR] at h
      have hm1 : m1 = mem := exec_mem hnw hx
      subst hm1
      have hs : Open.step ⟨c, m1⟩ = some ⟨c1, m1⟩ :=
        Open.step_of_listed (m := ⟨c, m1⟩) hl hrip hfit (open_decode hdec) hx
      cases rest with
      | nil =>
        simp only [execBlock] at h
        cases h
        exact ⟨.step hin hs (.refl _), rfl⟩
      | cons nx rest' =>
        simp only [List.isEmpty_cons, Bool.false_or] at hft
        have hrip1 : c1.rip = base + BitVec.ofNat 64 (o + l) := by
          rw [exec_rip hft hx, hrip, BitVec.ofNat_add, BitVec.add_assoc]
        obtain ⟨hr, hm⟩ := execBlock_within (nx :: rest') (o + l) c1 x m1 s' mem' hrest hl hrip1 h
        exact ⟨.step hin hs hr, hm⟩
    | dataFault => rw [hx] at h; cases h
    | divideError => rw [hx] at h; cases h
    | undefinedCondition _ => rw [hx] at h; cases h
    | trap => rw [hx] at h; cases h

theorem runL_within {code : List Byte} {base : Word} {L : List (LInstr × Nat)} {o : Nat}
    {m m' : MState} (hok : listingAt code o L = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : runL L m = some m') :
    RunsIn Open.isa (InCode Open.isa base code.length) m m' ∧ m'.memory = m.memory := by
  unfold runL ofX at h
  split at h
  · rename_i s mem' hx
    cases h
    exact execBlock_within L o m.core _ m.memory s mem' hok hl hrip hx
  · cases h

/-! ## Bir listings with a final write (`BlockCert.listingAtW`) -/

theorem execBlockW_within {code : List Byte} {base : Word} :
    ∀ (L : List (LInstr × Nat)) (o : Nat) (c : State) (x : Silmaril.X86.Lift.Bir.Xmm)
      (mem : Memory) (s' : XState) (mem' : Memory),
      listingAtW code o L = true → Loaded mem base code → c.rip = base + BitVec.ofNat 64 o →
      execBlock L ⟨c, x⟩ mem = .ok s' mem' →
      RunsIn Open.isa (InCode Open.isa base code.length) ⟨c, mem⟩ ⟨s'.core, mem'⟩
  | [], _, c, x, mem, s', mem', _, _, _, h => by
    simp only [execBlock] at h
    cases h
    exact .refl _
  | (i, l) :: rest, o, c, x, mem, s', mem', hok, hl, hrip, h => by
    simp only [listingAtW] at hok
    split at hok
    · cases hok
    rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hdec, hfit⟩, hft⟩, hrest⟩ := hok
    have hin : InCode Open.isa base code.length (⟨c, mem⟩ : MState) :=
      inCode_of (m := ⟨c, mem⟩) hrip hfit (len_pos ext_decode_nil hdec)
    simp only [execBlock] at h
    rw [execL_toExt he] at h
    cases hx : Silmaril.X86.Ext.exec e c mem l with
    | ok c1 m1 =>
      rw [hx] at h
      simp only [liftR] at h
      have hs : Open.step ⟨c, mem⟩ = some ⟨c1, m1⟩ :=
        Open.step_of_listed (m := ⟨c, mem⟩) hl hrip hfit (open_decode hdec) hx
      cases rest with
      | nil =>
        simp only [execBlock] at h
        cases h
        exact .step hin hs (.refl _)
      | cons nx rest' =>
        simp only [List.isEmpty_cons, Bool.false_or, Bool.and_eq_true] at hft
        have hm1 : m1 = mem := exec_mem hft.1 hx
        subst hm1
        have hrip1 : c1.rip = base + BitVec.ofNat 64 (o + l) := by
          rw [exec_rip hft.2 hx, hrip, BitVec.ofNat_add, BitVec.add_assoc]
        exact .step hin hs (execBlockW_within (nx :: rest') (o + l) c1 x m1 s' mem' hrest hl hrip1 h)
    | dataFault => rw [hx] at h; cases h
    | divideError => rw [hx] at h; cases h
    | undefinedCondition _ => rw [hx] at h; cases h
    | trap => rw [hx] at h; cases h

theorem runLW_within {code : List Byte} {base : Word} {L : List (LInstr × Nat)} {o : Nat}
    {m m' : MState} (hok : listingAtW code o L = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : runL L m = some m') :
    RunsIn Open.isa (InCode Open.isa base code.length) m m' := by
  unfold runL ofX at h
  split at h
  · rename_i s mem' hx
    cases h
    exact execBlockW_within L o m.core _ m.memory s mem' hok hl hrip hx
  · cases h

/-! ## `Ext8` listings (`BlockCert8.listing8`, checked runs `run8`) -/

open Silmaril.Machine.X86.BlockCert8 in
theorem run8_within {code : List Byte} {base : Word} :
    ∀ (L : List LI) (o : Nat) (m m' : MState),
      listing8 code o L = true → Loaded m.memory base code →
      m.core.rip = base + BitVec.ofNat 64 o → run8 L m = some m' →
      RunsIn Open.isa (InCode Open.isa base code.length) m m' ∧ m'.memory = m.memory
  | [], _, m, m', _, _, _, h => by
    simp only [run8, Option.some.injEq] at h
    subst h; exact ⟨.refl _, rfl⟩
  | (i, l) :: rest, o, m, m', hok, hl, hrip, h => by
    simp only [listing8, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hdec, hfit⟩, hrest⟩ := hok
    have hin : InCode Open.isa base code.length m :=
      inCode_of hrip hfit (len_pos open_decode_nil hdec)
    simp only [run8] at h
    split at h
    · rename_i c mem hx
      split at h
      · rename_i hc
        obtain ⟨hmem, hnext⟩ := hc
        subst hmem
        have hs : Open.step m = some ⟨c, m.memory⟩ :=
          Open.step_of_listed (m := m) hl hrip hfit hdec hx
        cases rest with
        | nil =>
          simp only [run8, Option.some.injEq] at h
          subst h
          exact ⟨.step hin hs (.refl _), rfl⟩
        | cons nx rest' =>
          have hrip1 : c.rip = base + BitVec.ofNat 64 (o + l) := by
            rcases hnext with h0 | h1
            · cases h0
            · rw [h1, hrip, BitVec.ofNat_add, BitVec.add_assoc]
          obtain ⟨hr, hm⟩ := run8_within (nx :: rest') (o + l) ⟨c, m.memory⟩ m' hrest hl hrip1 h
          exact ⟨.step hin hs hr, hm⟩
      · cases h
    · cases h

/-! ## `Ext9` block code (`BlockCert9.Code`) on `Open9.isa` -/

open Silmaril.Machine.X86.BlockCert9 in
theorem exec9_rip {i : Ext9.Instr} (hf : fallsThrough9 i = true) {s : State} {mem : Memory}
    {len : Nat} {s' : State} {mem' : Memory} (h : Ext9.exec i s mem len = .ok s' mem') :
    s'.rip = s.rip + BitVec.ofNat 64 len := by
  cases i with
  | ext8 i =>
    cases i with
    | base e => exact BlockCert.exec_rip hf h
    | new _ => cases hf
  | new n => exact execNew_rip hf h

open Silmaril.Machine.X86.BlockCert9 in
theorem exec9_mem {i : Ext9.Instr} (hf : noWrite9 i = true) {s : State} {mem : Memory}
    {len : Nat} {s' : State} {mem' : Memory} (h : Ext9.exec i s mem len = .ok s' mem') :
    mem' = mem := by
  cases i with
  | ext8 i =>
    cases i with
    | base e => exact BlockCert.exec_mem hf h
    | new _ => cases hf
  | new n => exact execNew_mem hf h

theorem inCode9_of {m : MState} {base : Word} {o l len : Nat}
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ len) (hl : 0 < l) :
    InCode Open9.isa base len m :=
  ⟨o, by omega, hrip⟩

open Silmaril.Machine.X86.BlockCert9 in
theorem runX_within {code : List Byte} {base : Word} :
    ∀ (L : List (Ext9.Instr × Nat)) (o : Nat) (m m' : MState),
      listingAt9 code o L = true → Loaded m.memory base code →
      m.core.rip = base + BitVec.ofNat 64 o → runX L m = some m' →
      RunsIn Open9.isa (InCode Open9.isa base code.length) m m' ∧ m'.memory = m.memory
  | [], _, m, m', _, _, _, h => by
    simp only [runX, Option.some.injEq] at h
    subst h
    exact ⟨.refl _, rfl⟩
  | (i, l) :: rest, o, m, m', hok, hl, hrip, h => by
    simp only [listingAt9, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hdec, hfit⟩, hnw⟩, hft⟩, hrest⟩ := hok
    have hin : InCode Open9.isa base code.length m :=
      inCode9_of hrip hfit (len_pos open9_decode_nil hdec)
    simp only [runX] at h
    split at h
    · rename_i c1 m1 hx
      have hm1 : m1 = m.memory := exec9_mem hnw hx
      have hs : Open9.step m = some ⟨c1, m1⟩ := Open9.step_of_listed hl hrip hfit hdec hx
      cases rest with
      | nil =>
        simp only [runX, Option.some.injEq] at h
        subst h
        exact ⟨.step hin hs (.refl _), hm1⟩
      | cons nx rest' =>
        simp only [List.isEmpty_cons, Bool.false_or] at hft
        have hrip1 : c1.rip = base + BitVec.ofNat 64 (o + l) := by
          rw [exec9_rip hft hx, hrip, BitVec.ofNat_add, BitVec.add_assoc]
        have hl1 : Loaded (⟨c1, m1⟩ : MState).memory base code := by
          show Loaded m1 base code; rw [hm1]; exact hl
        obtain ⟨hr, hm⟩ := runX_within (nx :: rest') (o + l) ⟨c1, m1⟩ m' hrest hl1 hrip1 h
        exact ⟨.step hin hs hr, hm.trans hm1⟩
    · cases h

open Silmaril.Machine.X86.BlockCert9 in
theorem code_run_within {code : List Byte} {base : Word} {c : Code} {o : Nat} {m m' : MState}
    (hok : c.check code o = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : c.run m = some m') :
    RunsIn Open9.isa (InCode Open9.isa base code.length) m m' ∧ m'.memory = m.memory := by
  cases c with
  | bir L =>
    obtain ⟨hr, hm⟩ := runL_within hok hl hrip h
    exact ⟨runsIn_map (fun hs => Open9.step_of_open hs) hr, hm⟩
  | x9 L => exact runX_within L o m m' hok hl hrip h

end Silmaril.Proofs.Machine.X86.Cert.Kinds
