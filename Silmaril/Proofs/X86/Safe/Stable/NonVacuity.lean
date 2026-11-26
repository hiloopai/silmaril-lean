module

public import Silmaril.Proofs.X86.Safe.Stable.RightRot

/-!
# Proofs: `rightRot_tripleS` is not vacuous (a concrete state and a non-trivial frame)

A concrete machine state of which `RightRot.pre ∗ (regPt .rbx 7 ∗ strue)`
holds of the **whole** state: one region mapping every address read/write/execute,
`right_rot`'s 37 bytes at `0x400000`, the return address `0x401000` at `rsp = 0x7008`,
`rbp = 0x8000`, `rdi = 0x12345678`, `rsi = 3` and `rbx = 7`. Applying `rightRot_tripleS` with
the frame `regPt .rbx 7 ∗ strue` gives a run that returns to `0x401000`, and at every
intermediate state of that run `rbx` still reads `7` (the stability clause, read back as a
register value).

The `HoldsIn` helpers are copied from `Silmaril/Proofs/X86/Ladder/ListSL/NonVacuity.lean`
(itself a copy of track A's `Sep/Demo/NonVacuity`), which this module may not import.
-/

@[expose] public section

-- Some `try`/`all_goals` combinators below are needed on some goals only.
set_option linter.unusedTactic false

namespace Silmaril.Proofs.X86.SafeStable.NonVacuity

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region Permissions addressLimit)
open Silmaril.Machine.Execution (run)
open Silmaril.X86 Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le)
open Silmaril.X86.Safe

/-! ## `HoldsIn` (copied from `Ladder/ListSL/NonVacuity`) -/

/-- `P` holds of a part of `s` whose domain lies in `D`. -/
def HoldsIn (P : SProp) (s : Frag) (D : Loc → Prop) : Prop :=
  ∃ h, P h ∧ Le h s ∧ ∀ l, (h l).isSome → D l

theorem emp_in (s : Frag) : HoldsIn emp s (fun _ => False) :=
  ⟨Frag.empty, rfl, fun _ _ e => by simp [Frag.empty] at e, fun _ e => by simp [Frag.empty] at e⟩

theorem sep_in {P Q : SProp} {s : Frag} {D₁ D₂ : Loc → Prop} (hp : HoldsIn P s D₁)
    (hq : HoldsIn Q s D₂) (hd : ∀ l, D₁ l → D₂ l → False) :
    HoldsIn (P ∗ Q) s (fun l => D₁ l ∨ D₂ l) := by
  obtain ⟨h₁, hP, hl₁, hD₁⟩ := hp
  obtain ⟨h₂, hQ, hl₂, hD₂⟩ := hq
  have disj : Disjoint h₁ h₂ := by
    intro l
    cases e₁ : h₁ l with
    | none => exact .inl rfl
    | some v =>
      cases e₂ : h₂ l with
      | none => exact .inr rfl
      | some w => exact absurd (hd l (hD₁ l (by simp [e₁])) (hD₂ l (by simp [e₂]))) id
  refine ⟨union h₁ h₂, ⟨h₁, h₂, disj, rfl, hP, hQ⟩, ?_, ?_⟩
  · intro l v e
    simp only [Frag.union] at e
    cases e₁ : h₁ l with
    | none => rw [e₁] at e; exact hl₂ l v e
    | some u => rw [e₁] at e; cases e; exact hl₁ l _ e₁
  · intro l e
    simp only [Frag.union] at e
    cases e₁ : h₁ l with
    | none => rw [e₁] at e; exact .inr (hD₂ l e)
    | some u => exact .inl (hD₁ l (by simp [e₁]))

theorem mono_in {P : SProp} {s : Frag} {D D' : Loc → Prop} (hp : HoldsIn P s D)
    (hD : ∀ l, D l → D' l) : HoldsIn P s D' := by
  obtain ⟨h, a, b, c⟩ := hp; exact ⟨h, a, b, fun l e => hD l (c l e)⟩

theorem single_le {l : Loc} {v : Val} {s : Frag} (e : s l = some v) :
    Le (Frag.single l v) s := by
  intro l' w h; simp only [Frag.single] at h; split at h <;> simp_all

theorem single_dom {l : Loc} {v : Val} : ∀ l', (Frag.single l v l').isSome → l' = l := by
  intro l' h; simp only [Frag.single] at h; split at h <;> simp_all

theorem regPt_in (m : MState) (r : Reg) :
    HoldsIn (regPt r (m.core.read r)) (toFrag m) (· = .reg r) :=
  ⟨_, rfl, single_le (s := toFrag m) rfl, single_dom⟩

theorem regAny_in (m : MState) (r : Reg) : HoldsIn (regAny r) (toFrag m) (· = .reg r) := by
  obtain ⟨h, a, b, c⟩ := regPt_in m r; exact ⟨h, ⟨_, a⟩, b, c⟩

theorem ripPt_in (m : MState) : HoldsIn (ripPt m.core.rip) (toFrag m) (· = .rip) :=
  ⟨_, rfl, single_le (s := toFrag m) rfl, single_dom⟩

theorem flagsAny_in (m : MState) : HoldsIn flagsAny (toFrag m) (· = .flags) :=
  ⟨_, ⟨m.core.flags, rfl⟩, single_le (s := toFrag m) rfl, single_dom⟩

theorem bytesAt_in {need : Permissions → Prop} (m : MState) :
    ∀ (a : Nat) (bs : List Byte), (∀ i (hi : i < bs.length), a + i < addressLimit ∧
      m.memory.bytes.get? (a + i) = some bs[i] ∧ need (permsAt m.memory (a + i))) →
      HoldsIn (bytesAt need a bs) (toFrag m) (fun l => ∃ i < bs.length, l = .mem (a + i))
  | a, [], _ => mono_in (emp_in _) (fun _ h => h.elim)
  | a, b :: bs, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hb : HoldsIn (byteAt need a b) (toFrag m) (· = .mem a) := by
      refine ⟨Frag.single (.mem a) (.cell ⟨some b, permsAt m.memory a⟩),
        ⟨h0.1, _, h0.2.2, rfl⟩, single_le ?_, single_dom⟩
      simp only [toFrag, h0.2.1]
    have ht := bytesAt_in m (a + 1) bs (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    refine mono_in (sep_in hb ht ?_) ?_
    · rintro l rfl ⟨i, -, e⟩; simp at e; omega
    · rintro l (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by simp⟩
      · exact ⟨i + 1, by simp; omega, by simp; omega⟩

/-- `blockAny` analogue of `bytesAt_in` (new here). -/
theorem blockAny_in (m : MState) :
    ∀ (a n : Nat), (∀ i < n, a + i < addressLimit ∧ RW (permsAt m.memory (a + i))) →
      HoldsIn (blockAny a n) (toFrag m) (fun l => ∃ i < n, l = .mem (a + i))
  | a, 0, _ => mono_in (emp_in _) (fun _ h => h.elim)
  | a, n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    have hb : HoldsIn (byteAny a) (toFrag m) (· = .mem a) :=
      ⟨Frag.single (.mem a) (.cell ⟨m.memory.bytes.get? a, permsAt m.memory a⟩),
        ⟨h0.1, _, h0.2, rfl⟩, single_le (by simp only [toFrag]), single_dom⟩
    have ht := blockAny_in m (a + 1) n (fun i hi => by
      have := h (i + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    refine mono_in (sep_in hb ht ?_) ?_
    · rintro l rfl ⟨i, -, e⟩; simp at e; omega
    · rintro l (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · exact ⟨i + 1, by omega, by simp; omega⟩

/-! ## The concrete state -/

def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩
def entryAt : Word := 0x400000
def spAt : Word := 0x7008
def retAt : Word := 0x401000
def bpAt : Word := 0x8000
def vdi : Word := 0x12345678
def vsi : Word := 3

open Silmaril.Machine.LittleEndian (encodeWords) in
/-- Code at `0x400000`, the return address at `0x7008`. -/
def mem : Memory :=
  ⟨[allRegion],
    Memory.install (Memory.install ∅ spAt.toNat (encodeWords [retAt]))
      entryAt.toNat Silmaril.X86.Decompile.RightRot.code⟩

def core : State :=
  ⟨fun r => match r with
    | .rdi => vdi | .rsi => vsi | .rsp => spAt | .rbp => bpAt | .rbx => 7 | _ => 0,
    entryAt, ⟨none, none, none, none, none, none⟩, 0⟩

def m : MState := ⟨core, mem⟩

theorem perms_all (a : Nat) (ha : a < 2 ^ 64) : permsAt mem a = ⟨true, true, true⟩ := by
  have : a < 18446744073709551616 := ha
  simp [permsAt, Memory.permits, mem, allRegion, Region.Contains, Permissions.allows, this]

theorem code_length : Silmaril.X86.Decompile.RightRot.code.length = 37 := by decide

theorem get_ret (i : Nat) (hi : i < 8) : mem.bytes.get? (spAt.toNat + i) =
    (Silmaril.Machine.LittleEndian.encodeWords [retAt])[i]? := by
  have eS : spAt.toNat = 0x7008 := rfl
  have eE : entryAt.toNat = 0x400000 := rfl
  dsimp only [mem]
  rw [Memory.install_outside _ _ _ _ (by rw [eE, eS, code_length]; omega)]
  have hl : i < (Silmaril.Machine.LittleEndian.encodeWords [retAt]).length := by simp; omega
  rw [Memory.install_get _ _ _ i hl, List.getElem?_eq_getElem hl]

set_option linter.unusedSimpArgs false in
/-- **The precondition, with the frame `regPt .rbx 7`, holds of a part of `m`.** -/
theorem pre_holds :
    ∃ h, (RightRot.pre entryAt retAt spAt bpAt vdi vsi ∗ regPt .rbx 7) h ∧ Le h (toFrag m) := by
  have eE : entryAt.toNat = 0x400000 := rfl
  have eS : spAt.toNat = 0x7008 := rfl
  have hcode := bytesAt_in (need := EX) m entryAt.toNat Silmaril.X86.Decompile.RightRot.code
    (fun i hi => by
      rw [code_length] at hi
      refine ⟨by rw [eE]; simp only [addressLimit]; omega,
        Memory.install_get _ _ _ _ (by rw [code_length]; omega), ?_⟩
      show EX (permsAt mem _)
      rw [perms_all (entryAt.toNat + i) (by rw [eE]; omega)]; rfl)
  have hword := bytesAt_in (need := RW) m spAt.toNat
    (Silmaril.Machine.LittleEndian.encodeWords [retAt]) (fun i hi => by
      have hi' : i < 8 := by simpa using hi
      refine ⟨by rw [eS]; simp only [addressLimit]; omega, ?_, ?_⟩
      · show mem.bytes.get? _ = _
        rw [get_ret i hi', List.getElem?_eq_getElem hi]
      · show RW (permsAt mem _)
        rw [perms_all _ (by rw [eS]; omega)]; exact ⟨rfl, rfl⟩)
  have hblk := blockAny_in m (spAt.toNat - 16) 16 (fun i hi => by
    refine ⟨by rw [eS]; simp only [addressLimit]; omega, ?_⟩
    show RW (permsAt mem _)
    rw [perms_all _ (by rw [eS]; omega)]; exact ⟨rfl, rfl⟩)
  have hall := sep_in (sep_in hcode (sep_in (ripPt_in m) (sep_in (regPt_in m .rsp)
    (sep_in (regPt_in m .rbp) (sep_in (regPt_in m .rdi) (sep_in (regPt_in m .rsi)
    (sep_in (regAny_in m .rax) (sep_in (regAny_in m .rcx) (sep_in (regAny_in m .rdx)
    (sep_in (flagsAny_in m) (sep_in hblk hword ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_)
    (regPt_in m .rbx) ?_
  · obtain ⟨h, hp, hl, -⟩ := hall
    exact ⟨h, hp, hl⟩
  all_goals (intro l h1 h2; cases l with
    | reg r => cases r <;> simp_all
    | mem a =>
      try simp only [code_length, Silmaril.Machine.LittleEndian.encodeWords_length,
        List.length_cons, List.length_nil, reduceCtorEq, Loc.mem.injEq, false_or, or_false,
        eE, eS] at h1 h2
      all_goals (casesm* _ ∨ _, ∃ _, _, _ ∧ _ <;> omega)
    | _ => simp_all)

/-- `P` holding of a part of the state gives `P ∗ strue` of the whole state. -/
theorem sep_strue_of_le {P : SProp} {h s : Frag} (hp : P h) (hl : Le h s) : (P ∗ strue) s := by
  have := stable_of_le hp hl
  rwa [sep_comm] at this

/-- **Non-vacuity of `rightRot_tripleS`.** From the concrete state, the open machine runs to a
state that has returned to `0x401000` with `rsp = 0x7010` and `rbp = 0x8000`, and **at every
state of the run `rbx = 7`**: the frame `regPt .rbx 7 ∗ strue` is stable. -/
theorem rightRot_concrete :
    ∃ n fin, run Silmaril.X86.Open.step n m = some fin ∧
      fin.core.rip = retAt ∧ fin.core.read .rsp = spAt + 8#64 ∧ fin.core.read .rbp = bpAt ∧
      fin.core.read .rbx = 7 ∧
      ∀ k < n, ∀ mk, run Silmaril.X86.Open.step k m = some mk → mk.core.read .rbx = 7 := by
  obtain ⟨h, hp, hl⟩ := pre_holds
  have hwhole : (RightRot.pre entryAt retAt spAt bpAt vdi vsi ∗ (regPt .rbx 7 ∗ strue))
      (toFrag m) := by
    rw [← sep_assoc]; exact sep_strue_of_le hp hl
  have hT := RightRot.rightRot_tripleS entryAt retAt spAt bpAt vdi vsi
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n, fin, hr, hq, hs⟩ := hT _ m hwhole
  have hrefl : ∀ s : Frag, Le s s := fun _ _ _ e => e
  -- The final state.
  rw [← sep_assoc] at hq
  obtain ⟨a, -, hqa, -, hla, -, -, -⟩ := sep_le hq (hrefl _)
  obtain ⟨q, x, hqq, hx, hlq, hlx, -, -⟩ := sep_le hqa hla
  obtain ⟨c0, r0, -, r0P, -, hl0, -, -⟩ := sep_le hqq hlq
  obtain ⟨c1, r1, hrip, r1P, hl1, hlr1, -, -⟩ := sep_le r0P hl0
  obtain ⟨c2, r2, hrsp, r2P, hl2, hlr2, -, -⟩ := sep_le r1P hlr1
  obtain ⟨c3, -, hrbp, -, hl3, -, -, -⟩ := sep_le r2P hlr2
  refine ⟨n, fin, hr, ripPt_le hrip hl1, regPt_le hrsp hl2, regPt_le hrbp hl3,
    regPt_le hx hlx, fun k hk mk hrk => ?_⟩
  -- An intermediate state.
  have hk := hs k hk mk hrk
  obtain ⟨-, b, -, hb, -, hlb, -, -⟩ := sep_le hk (hrefl _)
  obtain ⟨c, -, hc, -, hlc, -, -, -⟩ := sep_le hb hlb
  exact regPt_le hc hlc

end Silmaril.Proofs.X86.SafeStable.NonVacuity
