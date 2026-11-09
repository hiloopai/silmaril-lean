module

public import Silmaril.X86.Sep.Ind.Defs
public import Silmaril.X86.Sep.Thms
public import Silmaril.Proofs.X86.Sep.Ind

/-!
# Proofs: the indirect `call`/`jmp` laws are not vacuous

Two concrete `Open9` states (one region mapping every address read/write/execute) that meet
the preconditions of the `mem` laws for the acceptance encodings, and the runs the laws then
give:

* `jmpM_run`: `jmp *0x38(%rdi)` (`FF 67 38`) at `0x400000`, `rdi = 0x6000`, the word
  `0x405678` at `0x6038`: the machine reaches `rip = 0x405678`.
* `callM_run`: `call *0x8(%rbx)` (`FF 53 08`) at `0x400000`, `rbx = 0x6000`, the word
  `0x401234` at `0x6008`, `rsp = 0x7000`: the machine reaches `rip = 0x401234`,
  `rsp = 0x6ff8`, with the return address `0x400003` stored at `0x6ff8`.

`HoldsIn P s D` (`P` holds of a part of `s` with domain in `D`) and `sep_in` assemble the
witness fragment from disjoint pieces. The laws used are `jmpM_open9`/`callM_open9` of
`Proofs/X86/Sep/Ind.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep.Ind.Witness

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region Permissions addressLimit)
open Silmaril.Machine.Execution (run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Ind
open Silmaril.X86.Sep.Frag (union Disjoint Le diff)
open Silmaril.X86.Safe (Progress)

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

theorem ripPt_in (m : MState) : HoldsIn (ripPt m.core.rip) (toFrag m) (· = .rip) :=
  ⟨_, rfl, single_le (s := toFrag m) rfl, single_dom⟩

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
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨i + 1, by simp; omega, by simp; omega⟩

theorem blockAny_in (m : MState) :
    ∀ (a n : Nat), (∀ i < n, a + i < addressLimit ∧ RW (permsAt m.memory (a + i))) →
      HoldsIn (blockAny a n) (toFrag m) (fun l => ∃ i < n, l = .mem (a + i))
  | a, 0, _ => mono_in (emp_in _) (fun _ h => h.elim)
  | a, n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    have hb : HoldsIn (byteAny a) (toFrag m) (· = .mem a) :=
      ⟨_, ⟨h0.1, _, h0.2, rfl⟩, single_le (s := toFrag m) rfl, single_dom⟩
    have ht := blockAny_in m (a + 1) n (fun i hi => by
      have := h (i + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    refine mono_in (sep_in hb ht ?_) ?_
    · rintro l rfl ⟨i, -, e⟩; simp at e; omega
    · rintro l (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · exact ⟨i + 1, by omega, by simp; omega⟩

/-- `P` holds of a part of `m`, so with the rest as frame `P ∗ ⊤` holds of all of `m`. -/
theorem sep_true_of_le {P : SProp} {h : Frag} {m : MState} (hp : P h) (hl : Le h (toFrag m)) :
    (P ∗ fun _ => True) (toFrag m) := by
  refine ⟨h, diff (toFrag m) h, fun l => ?_, ?_, hp, trivial⟩
  · simp only [diff]; cases e : h l <;> simp
  · funext l
    simp only [union, diff]
    cases e : h l with
    | none => simp
    | some v => simp [hl l v e]

theorem le_refl' (h : Frag) : Le h h := fun _ _ e => e

/-! ## A concrete state -/

def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩

/-- The code `bs` at `0x400000`, the word `p` at `0x6000 + off`. -/
def mem (bs : List Byte) (off : Nat) (p : Word) : Memory :=
  ⟨[allRegion], Memory.install (Memory.install ∅ (0x6000 + off) (encodeWords [p])) 0x400000 bs⟩

/-- `rip = 0x400000`, `rbx = rdi = 0x6000`, `rsp = 0x7000`. -/
def core : State :=
  ⟨fun r => match r with | .rbx => 0x6000 | .rdi => 0x6000 | .rsp => 0x7000 | _ => 0,
    0x400000, ⟨none, none, none, none, none, none⟩, 0⟩

theorem perms_all (bs : List Byte) (off : Nat) (p : Word) (a : Nat) (ha : a < 2 ^ 64) :
    permsAt (mem bs off p) a = ⟨true, true, true⟩ := by
  have : a < 18446744073709551616 := ha
  simp [permsAt, Memory.permits, mem, allRegion, Region.Contains, Permissions.allows, this]

theorem code_in (bs : List Byte) (off : Nat) (p : Word) (hbs : bs.length ≤ 0x1000) :
    HoldsIn (codePt (0x400000 : Word).toNat bs) (toFrag ⟨core, mem bs off p⟩)
      (fun l => ∃ i < bs.length, l = .mem (0x400000 + i)) := by
  rw [show (0x400000 : Word).toNat = 0x400000 from rfl]
  exact bytesAt_in (need := EX) _ _ bs (fun i hi => by
    refine ⟨by simp only [addressLimit]; omega, ?_, ?_⟩
    · exact Memory.install_get _ _ _ _ hi
    · show EX (permsAt (mem bs off p) _)
      rw [perms_all bs off p _ (by simp; omega)]; rfl)

theorem word_in (bs : List Byte) (off : Nat) (p : Word) (hbs : bs.length ≤ 0x1000)
    (hoff : off < 0x100) :
    HoldsIn (wordAt RO (0x6000 + off) p) (toFrag ⟨core, mem bs off p⟩)
      (fun l => ∃ i < 8, l = .mem (0x6000 + off + i)) := by
  have := bytesAt_in (need := RO) ⟨core, mem bs off p⟩ (0x6000 + off) (encodeWords [p])
    (fun i hi => by
      simp only [Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
        List.length_nil] at hi
      refine ⟨by simp only [addressLimit]; omega, ?_, ?_⟩
      · show (Memory.install _ _ _).get? _ = _
        rw [Memory.install_outside _ _ _ _ (by omega)]
        exact Memory.install_get _ _ _ _ (by simp; omega)
      · show RO (permsAt (mem bs off p) _)
        rw [perms_all bs off p _ (by omega)]; rfl)
  simpa [wordAt] using this

/-! ## `jmp *0x38(%rdi)` (`FF 67 38`, `longjmp`) -/

def mJ : MState := ⟨core, mem (encJmpM .rdi 0x38#8) 0x38 0x405678⟩

-- `simp` closes some of the memory cases, the tactic block the others.
set_option linter.unusedTactic false in
theorem jmpM_pre :
    ∃ h, (codePt (0x400000 : Word).toNat (encJmpM .rdi 0x38#8) ∗ ripPt 0x400000 ∗
      regPt .rdi 0x6000 ∗ wordAt RO (ea 0x6000 0x38#8).toNat 0x405678) h ∧ Le h (toFrag mJ) := by
  have hl : (encJmpM .rdi 0x38#8).length = 3 := by decide
  have hea : (ea 0x6000 0x38#8).toNat = 0x6000 + 0x38 := by decide
  rw [hea]
  have hD := sep_in (code_in (encJmpM .rdi 0x38#8) 0x38 0x405678 (by omega))
    (sep_in (ripPt_in mJ) (sep_in (regPt_in mJ .rdi)
      (word_in (encJmpM .rdi 0x38#8) 0x38 0x405678 (by omega) (by omega)) ?_) ?_) ?_
  · obtain ⟨h, hp, hl, -⟩ := hD; exact ⟨h, hp, hl⟩
  all_goals (intro l h1 h2; cases l with
    | reg r => cases r <;> simp_all
    | mem a =>
      simp only [hl, reduceCtorEq, Loc.mem.injEq, false_or] at h1 h2
      all_goals (obtain ⟨i, hi, rfl⟩ := h1
                 rcases h2 with ⟨j, hj, e⟩ | ⟨j, hj, e⟩ | ⟨j, hj, e⟩ <;> omega)
    | _ => simp_all)

/-- **The `jmp *d8(%base)` law is not vacuous**: the law applies to a concrete state and the
`Open9` machine reaches `rip = 0x405678`, the word at `rdi + 0x38`. -/
theorem jmpM_run : ∃ k m', run Open9.step (k + 1) mJ = some m' ∧ m'.core.rip = 0x405678 := by
  obtain ⟨h, hp, hl⟩ := jmpM_pre
  obtain ⟨k, m', hrun, hR⟩ :=
    Silmaril.Proofs.X86.Sep.Ind.jmpM_open9 (need := RO) (fun _ h => h)
      .rdi 0x38#8 0x400000 0x6000 0x405678 _ mJ trivial (sep_true_of_le hp hl)
  refine ⟨k, m', hrun, ?_⟩
  obtain ⟨_, -, hR, -, hlR, -, -, -⟩ := sep_le hR (le_refl' _)
  obtain ⟨_, hr, -, hr', -, hlr, -, -⟩ := sep_le hR hlR
  obtain ⟨_, -, hrip, -, hlrip, -, -, -⟩ := sep_le hr' hlr
  exact ripPt_le hrip hlrip

/-! ## `call *0x8(%rbx)` (`FF 53 08`, a method table) -/

def mC : MState := ⟨core, mem (encCallM .rbx 0x08#8) 0x08 0x401234⟩

-- `simp` closes some of the memory cases, the tactic block the others.
set_option linter.unusedTactic false in
theorem callM_pre :
    ∃ h, (codePt (0x400000 : Word).toNat (encCallM .rbx 0x08#8) ∗ ripPt 0x400000 ∗
      regPt .rbx 0x6000 ∗ wordAt RO (ea 0x6000 0x08#8).toNat 0x401234 ∗ regPt .rsp 0x7000 ∗
      blockAny ((0x7000 : Word).toNat - 8) 8) h ∧ Le h (toFrag mC) := by
  have hl : (encCallM .rbx 0x08#8).length = 3 := by decide
  have hea : (ea 0x6000 0x08#8).toNat = 0x6000 + 0x08 := by decide
  rw [hea, show (0x7000 : Word).toNat - 8 = 0x6ff8 from rfl]
  have hb := blockAny_in mC 0x6ff8 8 (fun i hi => by
    refine ⟨by simp only [addressLimit]; omega, ?_⟩
    show RW (permsAt (mem _ _ _) _)
    rw [perms_all _ _ _ _ (by omega)]; exact ⟨rfl, rfl⟩)
  have hD := sep_in (code_in (encCallM .rbx 0x08#8) 0x08 0x401234 (by omega))
    (sep_in (ripPt_in mC) (sep_in (regPt_in mC .rbx)
      (sep_in (word_in (encCallM .rbx 0x08#8) 0x08 0x401234 (by omega) (by omega))
        (sep_in (regPt_in mC .rsp) hb ?_) ?_) ?_) ?_) ?_
  · obtain ⟨h, hp, hl, -⟩ := hD; exact ⟨h, hp, hl⟩
  all_goals (intro l h1 h2; cases l with
    | reg r => cases r <;> simp_all
    | mem a =>
      simp only [hl, reduceCtorEq, Loc.mem.injEq, false_or] at h1 h2
      all_goals (obtain ⟨i, hi, rfl⟩ := h1
                 rcases h2 with ⟨j, hj, e⟩ | ⟨j, hj, e⟩ | ⟨j, hj, e⟩ <;> omega)
    | _ => simp_all)

/-- **The `call *d8(%base)` law is not vacuous**: the law applies to a concrete state and the `Open9`
machine reaches `rip = 0x401234` (the word at `rbx + 8`) with `rsp = 0x6ff8` and the return
address `0x400003` (after the three-byte call) stored at `0x6ff8`. -/
theorem callM_run : ∃ k m', run Open9.step (k + 1) mC = some m' ∧ m'.core.rip = 0x401234 ∧
    m'.core.read .rsp = 0x6ff8 ∧
    ∀ i (hi : i < 8), m'.memory.bytes.get? (0x6ff8 + i) = some (encodeWords [0x400003])[i] := by
  obtain ⟨h, hp, hl⟩ := callM_pre
  obtain ⟨k, m', hrun, hR⟩ :=
    Silmaril.Proofs.X86.Sep.Ind.callM_open9 (need := RO) (fun _ h => h)
      .rbx 0x08#8 0x400000 0x7000 0x6000 0x401234 (by decide) _ mC trivial (sep_true_of_le hp hl)
  refine ⟨k, m', hrun, ?_⟩
  obtain ⟨_, -, hR, -, hlR, -, -, -⟩ := sep_le hR (le_refl' _)
  obtain ⟨_, hr, -, hr, -, hlr, -, -⟩ := sep_le hR hlR
  obtain ⟨_, hr1, hrip, hr, hlrip, hlr, -, -⟩ := sep_le hr hlr
  obtain ⟨_, hr, -, hr, -, hlr, -, -⟩ := sep_le hr hlr
  obtain ⟨_, hr, -, hr, -, hlr, -, -⟩ := sep_le hr hlr
  obtain ⟨_, _, hsp, hw, hlsp, hlw, -, -⟩ := sep_le hr hlr
  refine ⟨ripPt_le hrip hlrip, regPt_le hsp hlsp, fun i hi => ?_⟩
  have e : nextPc 0x400000 (encCallM .rbx 0x08#8) = 0x400003 := by decide
  rw [e] at hw
  exact (bytesAt_le hw hlw i (by simpa using hi)).2.1

end Silmaril.Proofs.X86.Sep.Ind.Witness
