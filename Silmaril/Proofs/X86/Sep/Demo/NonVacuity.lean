module

public import Silmaril.X86.Sep.Demo.Defs
public import Silmaril.X86.Sep.SysV.Thms
public import Silmaril.Proofs.X86.Sep.Demo.Leaf
/-!
# Proofs: the System V template is satisfiable

A concrete machine state of which `codePt leaf ∗ leafSpec.SysVPre (2, 3) leaf sp ret` holds:
one region mapping every address read/write/execute, the leaf code at `0x400000`, the
return address `0x401000` at `rsp = 0x7000`, `rdi = 2`, `rsi = 3`. So the template's
ownership (registers, flags, return slot, code, separated from each other) is not vacuous,
and `leaf_sat` applied to it gives a concrete open-machine run returning `rax = 5`.

`HoldsIn P s D` is `P` holding of a part of `s` whose domain lies in `D`; `sep_in` builds
`P ∗ Q` from parts with disjoint domain bounds.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SepDemo.NonVacuity

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region Permissions addressLimit)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Demo
open Silmaril.X86.Sep.Frag (union Disjoint Le)

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
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨i + 1, by simp; omega, by simp; omega⟩

/-! A concrete state: everything mapped read/write/execute, the leaf code at `0x400000`,
the return address `0x401000` at `rsp = 0x7000`, `rdi = 2`, `rsi = 3`. -/

def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩
def leafAt : Word := 0x400000
def spAt : Word := 0x7000
def retAt : Word := 0x401000

def mem : Memory :=
  ⟨[allRegion], Memory.install (Memory.install ∅ spAt.toNat
    (Silmaril.Machine.LittleEndian.encodeWords [retAt])) leafAt.toNat Silmaril.X86.Leaf.bytes⟩

def core : State :=
  ⟨fun r => match r with | .rdi => 2 | .rsi => 3 | .rsp => spAt | _ => 0, leafAt, ⟨none, none, none, none, none, none⟩, 0⟩

def m : MState := ⟨core, mem⟩

theorem perms_all (a : Nat) (ha : a < 2 ^ 64) : permsAt mem a = ⟨true, true, true⟩ := by
  have : a < 18446744073709551616 := ha
  simp [permsAt, Memory.permits, mem, allRegion, Region.Contains, Permissions.allows, this]

-- The location case split runs one tactic script on every location kind; the unused-tactic
-- linter flags the steps that only some kinds need.
set_option linter.unusedTactic false in
theorem leaf_pre_holds :
    ∃ h, ((codePt leafAt.toNat Silmaril.X86.Leaf.bytes ∗
      leafSpec.SysVPre ((2 : Word), (3 : Word)) leafAt spAt retAt) h) ∧ Le h (toFrag m) := by
  have eL : leafAt.toNat = 0x400000 := rfl
  have eS : spAt.toNat = 0x7000 := rfl
  have hcode := bytesAt_in (need := EX) m leafAt.toNat Silmaril.X86.Leaf.bytes (fun i hi => by
    simp only [Silmaril.X86.Leaf.bytes, List.length_cons, List.length_nil] at hi
    refine ⟨by rw [eL]; simp only [addressLimit]; omega,
      Memory.install_get _ _ _ _ (by simp [Silmaril.X86.Leaf.bytes]; omega), ?_⟩
    show EX (permsAt mem _)
    rw [perms_all (leafAt.toNat + i) (by rw [eL]; omega)]; rfl)
  have hword := bytesAt_in (need := RW) m spAt.toNat
      (Silmaril.Machine.LittleEndian.encodeWords [retAt]) (fun i hi => by
    simp only [Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
      List.length_nil] at hi
    refine ⟨by rw [eS]; simp only [addressLimit]; omega, ?_, ?_⟩
    · show (Memory.install _ _ _).get? _ = _
      rw [Memory.install_outside _ _ _ _ (by rw [eL, eS]; simp [Silmaril.X86.Leaf.bytes]; omega)]
      exact Memory.install_get _ _ _ _ (by simp; omega)
    · show RW (permsAt mem _)
      rw [perms_all (spAt.toNat + i) (by rw [eS]; omega)]; exact ⟨rfl, rfl⟩)
  have hArgs := sep_in (regPt_in m .rdi) (sep_in (regPt_in m .rsi) (sep_in (regAny_in m .rdx)
      (sep_in (regAny_in m .rcx) (sep_in (regAny_in m .r8) (sep_in (regAny_in m .r9) (emp_in _)
        ?_) ?_) ?_) ?_) ?_) ?_
  have hScr := sep_in (regAny_in m .rax) (sep_in (regAny_in m .r10) (sep_in (regAny_in m .r11)
      (emp_in _) ?_) ?_) ?_
  have hRegs := sep_in hArgs hScr ?_
  have hEntry := sep_in (ripPt_in m) (sep_in (regPt_in m .rsp) (sep_in hRegs
    (sep_in (flagsAny_in m) (sep_in hword (emp_in _) ?_) ?_) ?_) ?_) ?_
  have hD := sep_in hcode (sep_in hEntry (emp_in _) ?_) ?_
  · obtain ⟨h, hp, hl, -⟩ := hD
    exact ⟨h, hp, hl⟩
  all_goals (intro l h1 h2; cases l with
    | reg r => cases r <;> simp_all
    | mem a =>
      try simp only [Silmaril.X86.Leaf.bytes, Silmaril.Machine.LittleEndian.encodeWords_length,
        List.length_cons, List.length_nil, reduceCtorEq, Loc.mem.injEq, false_or, or_false]
        at h1 h2
      all_goals (obtain ⟨i, hi, rfl⟩ := h1; obtain ⟨j, hj, e⟩ := h2; omega)
    | _ => simp_all)


/-- The leaf spec, applied to the concrete state: the open machine returns to `retAt` with
`rax = 5`. -/
theorem leaf_concrete :
    ∃ fin, Silmaril.Machine.Execution.Reaches Silmaril.X86.Open.step m fin ∧
      fin.core.rip = retAt ∧ fin.core.read .rax = 5 ∧ fin.core.read .rsp = spAt + 8#64 := by
  obtain ⟨h, hp, hl⟩ := leaf_pre_holds
  obtain ⟨fin, h', hrun, hq, hl', -⟩ :=
    Triple.run (s := m) (leaf_sat leafAt (2, 3) spAt retAt trivial (by decide)) trivial hp hl
  obtain ⟨v, erip, ersp, erax, u, hu, -⟩ := FnSpec.sysVPost_le hq hl'
  exact ⟨fin, hrun, erip, by rw [erax, hu.2]; decide, ersp⟩

end Silmaril.Proofs.X86.SepDemo.NonVacuity
