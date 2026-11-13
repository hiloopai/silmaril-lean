module

public import Silmaril.Proofs.X86.Pool.Example
public import Silmaril.X86.Safe.Stable.Thms

/-!
# Proofs: two threads running the `right_rot` leaf

Two threads run the same `clang -O0` `right_rot` (37 bytes at `0x400000`, shared read-only)
on disjoint stacks (`rsp = 0x7008` and `0x9008`, return addresses `0x401000` and
`0x402000`). Each thread owns exactly `RightRot.pre` **without the code** (`rrPre`):
`rip`, `rsp`, `rbp`, `rdi`, `rsi`, `rax`, `rcx`, `rdx`, the flags, the sixteen frame bytes
below `rsp` and the return slot.

`rightRot_two_ownershipSafeEv` proves the pool `OwnershipSafeEv` (hence `OwnershipSafe`)
**under the hypothesis** `RightRotLocal` (in the header: `Task.rightRotLocal`): `right_rot`
meets the footprint triple `LTripleEv` with the code as read-only context. The existing
proof gives only the stable triple `rightRot_tripleS`, whose run proof fixes the frame for the
whole run, so it does not give `LTriple`. The hypothesis is proved per step (`RightRotLocal.lean`,
`rightRotLocal`), so the header states the pool results unconditionally. Everything else (the
concrete state, the fragments, their disjointness, the side conditions) is proved here.
-/

@[expose] public section

-- Some `try`/`all_goals` combinators below are needed on some goals only.
set_option linter.unusedTactic false

namespace Silmaril.Proofs.X86.Pool.RightRotPool

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region Permissions addressLimit)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86.Decompile.RightRot (code rightRotSpec)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le)
open Silmaril.X86.Pool
open Silmaril.Proofs.X86.Pool
open Silmaril.Proofs.X86.Pool.Example (HoldsIn sep_in mono_in emp_in single_le single_dom
  regPt_in ripPt_in bytesAt_in disjoint_of_dom retFin allRegion)

/-- `RightRot.pre` without the code: what one thread owns. -/
def rrPre (e ret sp bp vdi vsi : Word) : SProp :=
  ripPt e ∗ regPt .rsp sp ∗ regPt .rbp bp ∗ regPt .rdi vdi ∗
    regPt .rsi vsi ∗ regAny .rax ∗ regAny .rcx ∗ regAny .rdx ∗ flagsAny ∗
    blockAny (sp.toNat - 16) 16 ∗ wordPt sp.toNat ret

/-- `RightRot.post` without the code. -/
def rrPost (ret sp bp vdi vsi : Word) : SProp :=
  ripPt ret ∗ regPt .rsp (sp + 8#64) ∗ regPt .rbp bp ∗ regPt .rdi vdi ∗
    regPt .rsi vsi ∗
    Silmaril.X86.Safe.RightRot.raxLow32
      (rightRotSpec (vdi.setWidth 32) (vsi.setWidth 32).toNat) ∗
    regAny .rcx ∗ regAny .rdx ∗ flagsAny ∗ blockAny (sp.toNat - 16) 16 ∗ wordPt sp.toNat ret

/-- **`right_rot` as a footprint triple** (proved in `RightRotLocal.lean`; `LTripleEv` on `openEv`, whose step is
`Open.step`), with its code as the read-only context, under the side conditions and a return
address outside the code: frame-requantified safety, and every fetch, read and write within
the owned fragment and the code. -/
def RightRotLocal : Prop :=
  ∀ (e ret sp bp vdi vsi : Word), 16 ≤ sp.toNat →
    (e.toNat + 37 ≤ sp.toNat - 16 ∨ sp.toNat ≤ e.toNat) →
    0 < (vsi.setWidth 32).toNat → (vsi.setWidth 32).toNat < 32 →
    (ret.toNat < e.toNat ∨ e.toNat + 37 ≤ ret.toNat) →
    ∀ n, LTripleEv openEv (retFin ret) (codePt e.toNat code)
      (rrPre e ret sp bp vdi vsi) (rrPost ret sp bp vdi vsi) n

/-! ## The concrete pool -/

def codeAt : Word := 0x400000
def bpAt : Word := 0x8000
def vdi : Word := 0x12345678
def vsi : Word := 3

/-- Thread `t`'s stack pointer. -/
def sp (t : Bool) : Word := if t then 0x7008 else 0x9008
/-- Thread `t`'s return address. -/
def retOf (t : Bool) : Word := if t then 0x401000 else 0x402000

theorem sp_toNat (t : Bool) : (sp t).toNat = if t then 0x7008 else 0x9008 := by
  cases t <;> rfl

/-- `right_rot` at `0x400000`, the return addresses at `0x7008` and `0x9008`. -/
def mem : Memory :=
  ⟨[allRegion],
    Memory.install (Memory.install (Memory.install ∅ (sp true).toNat (encodeWords [retOf true]))
      (sp false).toNat (encodeWords [retOf false])) codeAt.toNat code⟩

def core (t : Bool) : State :=
  ⟨fun r => match r with
    | .rdi => vdi | .rsi => vsi | .rsp => sp t | .rbp => bpAt | _ => 0,
    codeAt, ⟨none, none, none, none, none, none⟩, 0⟩

/-- The two-thread `right_rot` pool. -/
def pool : Pool Bool := ⟨fun t => some (core t), mem⟩

def fin (t : Bool) (c : State) : Prop := retFin (retOf t) c

theorem perms_all (a : Nat) (ha : a < 2 ^ 64) : permsAt mem a = ⟨true, true, true⟩ := by
  have : a < 18446744073709551616 := ha
  simp [permsAt, Memory.permits, mem, allRegion, Region.Contains, Permissions.allows, this]

theorem code_length : code.length = 37 := by decide

theorem get_code (i : Nat) (hi : i < code.length) :
    mem.bytes.get? (codeAt.toNat + i) = some Silmaril.X86.Decompile.RightRot.code[i] :=
  Memory.install_get _ _ _ i hi

theorem get_word (t : Bool) (i : Nat) (hi : i < 8) : mem.bytes.get? ((sp t).toNat + i) =
    (encodeWords [retOf t])[i]? := by
  have eC : codeAt.toNat = 0x400000 := rfl
  have hl : i < (encodeWords [retOf t]).length := by simp; omega
  dsimp only [mem]
  cases t with
  | true =>
    rw [Memory.install_outside _ _ _ _ (by rw [eC, sp_toNat, code_length]; simp; omega),
      Memory.install_outside _ _ _ _ (by rw [sp_toNat, sp_toNat]; simp; omega),
      Memory.install_get _ _ _ i hl, List.getElem?_eq_getElem hl]
  | false =>
    rw [Memory.install_outside _ _ _ _ (by rw [eC, sp_toNat, code_length]; simp; omega),
      Memory.install_get _ _ _ i hl, List.getElem?_eq_getElem hl]

theorem regAny_in (m : MState) (r : Reg) : HoldsIn (regAny r) (toFrag m) (· = .reg r) := by
  obtain ⟨h, a, b, c⟩ := regPt_in m r; exact ⟨h, ⟨_, a⟩, b, c⟩

theorem flagsAny_in (m : MState) : HoldsIn flagsAny (toFrag m) (· = .flags) :=
  ⟨_, ⟨m.core.flags, rfl⟩, single_le (s := toFrag m) rfl, single_dom⟩

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

/-- The owned domain of thread `t`: local locations, and the 24 stack bytes from `sp - 16`. -/
def dom (t : Bool) (l : Loc) : Prop :=
  l.isLocal = true ∨ ∃ i < 24, l = .mem ((sp t).toNat - 16 + i)

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
theorem thread_holds (t : Bool) :
    HoldsIn (rrPre codeAt (retOf t) (sp t) bpAt vdi vsi) (toFrag ⟨core t, mem⟩) (dom t) := by
  let m : MState := ⟨core t, mem⟩
  have hspn : 16 ≤ (sp t).toNat ∧ (sp t).toNat + 8 < 2 ^ 64 := by
    rw [sp_toNat]; split <;> omega
  have hword := bytesAt_in (need := RW) m (sp t).toNat (encodeWords [retOf t]) (fun i hi => by
    have hi' : i < 8 := by simpa using hi
    refine ⟨by simp only [addressLimit]; omega, ?_, ?_⟩
    · show mem.bytes.get? _ = _
      rw [get_word t i hi', List.getElem?_eq_getElem hi]
    · show RW (permsAt mem _)
      rw [perms_all _ (by omega)]; exact ⟨rfl, rfl⟩)
  have hblk := blockAny_in m ((sp t).toNat - 16) 16 (fun i hi => by
    refine ⟨by simp only [addressLimit]; omega, ?_⟩
    show RW (permsAt mem _)
    rw [perms_all _ (by omega)]; exact ⟨rfl, rfl⟩)
  have hall := sep_in (ripPt_in m) (sep_in (regPt_in m .rsp)
    (sep_in (regPt_in m .rbp) (sep_in (regPt_in m .rdi) (sep_in (regPt_in m .rsi)
    (sep_in (regAny_in m .rax) (sep_in (regAny_in m .rcx) (sep_in (regAny_in m .rdx)
    (sep_in (flagsAny_in m) (sep_in hblk hword ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · have e1 : m.core.rip = codeAt := rfl
    have e2 : m.core.read .rsp = sp t := rfl
    have e3 : m.core.read .rbp = bpAt := rfl
    have e4 : m.core.read .rdi = vdi := rfl
    have e5 : m.core.read .rsi = vsi := rfl
    rw [e1, e2, e3, e4, e5] at hall
    refine mono_in hall (fun l h => ?_)
    rcases h with h | h | h | h | h | h | h | h | h | ⟨i, hi, h⟩ | ⟨i, hi, h⟩
    all_goals first
      | (left; subst h; rfl)
      | (right; exact ⟨i, by omega, h⟩)
      | (right; refine ⟨16 + i, by simp at hi; omega, ?_⟩; rw [h]; congr 1; omega)
  all_goals (intro l h1 h2; cases l with
    | reg r => cases r <;> simp_all
    | mem a =>
      simp only [Loc.mem.injEq, reduceCtorEq, false_or, or_false,
        Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
        List.length_nil] at h1 h2
      all_goals (casesm* _ ∨ _, ∃ _, _, _ ∧ _; omega)
    | _ => simp_all)

/-- The code's domain. -/
def cdom (l : Loc) : Prop := ∃ i < 37, l = .mem (codeAt.toNat + i)

theorem code_holds (c : State) : HoldsIn (codePt codeAt.toNat code) (toFrag ⟨c, mem⟩) cdom := by
  have := bytesAt_in (need := EX) ⟨c, mem⟩ codeAt.toNat code (fun i hi => by
    have eC : codeAt.toNat = 0x400000 := rfl
    rw [code_length] at hi
    refine ⟨by rw [eC]; simp only [addressLimit]; omega, get_code i (by rw [code_length]; omega),
      ?_⟩
    show EX (permsAt mem _)
    rw [perms_all _ (by rw [eC]; omega)]; rfl)
  exact mono_in this (fun l ⟨i, hi, h⟩ => ⟨i, by rw [code_length] at hi; exact hi, h⟩)

theorem dom_cdom (t : Bool) (l : Loc) (h₁ : dom t l) (h₂ : cdom l) : False := by
  obtain ⟨j, hj, rfl⟩ := h₂
  rcases h₁ with h | ⟨i, hi, h⟩
  · cases h
  · have eC : codeAt.toNat = 0x400000 := rfl
    simp only [Loc.mem.injEq, sp_toNat, eC] at h
    split at h <;> omega

theorem dom_dom (l : Loc) (hl : l.isLocal = false) (h₁ : dom true l) (h₂ : dom false l) :
    False := by
  rcases h₁ with h | ⟨i, hi, rfl⟩
  · rw [hl] at h; cases h
  · rcases h₂ with h' | ⟨j, hj, h'⟩
    · cases h'
    · simp only [Loc.mem.injEq, sp_toNat, ite_true, Bool.false_eq_true, ite_false] at h'
      omega

theorem shared_disjoint_dom {hT hF : Frag} (dT : ∀ l, (hT l).isSome → dom true l)
    (dF : ∀ l, (hF l).isSome → dom false l) (l : Loc) (hl : l.isLocal = false) :
    hT l = none ∨ hF l = none := by
  cases e₁ : hT l with
  | none => exact .inl rfl
  | some v =>
    cases e₂ : hF l with
    | none => exact .inr rfl
    | some w => exact (dom_dom l hl (dT l (by simp [e₁])) (dF l (by simp [e₂]))).elim

theorem side (t : Bool) :
    16 ≤ (sp t).toNat ∧ (codeAt.toNat + 37 ≤ (sp t).toNat - 16 ∨ (sp t).toNat ≤ codeAt.toNat) ∧
    0 < (vsi.setWidth 32).toNat ∧ (vsi.setWidth 32).toNat < 32 ∧
    ((retOf t).toNat < codeAt.toNat ∨ codeAt.toNat + 37 ≤ (retOf t).toNat) := by
  cases t <;> decide

/-- **The two-thread `right_rot` pool is ownership-safe, if `right_rot` meets the
footprint triple** (`RightRotLocal`). -/
theorem rightRot_two_ownershipSafeEv (h : RightRotLocal) : OwnershipSafeEv openEv fin pool := by
  obtain ⟨hT, pT, lT, dT⟩ := thread_holds true
  obtain ⟨hF, pF, lF, dF⟩ := thread_holds false
  obtain ⟨r, pr, lr, dr⟩ := code_holds (core true)
  have hrS : SharedOnly r := by
    intro l hl
    cases e : r l with
    | none => rfl
    | some v =>
      obtain ⟨i, -, rfl⟩ := dr l (by simp [e])
      cases hl
  have hdr : ∀ t : Bool, Disjoint (if t then hT else hF) r := by
    intro t; cases t
    · exact disjoint_of_dom dF dr (dom_cdom false)
    · exact disjoint_of_dom dT dr (dom_cdom true)
  have dTF : PFrag.Disjoint (embed true hT) (embed false hF) :=
    disjoint_embed_ne (by decide) (shared_disjoint_dom dT dF)
  refine ⟨fun t => if t then hT else hF, r, fun t => rrPost (retOf t) (sp t) bpAt vdi vsi, hrS,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; simp [pool] at ht
  · intro t t' htt
    cases t <;> cases t'
    · exact absurd rfl htt
    · exact PF.disjoint_symm dTF
    · exact dTF
    · exact absurd rfl htt
  · intro t; exact disjoint_embed_embedS (hdr t)
  · intro t
    apply embed_le_poolFrag (c := core t) rfl
    cases t
    · exact lF
    · exact lT
  · exact embedS_le_poolFrag (c := core true) lr
  · intro t c ht n
    simp only [pool, Option.some.injEq] at ht
    subst ht
    have hp : rrPre codeAt (retOf t) (sp t) bpAt vdi vsi (if t then hT else hF) := by
      cases t
      · exact pF
      · exact pT
    obtain ⟨s1, s2, s3, s4, s5⟩ := side t
    exact h codeAt (retOf t) (sp t) bpAt vdi vsi s1 s2 s3 s4 s5 n (core t) _ r pr hp (hdr t)

/-- The same pool is `OwnershipSafe` on `Open.step`, under `RightRotLocal`. -/
theorem rightRot_two_ownershipSafe (h : RightRotLocal) :
    OwnershipSafe Silmaril.X86.Open.step fin pool := by
  rw [← openEv_step]; exact OwnershipSafeEv.toOwnershipSafe (rightRot_two_ownershipSafeEv h)

end Silmaril.Proofs.X86.Pool.RightRotPool
