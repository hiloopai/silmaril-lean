module

public import Silmaril.X86.Stencils.ByteLoop.Defs
public import Silmaril.X86.Sep.SysV.Thms

/-!
# Byte-loop stencils: from state-level contracts to System V separation-logic specs

`copy_sat`, `fill_sat`, `scan_sat` apply `FnSpec.sat_of_fnContract`: every entry fact of the
state-level contract is read off the separation-logic precondition (atoms give permissions,
backing and bounds; separation gives the `Apart` facts), the contract's footprint is owned
by the precondition, and the postcondition's fragments are re-valued in the final state.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Stencils.ByteLoop

open Silmaril.X86 (MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory addressLimit)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.X86.Stencils.ByteLoop

/-! ## Fragments -/

theorem isSome_union {a b : Frag} {l : Loc} : (union a b l).isSome ↔ (a l).isSome ∨ (b l).isSome := by
  unfold union; cases a l <;> simp

theorem le_union_left {a b s : Frag} (h : Le (union a b) s) : Le a s := fun l v hl =>
  h l v (by simp [union, hl])

theorem le_union_right {a b s : Frag} (hd : Disjoint a b) (h : Le (union a b) s) : Le b s :=
  fun l v hl => h l v (by
    rcases hd l with e | e
    · simp [union, e, hl]
    · rw [e] at hl; cases hl)

theorem disjoint_union {a b c : Frag} (h : Disjoint a (union b c)) : Disjoint a b ∧ Disjoint a c := by
  constructor <;> intro l <;> rcases h l with e | e
  all_goals try exact .inl e
  all_goals right; unfold union at e; cases hb : b l <;> simp_all

theorem disjoint_symm {a b : Frag} (h : Disjoint a b) : Disjoint b a := fun l => (h l).symm

theorem not_both {a b : Frag} (h : Disjoint a b) {l : Loc} (ha : (a l).isSome)
    (hb : (b l).isSome) : False := by
  rcases h l with e | e <;> simp_all

theorem dom_left {P Q : SProp} {h : Frag} (hpq : (P ∗ Q) h) {l : Loc}
    (k : ∀ a, P a → (a l).isSome) : (h l).isSome := by
  obtain ⟨a, b, _, rfl, ha, _⟩ := hpq
  exact isSome_union.mpr (.inl (k a ha))

theorem dom_right {P Q : SProp} {h : Frag} (hpq : (P ∗ Q) h) {l : Loc}
    (k : ∀ b, Q b → (b l).isSome) : (h l).isSome := by
  obtain ⟨a, b, _, rfl, _, hb⟩ := hpq
  exact isSome_union.mpr (.inr (k b hb))

/-- Owned intervals of disjoint fragments are apart. -/
theorem apart_of_disjoint {h₁ h₂ : Frag} (hd : Disjoint h₁ h₂) {a n b k : Nat}
    (h1 : ∀ i < n, (h₁ (.mem (a + i))).isSome) (h2 : ∀ j < k, (h₂ (.mem (b + j))).isSome) :
    Apart a n b k := by
  unfold Apart
  by_contra hc
  rcases Nat.le_total a b with hab | hab
  · have x1 := h1 (b - a) (by omega)
    have x2 := h2 0 (by omega)
    rw [show a + (b - a) = b by omega] at x1
    rw [Nat.add_zero] at x2
    exact not_both hd x1 x2
  · have x1 := h1 0 (by omega)
    have x2 := h2 (a - b) (by omega)
    rw [show b + (a - b) = a by omega] at x2
    rw [Nat.add_zero] at x1
    exact not_both hd x1 x2

theorem reval_empty (s : Frag) : reval Frag.empty s = Frag.empty := by
  funext l; simp [reval, Frag.empty]

/-- The entry template owns the return slot. -/
theorem slot_owned {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    (hT : S.SysVEntry x entry sp ret h) : ∀ i < 8, (h (.mem (sp.toNat + i))).isSome := by
  intro i hi
  refine dom_right hT fun _ h1 => dom_right h1 fun _ h2 => dom_right h2 fun _ h3 =>
    dom_right h3 fun _ h4 => dom_left h4 fun _ h5 => ?_
  exact bytesAt_dom h5 i (by simp; omega)

theorem permsAt_eq {mem mem' : Memory} {fp : Nat → Prop} (hw : mem.WritesWithin mem' fp)
    (a : Nat) : permsAt mem' a = permsAt mem a := by
  simp [permsAt, Memory.permits, hw.1]

/-! ## The common entry reading -/

/-- What every stencil reads off the template and the code: the program counter, `rsp`,
the argument registers, the loaded code, and the pieces of the precondition's fragments. -/
structure EntryRead (S : FnSpec) (code : List Byte) (entry : Word) (x : S.Arg) (sp : Word)
    (m : MState) (hc ht hu : Frag) : Prop where
  rip : m.core.rip = entry
  rsp : m.core.read .rsp = sp
  loaded : Loaded m.memory entry code
  lt : Le ht (toFrag m)
  lu : Le hu (toFrag m)
  dcu : Disjoint hc hu
  dtu : Disjoint ht hu
  codeOwn : ∀ i < code.length, (hc (.mem (entry.toNat + i))).isSome
  slotOwn : ∀ i < 8, (ht (.mem (sp.toNat + i))).isSome

theorem entryRead {S : FnSpec} {code : List Byte} {entry : Word} (hne : code ≠ [])
    {x : S.Arg} {sp ret : Word} {m : MState} {hc ht hu : Frag}
    (hcP : codePt entry.toNat code hc) (htP : S.SysVEntry x entry sp ret ht)
    (hd1 : Disjoint hc (union ht hu)) (hd2 : Disjoint ht hu)
    (hl : Le (union hc (union ht hu)) (toFrag m)) : EntryRead S code entry x sp m hc ht hu := by
  have hlr := le_union_right hd1 hl
  have hlt := le_union_left hlr
  exact ⟨FnSpec.sysVEntry_rip htP hlt, FnSpec.sysVEntry_rsp htP hlt,
    fetchBytes_of_codePt hne hcP (le_union_left hl), hlt, le_union_right hd2 hlr,
    (disjoint_union hd1).2, hd2, fun i hi => bytesAt_dom hcP i hi, slot_owned htP⟩

theorem arg_toNat {w : Word} {n : Nat} (h : w = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    w.toNat = n := by
  subst h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-! ## `Copy` -/

theorem copy_sat {code : List Byte} {entry : Word} (hne : code ≠ [])
    (hK : (copyContract code entry).Total Silmaril.X86.Open.isa) :
    copySpec.Sat Silmaril.X86.Open.isa (codePt entry.toNat code) entry := by
  apply FnSpec.sat_of_fnContract ⟨copyContract code entry, hK⟩
  intro x sp0 ret m hc ht hu _ _ hcP htP huP hd1 hd2 hl
  have R := entryRead hne hcP htP hd1 hd2 hl
  obtain ⟨⟨hlen, hsmall⟩, hbuf⟩ := (spure_sep_apply _ _ _).mp huP
  obtain ⟨ho, hi, hdoi, rfl, hoP, hiP⟩ := hbuf
  have hlo := le_union_left R.lu
  have hli := le_union_right hdoi R.lu
  have e0 := FnSpec.sysVEntry_args htP R.lt 0 (by decide) (by simp [copySpec])
  have e1 := FnSpec.sysVEntry_args htP R.lt 1 (by decide) (by simp [copySpec])
  have e2 := FnSpec.sysVEntry_args htP R.lt 2 (by decide) (by simp [copySpec])
  simp only [argRegs, copySpec, List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2
  have a0 : arg0 m = x.d.toNat := by simp [arg0, e0]
  have a1 : arg1 m = x.s.toNat := by simp [arg1, e1]
  have a2 : arg2 m = x.src.length := arg_toNat e2 hsmall
  have hob := fun i (h : i < x.old.length) => bytesAt_le hoP hlo i h
  have hib := fun i (h : i < x.src.length) => bytesAt_le hiP hli i h
  have ownO : ∀ i < x.src.length, (ho (.mem (x.d.toNat + i))).isSome :=
    fun i h => bytesAt_dom hoP i (by omega)
  have ownI : ∀ i < x.src.length, (hi (.mem (x.s.toNat + i))).isSome :=
    fun i h => bytesAt_dom hiP i h
  have dCO := (disjoint_union R.dcu).1
  have dTO := (disjoint_union R.dtu).1
  refine ⟨⟨R.rip, R.loaded, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [a0, a2]; intro i h
    obtain ⟨b1, -, b3⟩ := hob i (by omega)
    exact ⟨b1, b3.2⟩
  · rw [a1, a2]; intro i h
    obtain ⟨b1, b2, b3⟩ := hib i h
    exact ⟨b1, b3, by rw [b2]; rfl⟩
  · rw [a0, a1, a2]; exact apart_of_disjoint hdoi ownO ownI
  · rw [a0, a2]; exact apart_of_disjoint (disjoint_symm dCO) ownO R.codeOwn
  · rw [a0, a2, Silmaril.X86.Stencils.ByteLoop.sp, R.rsp]; exact apart_of_disjoint (disjoint_symm dTO) ownO R.slotOwn
  · intro a ⟨h1, h2⟩
    simp only [a0, a2] at h1 h2
    have := ownO (a - x.d.toNat) (by omega)
    rw [show x.d.toNat + (a - x.d.toNat) = a by omega] at this
    exact isSome_union.mpr (.inr (isSome_union.mpr (.inl this)))
  · intro fin ⟨hrax, hw, hcopy⟩
    simp only [a0, a1, a2] at hcopy hw
    have apOI : Apart x.d.toNat x.src.length x.s.toNat x.src.length :=
      apart_of_disjoint hdoi ownO ownI
    refine (spure_sep_apply _ _ _).mpr ⟨by rw [hrax, e0], ?_⟩
    refine sep_reval _ ⟨ho, hi, hdoi, rfl, hoP, hiP⟩ (fun a ha => ?_) (fun b hb => ?_)
    · refine bytesAt_reval ha hlen.symm fun i h => ⟨?_, ?_⟩
      · rw [hcopy i h]; exact (hib i h).2.1
      · rw [permsAt_eq hw]; exact (hob i (by omega)).2.2
    · refine bytesAt_reval hb rfl fun i h => ⟨?_, ?_⟩
      · rw [hw.2 _ (by unfold Apart at apOI; omega)]; exact (hib i h).2.1
      · rw [permsAt_eq hw]; exact (hib i h).2.2

/-! ## `Fill` -/

theorem fill_sat {code : List Byte} {entry : Word} (hne : code ≠ [])
    (hK : (fillContract code entry).Total Silmaril.X86.Open.isa) :
    fillSpec.Sat Silmaril.X86.Open.isa (codePt entry.toNat code) entry := by
  apply FnSpec.sat_of_fnContract ⟨fillContract code entry, hK⟩
  intro x sp0 ret m hc ht hu _ _ hcP htP huP hd1 hd2 hl
  have R := entryRead hne hcP htP hd1 hd2 hl
  obtain ⟨hsmall, hoP⟩ := (spure_sep_apply _ _ _).mp huP
  have e0 := FnSpec.sysVEntry_args htP R.lt 0 (by decide) (by simp [fillSpec])
  have e1 := FnSpec.sysVEntry_args htP R.lt 1 (by decide) (by simp [fillSpec])
  have e2 := FnSpec.sysVEntry_args htP R.lt 2 (by decide) (by simp [fillSpec])
  simp only [argRegs, fillSpec, List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2
  have a0 : arg0 m = x.d.toNat := by simp [arg0, e0]
  have a2 : arg2 m = x.old.length := arg_toNat e2 hsmall
  have hob := fun i (h : i < x.old.length) => bytesAt_le hoP R.lu i h
  have ownO : ∀ i < x.old.length, (hu (.mem (x.d.toNat + i))).isSome :=
    fun i h => bytesAt_dom hoP i h
  refine ⟨⟨R.rip, R.loaded, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [a0, a2]; intro i h
    obtain ⟨b1, -, b3⟩ := hob i h
    exact ⟨b1, b3.2⟩
  · rw [a0, a2]; exact apart_of_disjoint (disjoint_symm R.dcu) ownO R.codeOwn
  · rw [a0, a2, Silmaril.X86.Stencils.ByteLoop.sp, R.rsp]; exact apart_of_disjoint (disjoint_symm R.dtu) ownO R.slotOwn
  · intro a ⟨h1, h2⟩
    simp only [a0, a2] at h1 h2
    have := ownO (a - x.d.toNat) (by omega)
    rw [show x.d.toNat + (a - x.d.toNat) = a by omega] at this
    exact isSome_union.mpr (.inr this)
  · intro fin ⟨hrax, hw, hfill⟩
    simp only [a0, a2, e1] at hfill
    simp only [a0, a2] at hw
    refine (spure_sep_apply _ _ _).mpr ⟨by rw [hrax, e0], ?_⟩
    refine bytesAt_reval hoP (by simp) fun i h => ⟨?_, ?_⟩
    · simp only [List.length_replicate] at h
      rw [hfill i h]; simp
    · simp only [List.length_replicate] at h
      rw [permsAt_eq hw]; exact (hob i h).2.2

/-! ## `Scan` -/

theorem scan_sat {code : List Byte} {entry : Word} (hne : code ≠ [])
    (hK : (scanContract code entry).Total Silmaril.X86.Open.isa) :
    scanSpec.Sat Silmaril.X86.Open.isa (codePt entry.toNat code) entry := by
  apply FnSpec.sat_of_fnContract ⟨scanContract code entry, hK⟩
  intro x sp0 ret m hc ht hu _ _ hcP htP huP hd1 hd2 hl
  have R := entryRead hne hcP htP hd1 hd2 hl
  obtain ⟨hnz, hsP⟩ := (spure_sep_apply _ _ _).mp huP
  have e0 := FnSpec.sysVEntry_args htP R.lt 0 (by decide) (by simp [scanSpec])
  simp only [argRegs, scanSpec, List.getElem_cons_zero] at e0
  have a0 : arg0 m = x.s.toNat := by simp [arg0, e0]
  have hsb := fun i (h : i < (x.bs ++ [0]).length) => bytesAt_le hsP R.lu i h
  have hstr : CStr m.memory (arg0 m) x.bs.length := by
    rw [a0]
    refine ⟨fun i h => ?_, fun j h => ?_, ?_⟩
    · obtain ⟨b1, b2, b3⟩ := hsb i (by simpa using h)
      exact ⟨b1, b3, by rw [b2]; rfl⟩
    · rw [(hsb j (by simp; omega)).2.1, List.getElem_append_left h]
      intro e
      exact hnz (by rw [← Option.some.inj e]; exact List.getElem_mem h)
    · rw [(hsb x.bs.length (by simp)).2.1]; simp
  refine ⟨⟨R.rip, R.loaded, _, hstr⟩, fun _ h => h.elim, ?_⟩
  intro fin ⟨hrax, hw⟩
  refine (spure_sep_apply _ _ _).mpr ⟨hrax _ hstr, ?_⟩
  refine bytesAt_reval hsP rfl fun i h => ⟨?_, ?_⟩
  · rw [hw.2 _ id]; exact (hsb i h).2.1
  · rw [permsAt_eq hw]; exact (hsb i h).2.2

end Silmaril.Proofs.X86.Stencils.ByteLoop
