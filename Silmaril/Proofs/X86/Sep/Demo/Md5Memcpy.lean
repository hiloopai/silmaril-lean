module

public import Silmaril.X86.Sep.Demo.Defs
public import Silmaril.X86.Sep.SysV.Thms
public import Silmaril.Proofs.X86.Sep.Algebra
public import Silmaril.Proofs.X86.Sep.Demo.Leaf
public import Silmaril.Proofs.X86.Sep.Call
/-!
# Proofs: `MD5_memcpy` as a System V spec

`md5_memcpy_SPEC` is derived from `Silmaril.X86.Decompile.Md5Memcpy.md5_memcpy_returns`
(an `Ext.Returns` certificate) with no new symbolic execution: every side condition of the
certificate's `Entry` — permissions, bounds, buffer separation, separation of buffers from
the frame and from the code — is read off the separation-logic precondition, and its
`WritesOnly₂` frame and byte-copy postcondition become the spec's postcondition.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SepDemo

open Silmaril.X86 (State MState Word Byte Reg Insn sysv64)
open Silmaril.Process (Memory addressLimit)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Demo
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)

/-- Two owned address intervals of disjoint fragments do not overlap. -/
theorem interval_apart {h₁ h₂ : Frag} (hd : Disjoint h₁ h₂) {a n b k : Nat} (hn : 0 < n)
    (hk : 0 < k) (h1 : ∀ i < n, (h₁ (.mem (a + i))).isSome)
    (h2 : ∀ j < k, (h₂ (.mem (b + j))).isSome) : a + n ≤ b ∨ b + k ≤ a := by
  by_contra hc
  rcases Nat.le_total a b with hab | hab
  · have x1 := h1 (b - a) (by omega)
    have x2 := h2 0 hk
    rw [show a + (b - a) = b by omega] at x1
    rw [Nat.add_zero] at x2
    exact Silmaril.Proofs.X86.Sep.Frag.Disjoint.not_both hd x1 x2
  · have x1 := h1 0 hn
    have x2 := h2 (a - b) (by omega)
    rw [show b + (a - b) = a by omega] at x2
    rw [Nat.add_zero] at x1
    exact Silmaril.Proofs.X86.Sep.Frag.Disjoint.not_both hd x1 x2

theorem isSome_union_left {a b : Frag} {l : Loc} (h : (a l).isSome) : (union a b l).isSome :=
  Silmaril.Proofs.X86.Sep.Frag.isSome_union.mpr (.inl h)

theorem isSome_union_right {a b : Frag} {l : Loc} (h : (b l).isSome) : (union a b l).isSome :=
  Silmaril.Proofs.X86.Sep.Frag.isSome_union.mpr (.inr h)

/-- The entry template owns the budget and the return slot. -/
theorem sysVEntry_owns {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    (hT : S.SysVEntry x entry sp ret h) (hst : S.stack ≤ sp.toNat) :
    ∀ i < S.stack + 8, (h (.mem (sp.toNat - S.stack + i))).isSome := by
  intro i hi
  have R := @Silmaril.Proofs.X86.Sep.sep_dom_right
  have L := @Silmaril.Proofs.X86.Sep.sep_dom_left
  refine R hT fun _ h1 => R h1 fun _ h2 => R h2 fun _ h3 => R h3 fun _ h4 => ?_
  by_cases hlt : i < S.stack
  · exact R h4 fun _ h5 => blockAny_dom h5 i hlt
  · refine L h4 fun _ h5 => ?_
    have := bytesAt_dom h5 (i - S.stack) (by simp; omega)
    rwa [show sp.toNat + (i - S.stack) = sp.toNat - S.stack + i by omega] at this

/-- The entry template's budget, as a held block. -/
theorem sysVEntry_block {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag} {m : MState}
    (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) :
    ∃ b, blockAny (sp.toNat - S.stack) S.stack b ∧ Le b (toFrag m) := by
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le hT hl
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le hb hlb
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le hb hlb
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le hb hlb
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le hb hlb
  exact ⟨b, hb, hlb⟩

theorem take_one_drop {α : Type} : ∀ (l : List α) (i : Nat) (h : i < l.length),
    (l.drop i).take 1 = [l[i]]
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => by simp
  | _ :: l, i + 1, h => by simpa using take_one_drop l i (by simpa using h)

theorem toNat_add_of_lt {a : Word} {j : Nat} (h : a.toNat + j < 2 ^ 64) :
    (a + BitVec.ofNat 64 j).toNat = a.toNat + j := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
  exact Nat.mod_eq_of_lt h

theorem loadN_one_of_readBytes {mem : Memory} {a : Word} {b : Byte}
    (h : mem.readBytes a.toNat 1 = some [b]) :
    Silmaril.X86.Ext.loadN mem a 1 = some (BitVec.ofNat 64 b.toNat) := by
  simp [Silmaril.X86.Ext.loadN, h, Silmaril.X86.Ext.leValue]

theorem get_of_loadN_one {mem : Memory} {a : Word} {b : Byte}
    (h : Silmaril.X86.Ext.loadN mem a 1 = some (BitVec.ofNat 64 b.toNat)) :
    mem.bytes.get? a.toNat = some b := by
  unfold Silmaril.X86.Ext.loadN at h
  cases hr : mem.readBytes a.toNat 1 with
  | none => rw [hr] at h; cases h
  | some bs =>
    rw [hr] at h
    have hlen := Memory.readWith_length hr
    match bs, hlen with
    | [c], _ =>
      have hc : BitVec.ofNat 64 c.toNat = BitVec.ofNat 64 b.toNat := by
        simpa [Silmaril.X86.Ext.leValue] using h
      have e : c = b := by
        apply BitVec.eq_of_toNat_eq
        have := congrArg BitVec.toNat hc
        simp only [BitVec.toNat_ofNat] at this
        have h1 := c.isLt; have h2 := b.isLt
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        exact this
      subst e
      simpa using Memory.readWith_get hr 0 (by simp)

/-- **`MD5_memcpy` meets `md5Spec`.** -/
theorem md5_memcpy_SPEC (entry : Word) :
    md5Spec.Sat Silmaril.X86.Open.isa (codePt entry.toNat Silmaril.X86.Decompile.Md5Memcpy.code) entry := by
  apply FnSpec.satWith_of_runs
  intro x sp ret m hc ht hu _ _ hst hcP htP huP hd1 hd2 hl
  simp only [md5Spec] at hst
  have hlc := le_left hl
  have hlt := le_left (le_right hd1 hl)
  have hlu := le_right hd2 (le_right hd1 hl)
  -- the user part
  obtain ⟨he, hbuf, ⟨rfl, hlen, hpos, hsmall⟩, hbufP, -, hlbuf, -, rfl⟩ := sep_le huP hlu
  obtain ⟨ho, hi, hoP, hiP, hlo, hli, hdoi, rfl⟩ := sep_le hbufP hlbuf
  rw [Silmaril.Proofs.X86.Sep.Frag.empty_union] at hd1 hd2 hl hlu huP
  set len := x.src.length with hlen_def
  -- readings of the template
  have erip := FnSpec.sysVEntry_rip htP hlt
  have ersp := FnSpec.sysVEntry_rsp htP hlt
  have eret := FnSpec.sysVEntry_ret htP hlt
  have eout := FnSpec.sysVEntry_args htP hlt 0 (by decide) (by simp [md5Spec])
  have einp := FnSpec.sysVEntry_args htP hlt 1 (by decide) (by simp [md5Spec])
  have erdx := FnSpec.sysVEntry_args htP hlt 2 (by decide) (by simp [md5Spec])
  simp only [argRegs, md5Spec, List.getElem_cons_zero, List.getElem_cons_succ] at eout einp erdx
  obtain ⟨hb, hbP, hlb⟩ := sysVEntry_block htP hlt
  simp only [md5Spec] at hbP
  have howns := sysVEntry_owns htP (by simp only [md5Spec]; omega)
  simp only [md5Spec] at howns
  -- bytes of the buffers
  have hob := fun i (hi' : i < x.old.length) => bytesAt_le hoP hlo i hi'
  have hib := fun i (hi' : i < x.src.length) => bytesAt_le hiP hli i hi'
  have hinRead := readBytes_of_bytesPtRO (List.ne_nil_of_length_pos hpos) hiP hli
  have houtRead := readBytes_of_bytesPt (by
    intro e; rw [e] at hlen; simp at hlen; omega) hoP hlo
  rw [hlen] at houtRead
  have outBound : x.out.toNat + len ≤ 2 ^ 64 := by
    have := (hob (len - 1) (by omega)).1
    simp [addressLimit] at this; omega
  have inBound : x.inp.toNat + len ≤ 2 ^ 64 := by
    have := (hib (len - 1) (by omega)).1
    simp [addressLimit] at this; omega
  -- ownership
  have ownOut : ∀ i < len, (ho (.mem (x.out.toNat + i))).isSome :=
    fun i hi' => bytesAt_dom hoP i (by omega)
  have ownIn : ∀ i < len, (hi (.mem (x.inp.toNat + i))).isSome :=
    fun i hi' => bytesAt_dom hiP i hi'
  have ownCode : ∀ i < 70, (hc (.mem (entry.toNat + i))).isSome :=
    fun i hi' => bytesAt_dom hcP i (by simpa [Silmaril.X86.Decompile.Md5Memcpy.code] using hi')
  have dTU : Disjoint ht (union ho hi) := hd2
  have dTO : Disjoint ht ho := fun l => by
    rcases dTU l with e | e
    · exact .inl e
    · exact .inr (Silmaril.Proofs.X86.Sep.Frag.union_eq_none.mp e).1
  have dTI : Disjoint ht hi := fun l => by
    rcases dTU l with e | e
    · exact .inl e
    · exact .inr (Silmaril.Proofs.X86.Sep.Frag.union_eq_none.mp e).2
  have dCU : Disjoint hc (union ht (union ho hi)) := hd1
  have dC : ∀ l, (hc l).isSome → union ht (union ho hi) l = none :=
    fun l hl' => Silmaril.Proofs.X86.Sep.none_of_disjoint dCU hl'
  have dCO : Disjoint hc ho := fun l => by
    by_cases hs : (hc l).isSome
    · right
      have := Silmaril.Proofs.X86.Sep.Frag.union_eq_none.mp (dC l hs)
      exact (Silmaril.Proofs.X86.Sep.Frag.union_eq_none.mp this.2).1
    · left; simpa using hs
  have dCT : Disjoint hc ht := fun l => by
    by_cases hs : (hc l).isSome
    · right; exact (Silmaril.Proofs.X86.Sep.Frag.union_eq_none.mp (dC l hs)).1
    · left; simpa using hs
  have frameOwn : ∀ i < 40, (ht (.mem (sp.toNat - 32 + i))).isSome := howns
  have apartOI := interval_apart hdoi hpos hpos ownOut ownIn
  have apartOF := interval_apart (Silmaril.Proofs.X86.Sep.Frag.Disjoint.symm dTO) hpos
    (by omega : 0 < 40) ownOut frameOwn
  have apartIF := interval_apart (Silmaril.Proofs.X86.Sep.Frag.Disjoint.symm dTI) hpos
    (by omega : 0 < 40) ownIn frameOwn
  -- the certificate's entry condition
  have hrsp32 : 32 ≤ sp.toNat := hst
  have hlenOf : Silmaril.X86.Decompile.Md5Memcpy.lenOf m = len := by
    unfold Silmaril.X86.Decompile.Md5Memcpy.lenOf Silmaril.X86.Ext.Sz.read
    rw [erdx]
    simp
    omega
  have entryOk : Silmaril.X86.Decompile.Md5Memcpy.Entry entry ret m := by
    have hout : Silmaril.X86.Decompile.Md5Memcpy.outOf m = x.out := eout
    have hinp : Silmaril.X86.Decompile.Md5Memcpy.inOf m = x.inp := einp
    refine ⟨erip, fetchBytes_of_codePt (by decide) hcP hlc, by rw [ersp]; exact eret,
      ?_, ?_, by rw [ersp]; exact hrsp32, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ersp]; exact permitted_of_blockAny (.inr rfl) (by omega) hbP hlb
    · rw [ersp]; exact permitted_of_blockAny (.inl rfl) (by omega) hbP hlb
    · rw [hout, hlenOf]
      apply Silmaril.Proofs.X86.Sep.permitted_of (by omega)
      intro i hi'
      obtain ⟨b1, -, b3⟩ := hob i (by omega)
      exact ⟨b1, by simpa [permsAt] using b3.2⟩
    · rw [hout, hlenOf]
      exact Memory.readWith_permitted houtRead
    · rw [hinp, hlenOf]; exact Memory.readWith_permitted hinRead
    · intro j hj
      rw [hlenOf] at hj
      rw [hinp, Silmaril.X86.Ext.loadN, toNat_add_of_lt (by omega)]
      have := Memory.readBytes_sub_range hinRead (offset := j) (len := 1) hj (by omega)
      rw [this]; rfl
    · rw [hout, hlenOf]; exact outBound
    · rw [hinp, hlenOf]; exact inBound
    · show _ ∨ _
      rw [hout, hinp, hlenOf]
      exact apartOI
    · rw [hout, hlenOf, ersp]
      omega
    · rw [hinp, hlenOf, ersp]
      omega
    · rw [hout, hlenOf]
      exact interval_apart dCO (by omega) hpos ownCode ownOut
    · rw [ersp]
      have := interval_apart dCT (by omega : 0 < 70) (by omega : 0 < 40) ownCode frameOwn
      omega
  obtain ⟨final, hret, hrip, hcopy, hrsp, hcs, hw2⟩ :=
    Silmaril.X86.Decompile.Md5Memcpy.md5_memcpy_returns entryOk
  rw [hlenOf] at hcopy hw2
  have hout : Silmaril.X86.Decompile.Md5Memcpy.outOf m = x.out := eout
  have hinp : Silmaril.X86.Decompile.Md5Memcpy.inOf m = x.inp := einp
  rw [hout, hinp] at hcopy
  rw [hout, ersp] at hw2
  have hperms : ∀ a, permsAt final.memory a = permsAt m.memory a := by
    intro a; simp [permsAt, Memory.permits, hw2.1]
  refine ⟨final, (Silmaril.X86.Open.returns_open_ext hret).1, hrip,
    by rw [hrsp, ersp], hcs, ⟨hw2.1, fun a ha => hw2.2 a ?_ ?_⟩, ?_⟩
  · by_contra hc'
    exact ha (isSome_union_right (isSome_union_right (isSome_union_left (by
      have := ownOut (a - x.out.toNat) (by omega)
      rwa [show x.out.toNat + (a - x.out.toNat) = a by omega] at this))))
  · by_contra hc'
    exact ha (isSome_union_left (by
      have := frameOwn (a - (sp.toNat - 32)) (by omega)
      rwa [show sp.toNat - 32 + (a - (sp.toNat - 32)) = a by omega] at this))
  -- the postcondition on the user part
  show (bytesPt x.out.toNat x.src ∗ bytesPtRO x.inp.toNat x.src)
    (reval (union Frag.empty (union ho hi)) (toFrag final))
  rw [Silmaril.Proofs.X86.Sep.Frag.empty_union,
    Silmaril.Proofs.X86.Sep.Frag.reval_union]
  have srcByte : ∀ i (hi' : i < len), m.memory.readBytes (x.inp + BitVec.ofNat 64 i).toNat 1 =
      some [x.src[i]] := by
    intro i hi'
    rw [toNat_add_of_lt (by omega),
      Memory.readBytes_sub_range hinRead (offset := i) (len := 1) hi' (by omega),
      take_one_drop _ _ hi']
  refine ⟨_, _, Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hdoi _, rfl, ?_, ?_⟩
  · refine bytesAt_reval hoP hlen.symm fun i hi' => ⟨?_, ?_⟩
    · have hc := (hcopy i hi').trans (loadN_one_of_readBytes (srcByte i hi'))
      have := get_of_loadN_one hc
      rwa [toNat_add_of_lt (by omega)] at this
    · rw [hperms]; exact (hob i (by omega)).2.2
  · refine bytesAt_reval hiP rfl fun i hi' => ⟨?_, ?_⟩
    · rw [hw2.2 _ (by omega) (by omega)]
      exact (hib i hi').2.1
    · rw [hperms]; exact (hib i hi').2.2

end Silmaril.Proofs.X86.SepDemo
