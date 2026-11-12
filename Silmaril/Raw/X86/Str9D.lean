module

public import Silmaril.X86.Str9D.Defs
public import Silmaril.X86.Str9V.Thms

/-!
# `Str9D`: the lifts from `Str9V`, the laws of `std`/`cld` and of the string forms, the machine

* `step_of_str9v`, `run_of_str9v`: every `Str9V` step and run from a state with DF clear is
  one here, DF still clear.
* `step_of_fetch_flag` (`std`/`cld`), `step_of_fetch_str` (a string form with DF set,
  executed downwards) and their listing forms.
* `step_of_listed`: the law of `Str9FsX`'s integer instructions that are not string forms,
  at either DF value; `isa`.
-/

@[expose] public section

namespace Silmaril.X86.Str9D

open Silmaril.X86 (State Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Ext.ByteParser
open Silmaril.X86.Str9V (VState)
open Silmaril.Process (Memory)

/-! ## Lifting `Str9V` -/

/-- **Every `Str9V` step from DF clear is a step**, DF still clear. -/
theorem step_of_str9v {d : DState} {v' : VState} (hdf : d.df = false)
    (h : Str9V.step d.v = some v') : step d = some ⟨v', false⟩ := by
  unfold step stepLower
  simp [hdf, h]

/-- **Every `Str9V` run from DF clear is a run**, of the same length, ending with DF clear. -/
theorem run_of_str9v {n : Nat} {v v' : VState}
    (h : Silmaril.Machine.Execution.run Str9V.step n v = some v') :
    Silmaril.Machine.Execution.run step n ⟨v, false⟩ = some ⟨v', false⟩ := by
  obtain ⟨y, hy, rfl⟩ := Silmaril.Machine.Execution.run_simulates Str9V.step step
    (fun s y => y = ⟨s, false⟩)
    (fun s y s' hy hs => ⟨⟨s', false⟩, by subst hy; exact step_of_str9v rfl hs, rfl⟩)
    n rfl h
  exact hy

/-! ## The prefix scan -/

/-- `strClaims` is `false` only on bytes that already show a non-string opcode. -/
theorem strClaims_append : ∀ {w : List Byte} (more : List Byte), strClaims w = false →
    strClaims (w ++ more) = false
  | [], _, h => by simp [strClaims] at h
  | b :: t, more, h => by
    cases hb : isPrefix b
    · simp only [strClaims, List.cons_append, hb, Bool.false_eq_true, ite_false] at h ⊢; exact h
    · simp only [strClaims, List.cons_append, hb, ite_true] at h ⊢; exact strClaims_append more h

theorem ne_nil_of_strClaims {w : List Byte} (h : strClaims w = false) : w ≠ [] := by
  rintro rfl; simp [strClaims] at h

theorem decodeFlag_append {w : List Byte} {b : Bool} {n : Nat} (h : decodeFlag w = some (b, n))
    (more : List Byte) : decodeFlag (w ++ more) = some (b, n) := by
  unfold decodeFlag at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · cases h

theorem decodeStr_append {w : List Byte} {f : Str} {n : Nat} (h : decodeStr w = some (f, n))
    (more : List Byte) : decodeStr (w ++ more) = some (f, n) := by
  unfold decodeStr at h
  split at h <;>
    first | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl) | cases h

theorem strClaims_flag {w : List Byte} {b : Bool} {n : Nat} (h : decodeFlag w = some (b, n))
    (more : List Byte) : strClaims (w ++ more) = false := by
  unfold decodeFlag at h
  split at h
  · simp [strClaims, isPrefix, isStrOpcode]
  · simp [strClaims, isPrefix, isStrOpcode]
  · cases h

theorem strClaims_str {w : List Byte} {f : Str} {n : Nat} (h : decodeStr w = some (f, n))
    (more : List Byte) : strClaims (w ++ more) = true := by
  unfold decodeStr at h
  split at h <;> first | simp [strClaims, isPrefix, isStrOpcode] | cases h

/-! ## `Str9V` rejects -/

theorem vNew_none {w : List Byte} (h : vBad w = true) (more : List Byte) :
    Str9V.decodeNew (w ++ more) = none := by
  unfold vBad at h
  split at h
  · rename_i hb
    unfold Str9V.decodeNew
    rw [Str9V.good_pNew.bad hb more]
  · cases h

theorem stosd_none {w : List Byte} (h : stosdNo w = true) (more : List Byte) :
    Silmaril.X86.Str9FsX.decodeStosd (w ++ more) = none := by
  match w, h with
  | b :: t, h =>
    simp only [stosdNo, bne_iff_ne, ne_eq] at h
    simp only [List.cons_append]
    unfold Silmaril.X86.Str9FsX.decodeStosd
    split
    · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h
    · rfl

/-- **Where no layer reads the bytes, none of `Str9V`'s decoders claims them.** -/
theorem str9v_rejects {v : VState} {l : Nat} {w : List Byte}
    (fetched : v.g.x.m.memory.fetchBytes v.g.x.m.core.rip.toNat l = some w)
    (h15 : l ≤ maxInstrLength) (hb : lowerBad w = true) :
    Str9V.lowerClaims v.g = false ∧
      Str9V.fetchNew v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
  simp only [lowerBad, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hnone, hbad⟩, hne⟩, hbad9⟩, hstr⟩, ha⟩, hf⟩, hs⟩, hst⟩, hgb⟩, hvb⟩ := hb
  obtain ⟨more, hmore, hf8⟩ :=
    Silmaril.X86.Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn9 : Silmaril.X86.Ext9.fetchNew v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Ext9.fetchNew
    rw [hmore, Silmaril.X86.Str9.decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : Silmaril.X86.Str9.fetchStr v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9.fetchStr
    rw [hmore, Silmaril.X86.Str9Fs.decodeStr_none_of_strBad hstr more]
    rfl
  have hfn : Silmaril.X86.Str9Fs.fetchNew v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9Fs.fetchNew
    rw [hmore, Silmaril.X86.Str9FsX.str9fsNew_none ha hf more]
    rfl
  have hss : Silmaril.X86.Sse9.fetchSse v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Sse9.fetchSse
    rw [hmore, Silmaril.X86.Str9FsX.sse_none hs more]
    rfl
  have hsd : Silmaril.X86.Str9FsX.fetchStosd v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9FsX.fetchStosd
    rw [hmore, stosd_none hst more]
    rfl
  have hgn : Silmaril.X86.Str9G.fetchNew v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9G.fetchNew
    rw [hmore, Str9V.gNew_none hgb more]
    rfl
  have hc : Str9V.lowerClaims v.g = false := by
    unfold Str9V.lowerClaims; simp only; rw [hf8]; simp [hfn9, hfs, hfn, hss, hsd, hgn]
  have hv : Str9V.fetchNew v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Str9V.fetchNew
    rw [hmore, vNew_none hvb more]
    rfl
  exact ⟨hc, hv⟩

/-- **Where no layer reads the bytes, `Str9V` has no step.** -/
theorem str9v_none {v : VState} {l : Nat} {w : List Byte}
    (fetched : v.g.x.m.memory.fetchBytes v.g.x.m.core.rip.toNat l = some w)
    (h15 : l ≤ maxInstrLength) (hb : lowerBad w = true) : Str9V.step v = none := by
  obtain ⟨hc, hv⟩ := str9v_rejects fetched h15 hb
  simp only [Str9V.step, hc, hv, Bool.false_eq_true, ite_false]

/-! ## The laws of the layer's forms -/

/-- **`std` and `cld`**: on bytes no layer of `Str9V` reads, `FD` sets and `FC` clears DF. -/
theorem step_of_fetch_flag {d : DState} {w : List Byte} {b : Bool}
    (fetched : d.memory.fetchBytes d.core.rip.toNat 1 = some w)
    (hdec : decodeFlag w = some (b, 1)) (hb : lowerBad w = true) :
    step d = some ⟨Str9V.coreV d.v { d.core with rip := d.core.rip + BitVec.ofNat 64 1 } d.memory,
      b⟩ := by
  obtain ⟨more, hmore⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow (limit := maxInstrLength) fetched (by decide)
  have hw : strClaims (fetchWindow d.memory maxInstrLength d.core.rip.toNat) = false := by
    rw [← hmore]; exact strClaims_flag hdec more
  have hv : Str9V.step d.v = none := str9v_none fetched (by decide) hb
  have hff : fetchFlag d.memory d.core.rip.toNat = some (some (b, 1)) := by
    unfold fetchFlag
    rw [← hmore, decodeFlag_append hdec more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hw, Bool.and_false, Bool.false_eq_true, ite_false, stepLower, hv, hff]

/-- **A string form with DF set** runs downwards (`execStr true`). -/
theorem step_of_fetch_str {d : DState} {l : Nat} {w : List Byte} {f : Str} {c : State}
    {mem : Memory} (hdf : d.df = true)
    (fetched : d.memory.fetchBytes d.core.rip.toNat l = some w) (h15 : l ≤ maxInstrLength)
    (hdec : decodeStr w = some (f, l))
    (hx : execStr true f d.core d.memory (d.core.rip + BitVec.ofNat 64 l) = some (c, mem)) :
    step d = some (d.upd c mem) := by
  obtain ⟨more, hmore⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow fetched h15
  have hw : strClaims (fetchWindow d.memory maxInstrLength d.core.rip.toNat) = true := by
    rw [← hmore]; exact strClaims_str hdec more
  have hfs : fetchStr d.memory d.core.rip.toNat = some (some (f, l)) := by
    unfold fetchStr
    rw [← hmore, decodeStr_append hdec more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hdf, hw, Bool.and_self, ite_true, hfs, hx, Option.map_some]

/-- The fetch window at a listed offset. -/
theorem fetched_of_listed {d : DState} {base : Word} {code : List Byte} {o l : Nat}
    (hl : Loaded d.memory base code) (hrip : d.core.rip = base + BitVec.ofNat 64 o)
    (h1 : 0 < l) (hfit : o + l ≤ code.length) :
    d.memory.fetchBytes d.core.rip.toNat l = some ((code.drop o).take l) := by
  have hA : d.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  rw [hA]; exact hl.fetchBytes_sub h1 hfit

/-- **The law of the integer instructions that are not string forms**, at either DF value. -/
theorem step_of_listed {d : DState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Silmaril.X86.Str9FsX.Instr} {c : State} {mem : Memory} (hl : Loaded d.memory base code)
    (hrip : d.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Str9FsX.exec i d.core d.memory l = .ok c mem) :
    step d = some (d.upd c mem) := by
  unfold decode at hdec
  split at hdec
  · rename_i j n hj
    split at hdec
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hdec
      obtain ⟨rfl, rfl⟩ := hdec
      have hv := Str9V.isa.step_of (s := d.v) trivial hl hrip hfit hj hx trivial
      rw [Str9V.isa_step] at hv
      have hne := ne_nil_of_strClaims hc.1
      have h1 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hne)
      obtain ⟨more, hmore⟩ :=
        Silmaril.X86.fetchBytes_prefix_fetchWindow (fetched_of_listed hl hrip h1 hfit) hc.2
      have hw : strClaims (fetchWindow d.memory maxInstrLength d.core.rip.toNat) = false := by
        rw [← hmore]; exact strClaims_append more hc.1
      simp only [step, hw, Bool.and_false, Bool.false_eq_true, ite_false, stepLower, hv]
      rfl
    · cases hdec
  · cases hdec

end Silmaril.X86.Str9D
