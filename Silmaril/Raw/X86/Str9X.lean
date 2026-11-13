module

public import Silmaril.X86.Str9X.Defs
public import Silmaril.X86.Str9D.Thms

/-!
# `Str9X`: the conservative extension of `Str9D`, the x87 listing law, the machine

* `str9d_none`, `step_of_str9d`: where `Str9D` claims no bytes it has no step, so **every
  `Str9D` step is a step** with the x87 state kept.
* `step_of_fetch_fpu`, `step_of_listed_fpu`: the law of an x87 form.
* `isa`, `extendsStr9D`, `run_of_str9v`.
-/

@[expose] public section

namespace Silmaril.X86.Str9X

open Silmaril.X86 (State Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Str9D (DState)
open Silmaril.Process (Memory)

/-! ## Conservative extension -/

/-- Where no decoder of `Str9D` claims the bytes, `Str9D` has no step. -/
theorem str9d_none {d : DState} (h : lowerClaims d = false) : Str9D.step d = none := by
  simp only [lowerClaims, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hv : Str9V.step d.v = none := by
    simp only [Str9V.step, h2, h3, Bool.false_eq_true, ite_false]
  simp only [Str9D.step, h1, Bool.false_eq_true, ite_false, Str9D.stepLower, hv, h4]

/-- **Every `Str9D` step is a step**, with the x87 state kept. -/
theorem step_of_str9d {x : XState} {d' : DState} (h : Str9D.step x.d = some d') :
    step x = some ⟨d', x.fpu⟩ := by
  cases hc : lowerClaims x.d
  · rw [str9d_none hc] at h; cases h
  · simp [step, hc, h]

/-! ## The x87 listing law -/

theorem decodeL_spec {w : List Byte} {i : Silmaril.X86.Features.Fpu.Instr} {n : Nat}
    (h : decodeL w = some (i, n)) :
    Silmaril.X86.Features.Fpu.decode w = some (i, n) ∧ Str9D.lowerBad w = true ∧
      Str9D.decodeFlag w = none ∧ Str9D.strClaims w = false ∧ n ≤ maxInstrLength := by
  unfold decodeL at h
  split at h
  · rename_i j k hj
    split at h
    · rename_i c
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hj, c⟩
    · cases h
  · cases h

theorem decodeFlag_append_none {w : List Byte} (hne : w ≠ []) (h : Str9D.decodeFlag w = none)
    (more : List Byte) : Str9D.decodeFlag (w ++ more) = none := by
  match w, hne with
  | b :: t, _ =>
    cases hb : Str9D.decodeFlag (b :: t ++ more) with
    | none => rfl
    | some p =>
      exfalso
      unfold Str9D.decodeFlag at hb
      split at hb
      · rename_i tail heq
        simp only [List.cons_append, List.cons.injEq] at heq
        rw [heq.1] at h
        have : Str9D.decodeFlag (0xFD#8 :: t) = some (true, 1) := rfl
        rw [this] at h; cases h
      · rename_i tail heq
        simp only [List.cons_append, List.cons.injEq] at heq
        rw [heq.1] at h
        have : Str9D.decodeFlag (0xFC#8 :: t) = some (false, 1) := rfl
        rw [this] at h; cases h
      · cases hb

/-- **The fetch form of the x87 law.** -/
theorem step_of_fetch_fpu {x y : XState} {l : Nat} {w : List Byte}
    {i : Silmaril.X86.Features.Fpu.Instr}
    (fetched : x.memory.fetchBytes x.core.rip.toNat l = some w) (hdec : decodeL w = some (i, l))
    (hx : execFpu i l x = some y) : step x = some y := by
  obtain ⟨hd, hb, hfl, hsc, h15⟩ := decodeL_spec hdec
  obtain ⟨hc, hv⟩ := Str9D.str9v_rejects (v := x.d.v) fetched h15 hb
  obtain ⟨more, hmore⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow fetched h15
  have hw : Str9D.strClaims (fetchWindow x.memory maxInstrLength x.core.rip.toNat) = false := by
    rw [← hmore]; exact Str9D.strClaims_append more hsc
  have hff : Str9D.fetchFlag x.memory x.core.rip.toNat = none := by
    unfold Str9D.fetchFlag
    rw [← hmore, decodeFlag_append_none (Str9D.ne_nil_of_strClaims hsc) hfl more]
    rfl
  have hlc : lowerClaims x.d = false := by
    simp only [lowerClaims]
    simp only [XState.memory, XState.core] at hw hff
    simp [hw, hc, hv, hff]
  have hda : Silmaril.X86.Features.Fpu.decode (w ++ more) = some (i, l) :=
    Silmaril.X86.Features.Fpu.byteDecoder.decode_append more hd
  have hf : fetchFpu x.memory x.core.rip.toNat = some (some (i, l)) := by
    unfold fetchFpu
    rw [← hmore, hda]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hlc, Bool.false_eq_true, ite_false, hf, hx]

/-- **The x87 listing law.** -/
theorem step_of_listed_fpu {x y : XState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Silmaril.X86.Features.Fpu.Instr} (hl : Loaded x.memory base code)
    (hrip : x.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decodeL ((code.drop o).take l) = some (i, l)) (hx : execFpu i l x = some y) :
    step x = some y := by
  have h1 : 0 < l := Silmaril.X86.Features.Fpu.byteDecoder.decode_length_pos (decodeL_spec hdec).1
  exact step_of_fetch_fpu (Str9D.fetched_of_listed (d := x.d) hl hrip h1 hfit) hdec hx

end Silmaril.X86.Str9X
