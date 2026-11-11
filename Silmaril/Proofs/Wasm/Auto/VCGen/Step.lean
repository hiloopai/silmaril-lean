module

public import Silmaril.Proofs.Wasm.Auto.VCGen.Basic
public import Silmaril.Proofs.Wasm.Auto.VCGen.Convert
public import Silmaril.Wasm.Examples.Common.Thms

/-!
# The reflective VC generator: straight-line instructions

`step1_wp`: if `step1 i σ = some (σ', side)` and the side conditions hold in `ρ`, the
instruction `i` run from the store, frame and stack that `σ` denotes in `ρ` continues, in every
run, with the frame and stack that `σ'` denotes (the store is unchanged). By
`Silmaril.Wasm.Examples.Common.Wp.exec1` (`Silmaril.Wasm.Logic.Core.exec1` is the instruction's only
continuation) and, for conversions, `HWP.wrap`/`HWP.extend`. `step1_pc`: the path condition and
the types of the locals do not change.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.VCGen

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.VCGen
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Post exec1 popInt popV localVal?)
open Silmaril.Wasm.Logic.Hoare (HWP)

variable {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns}

theorem popInt_of (ρ ξ : Env) (t : IntType) (a : Tm t) (rs : List Val) :
    popInt t ((SV.of t a).den F ρ ξ :: rs) = some (a.den F ρ ξ, rs) := by
  cases t <;> rfl

theorem popInt_num (t : IntType) (x : BitVec t.width) (rs : List Val) :
    popInt t (.num ⟨.int t, x⟩ :: rs) = some (x, rs) := by
  cases t <;> rfl

theorem step1_pc {i : Instr} {σ σ' : SSt} {side : List Fm} (h : step1 i σ = some (σ', side)) :
    σ'.pc = σ.pc ∧ σ'.locals.map SV.ty = σ.locals.map SV.ty := by
  unfold step1 at h
  split at h <;> (try split at h) <;> (try split at h) <;>
    simp only [Option.some.injEq, Prod.mk.injEq, Option.map_eq_some_iff, reduceCtorEq,
      Prod.exists] at h
  all_goals first
    | (obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, _, _, ⟨rfl, -⟩⟩ := h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, _, rfl, -⟩ := h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨rfl, -⟩ := h
       refine ⟨rfl, ?_⟩
       apply List.ext_getElem?
       intro n
       simp only [List.getElem?_map, List.getElem?_set]
       split_ifs <;> simp_all)

/-- An instruction evaluated by `exec1`, in the symbolic reading. -/
theorem of_exec1 {i : Instr} {ρ : Env} {s : Store H} {f f' : Frame} {σ σ' : SSt}
    {rest : List Admin} {Q : Post H}
    (he : exec1 s f (dens F ρ σ.stack) i = some (s, f', dens F ρ σ'.stack))
    (hf' : f' = ⟨locs F ρ σ'.locals, f.module⟩)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain i :: rest) Q := by
  subst hf'
  exact Silmaril.Wasm.Examples.Common.Wp.exec1 (m := .part) he hk

theorem den_lit_toNat (ρ ξ : Env) (t : IntType) (c : BitVec t.width) :
    (Tm.lit t c.toNat).den F ρ ξ = c := litT_toNat t c

section Instr

variable {σ σ' : SSt} {side : List Fm} {ρ : Env} {s : Store H} {f : Frame} {rest : List Admin}
  {Q : Post H}

/-- The frame a symbolic state denotes, from its locals. -/
theorem frame_eq (hf : f.locals = locs F ρ σ.locals) : f = ⟨locs F ρ σ.locals, f.module⟩ := by
  rw [← hf]

theorem wp_nop (h : step1 .nop σ = some (σ', side)) (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain .nop :: rest) Q := by
  obtain ⟨rfl, rfl⟩ : σ = σ' ∧ [] = side := by simpa [step1] using h
  exact of_exec1 rfl (frame_eq hf) hk

theorem wp_drop (h : step1 .drop σ = some (σ', side)) (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain .drop :: rest) Q := by
  obtain ⟨v, st, hst, rfl, rfl⟩ : ∃ v st, σ.stack = v :: st ∧
      { σ with stack := st } = σ' ∧ [] = side := by
    simp only [step1] at h
    split at h <;> simp_all
  exact of_exec1 (σ' := { σ with stack := st }) (f' := f) (by simp [hst, exec1, popV])
    (frame_eq hf) hk

theorem wp_intConst {t : IntType} {c : BitVec t.width}
    (h : step1 (.intConst t c) σ = some (σ', side)) (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.intConst t c) :: rest) Q := by
  obtain ⟨rfl, rfl⟩ : { σ with stack := SV.of t (.lit t c.toNat) :: σ.stack } = σ' ∧
      [] = side := by simpa [step1] using h
  refine of_exec1 ?_ (by exact frame_eq hf) hk
  simp [exec1, SV.den_of, den_lit_toNat]

theorem wp_localGet {x : LocalIdx} (h : step1 (.localGet x) σ = some (σ', side))
    (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.localGet x) :: rest) Q := by
  obtain ⟨v, hv, rfl, rfl⟩ : ∃ v, σ.locals[x.toNat]? = some v ∧
      { σ with stack := v :: σ.stack } = σ' ∧ [] = side := by simpa [step1] using h
  refine of_exec1 ?_ (by exact frame_eq hf) hk
  simp [exec1, localVal?, Frame.local?, hf, hv]

theorem localSet_inv {x : LocalIdx} (h : step1 (.localSet x) σ = some (σ', side)) :
    ∃ v st, σ.stack = v :: st ∧ x.toNat < σ.locals.length ∧ [] = side ∧
      { σ with stack := st, locals := σ.locals.set x.toNat v } = σ' := by
  simp only [step1] at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, Prod.mk.injEq,
    reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, ‹_›, (List.getElem?_eq_some_iff.mp ‹_›).1, rfl, rfl⟩

theorem localTee_inv {x : LocalIdx} (h : step1 (.localTee x) σ = some (σ', side)) :
    ∃ v st, σ.stack = v :: st ∧ x.toNat < σ.locals.length ∧ [] = side ∧
      { σ with locals := σ.locals.set x.toNat v } = σ' := by
  simp only [step1] at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, Prod.mk.injEq,
    reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, ‹_›, (List.getElem?_eq_some_iff.mp ‹_›).1, rfl, rfl⟩

theorem wp_localSet {x : LocalIdx} (h : step1 (.localSet x) σ = some (σ', side))
    (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.localSet x) :: rest) Q := by
  obtain ⟨v, st, hst, hx, rfl, rfl⟩ := localSet_inv h
  refine of_exec1 ?_ rfl hk
  simp [exec1, popV, hst, hx, Frame.setLocal, hf, List.map_set]

theorem wp_localTee {x : LocalIdx} (h : step1 (.localTee x) σ = some (σ', side))
    (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.localTee x) :: rest) Q := by
  obtain ⟨v, st, hst, hx, rfl, rfl⟩ := localTee_inv h
  refine of_exec1 ?_ rfl hk
  simp [exec1, popV, hst, hx, Frame.setLocal, hf, List.map_set]

theorem wp_intUnOp {t : IntType} {op : IntUnOp} (h : step1 (.intUnOp t op) σ = some (σ', side))
    (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.intUnOp t op) :: rest) Q := by
  obtain ⟨a, st, hp, rfl, rfl⟩ : ∃ a st, pop1 t σ.stack = some (a, st) ∧
      { σ with stack := SV.of t (.un op a) :: st } = σ' ∧ [] = side := by simpa [step1] using h
  refine of_exec1 ?_ (by exact frame_eq hf) hk
  simp [exec1, pop1_eq hp, popInt_num, SV.den_of, Tm.den, intUnOp_eq_unT]

theorem wp_intBinOp {t : IntType} {op : IntBinOp} (h : step1 (.intBinOp t op) σ = some (σ', side))
    (hs : ∀ φ ∈ side, φ.den F ρ ρ) (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.intBinOp t op) :: rest) Q := by
  obtain ⟨b, st, a, st', hp, hp', rfl, rfl⟩ : ∃ b st a st', pop1 t σ.stack = some (b, st) ∧
      pop1 t st = some (a, st') ∧ { σ with stack := SV.of t (.bin op a b) :: st' } = σ' ∧
      safeF t op a b = side := by
    simp only [step1] at h
    rcases hp : pop1 t σ.stack with _ | ⟨b, st⟩ <;> simp only [hp, reduceCtorEq] at h
    rcases hp' : pop1 t st with _ | ⟨a, st'⟩ <;>
      simp only [hp', Option.map_none, Option.map_some, Option.some.injEq, Prod.mk.injEq,
        reduceCtorEq] at h
    exact ⟨b, st, a, st', rfl, hp', h⟩
  refine of_exec1 ?_ (by exact frame_eq hf) hk
  simp [exec1, pop1_eq hp, pop1_eq hp', popInt_num, SV.den_of, Tm.den, intBinOp_of_safe hs]

theorem wp_intTestOp {t : IntType} {op : IntTestOp}
    (h : step1 (.intTestOp t op) σ = some (σ', side)) (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.intTestOp t op) :: rest) Q := by
  obtain ⟨a, st, hp, rfl, rfl⟩ : ∃ a st, pop1 t σ.stack = some (a, st) ∧
      { σ with stack := .i32 (.eqz a) :: st } = σ' ∧ [] = side := by simpa [step1] using h
  refine of_exec1 ?_ (by exact frame_eq hf) hk
  have hst : dens F ρ σ.stack = .num ⟨.int t, a.den F ρ ρ⟩ :: dens F ρ st := by
    rw [pop1_eq hp, dens, List.map_cons, SV.den_of]
  simp [exec1, hst, popInt_num, SV.den, Tm.den, Val.i32, intTestOp_eq_eqzV]

theorem wp_intRelOp {t : IntType} {op : IntRelOp} (h : step1 (.intRelOp t op) σ = some (σ', side))
    (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.intRelOp t op) :: rest) Q := by
  obtain ⟨b, st, a, st', hp, hp', rfl, rfl⟩ : ∃ b st a st', pop1 t σ.stack = some (b, st) ∧
      pop1 t st = some (a, st') ∧ { σ with stack := .i32 (.rel op a b) :: st' } = σ' ∧
      [] = side := by
    simp only [step1] at h
    rcases hp : pop1 t σ.stack with _ | ⟨b, st⟩ <;> simp only [hp, reduceCtorEq] at h
    rcases hp' : pop1 t st with _ | ⟨a, st'⟩ <;>
      simp only [hp', Option.map_none, Option.map_some, Option.some.injEq, Prod.mk.injEq,
        reduceCtorEq] at h
    exact ⟨b, st, a, st', rfl, hp', h⟩
  refine of_exec1 ?_ (by exact frame_eq hf) hk
  have hst : dens F ρ σ.stack = .num ⟨.int t, b.den F ρ ρ⟩ :: .num ⟨.int t, a.den F ρ ρ⟩ ::
      dens F ρ st' := by
    rw [pop1_eq hp, pop1_eq hp', dens, List.map_cons, List.map_cons, SV.den_of, SV.den_of]
  simp [exec1, hst, popInt_num, SV.den, Tm.den, Val.i32, intRelOp_eq_relV]

theorem wp_wrap (h : step1 (.convert .wrap) σ = some (σ', side))
    (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.convert .wrap) :: rest) Q := by
  obtain ⟨a, st, hp, rfl, rfl⟩ : ∃ a st, pop1 .i64 σ.stack = some (a, st) ∧
      { σ with stack := .i32 (.wrap a) :: st } = σ' ∧ [] = side := by simpa [step1] using h
  rw [frame_eq hf, pop1_eq hp]
  simp only [dens, List.map_cons, List.reverse_cons, SV.of, SV.den, Tm.den, wrapW] at hk ⊢
  exact HWP.wrap hk

theorem wp_extend {sx : Signedness} (h : step1 (.convert (.extend sx)) σ = some (σ', side))
    (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.convert (.extend sx)) :: rest) Q := by
  obtain ⟨a, st, hp, rfl, rfl⟩ : ∃ a st, pop1 .i32 σ.stack = some (a, st) ∧
      { σ with stack := .i64 (.ext sx a) :: st } = σ' ∧ [] = side := by simpa [step1] using h
  rw [frame_eq hf, pop1_eq hp]
  cases sx <;> simp only [dens, List.map_cons, List.reverse_cons, SV.of, SV.den, Tm.den, extSW,
    extUW] at hk ⊢ <;>
    exact HWP.extend hk

theorem wp_convert {op : ConvertOp} (h : step1 (.convert op) σ = some (σ', side))
    (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.convert op) :: rest) Q := by
  cases op
  case wrap => exact wp_wrap h hf hk
  case extend => exact wp_extend h hf hk
  all_goals exact absurd h (by simp [step1])

end Instr

/-- **A straight-line instruction**, every run. -/
theorem step1_wp {i : Instr} {σ σ' : SSt} {side : List Fm} {ρ : Env} {s : Store H} {f : Frame}
    {rest : List Admin} {Q : Post H}
    (h : step1 i σ = some (σ', side)) (hs : ∀ φ ∈ side, φ.den F ρ ρ)
    (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain i :: rest) Q := by
  cases i
  case nop => exact wp_nop h hf hk
  case drop => exact wp_drop h hf hk
  case intConst => exact wp_intConst h hf hk
  case localGet => exact wp_localGet h hf hk
  case localSet => exact wp_localSet h hf hk
  case localTee => exact wp_localTee h hf hk
  case intUnOp => exact wp_intUnOp h hf hk
  case intBinOp => exact wp_intBinOp h hs hf hk
  case intTestOp => exact wp_intTestOp h hf hk
  case intRelOp => exact wp_intRelOp h hf hk
  case convert => exact wp_convert h hf hk
  all_goals exact absurd h (by simp [step1])

end Silmaril.Proofs.Wasm.Auto.VCGen