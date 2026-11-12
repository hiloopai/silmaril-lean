module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Bodies
public import Silmaril.Wasm.Examples.Common.Thms

@[expose] public section

/-!
# The Farkas checker: the export specifications

`Rep rs s`: the store holds a machine state with the invariant for the weighted rows `rs`.
`farkas_spec`: every export call of `farkasI` meets `Common.callSpec farkasI Rep next Good`,
at every profile and for every host relation. The bodies' specifications
(`row_hwp`, `entry_hwp`, `check_hwp`) give the final store; the invariant lemmas
(`inv_row`, `inv_entry`, `inv_check`, `cert_of_check`) give the abstract transition and
safety.
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Logic.Hoare (HWP FSpec FSpecValid)
open Silmaril.Wasm.Examples.Common (callSpec bodyPost outcomeResult? FSpecValid.of_body_hwp)
open Silmaril.Logic.LinArith (WRows Cmd)

/-- **The representation relation**: the store holds a machine state with the invariant. -/
def Rep (rs : WRows) (s : Store Nat) : Prop := ∃ m, Holds s m ∧ Inv m rs

theorem Mach.globals_inj {m m' : Mach} (h : m.globals = m'.globals) :
    m.bad = m'.bad ∧ m.hr = m'.hr ∧ m.y = m'.y ∧ m.vb = m'.vb := by
  simp only [Mach.globals, List.cons.injEq, GlobalInst.mk.injEq, true_and, and_true] at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  exact ⟨Val.num.inj h₁ |> fun h => by injection h, Val.num.inj h₂ |> fun h => by injection h,
    Val.num.inj h₃ |> fun h => by injection h, Val.num.inj h₄ |> fun h => by injection h⟩

/-- The machine state a store holds is unique. -/
theorem Holds.unique {s : Store Nat} {m m' : Mach} (h : Holds s m) (h' : Holds s m') : m = m' := by
  obtain ⟨s₁, -, rfl⟩ := h
  obtain ⟨s₂, -, he⟩ := h'
  have hg : m.globals = m'.globals := congrArg Store.globals he
  have hm : [(⟨memTy, m.mem⟩ : MemInst)] = [⟨memTy, m'.mem⟩] := congrArg Store.mems he
  obtain ⟨h₁, h₂, h₃, h₄⟩ := Mach.globals_inj hg
  have h₅ : m.mem = m'.mem := by simpa using hm
  cases m
  cases m'
  simp only at h₁ h₂ h₃ h₄ h₅
  subst h₁ h₂ h₃ h₄ h₅
  rfl

/-! ## Arguments -/

theorem typed_row {vs : List Val}
    (h : List.Forall₂ ScalarType.HasVal [.num (.int .i64), .num (.int .i64)] vs) :
    ∃ y b, vs = [Val.i64 y, Val.i64 b] := by
  rcases h with _ | ⟨⟨y, rfl⟩, _ | ⟨⟨b, rfl⟩, h⟩⟩
  cases h
  exact ⟨y, b, rfl⟩

theorem typed_entry {vs : List Val}
    (h : List.Forall₂ ScalarType.HasVal [.num (.int .i32), .num (.int .i64)] vs) :
    ∃ j a, vs = [Val.i32 j, Val.i64 a] := by
  rcases h with _ | ⟨⟨j, rfl⟩, _ | ⟨⟨a, rfl⟩, h⟩⟩
  cases h
  exact ⟨j, a, rfl⟩

theorem typed_nil {vs : List Val} (h : List.Forall₂ ScalarType.HasVal [] vs) : vs = [] := by
  cases h
  rfl

/-- The precondition of a call specification: the store holds the instance's functions. -/
theorem pre_funcs {f : farkasI.F.Op} {s : Store Nat} {args : List Val}
    (h : (callSpec farkasI Rep next Good f).pre s args) : s.funcs = farkasStore.funcs := by
  obtain ⟨-, _, m, hH, -⟩ := h
  exact hH.funcs

/-- The arguments of a call specification are typed. -/
theorem pre_len {f : farkasI.F.Op} {s : Store Nat} {args : List Val}
    (h : (callSpec farkasI Rep next Good f).pre s args) :
    args.length = (Ty.ofList ((farkasExports.get f.1).params.map ScalarType.toC)).length := by
  rw [h.1, Ty.length_ofList, List.length_map]
  exact f.2.2.length_eq.symm

/-- The abstract state of a store from the precondition is the given one. -/
theorem rep_unique {s₀ : Store Nat} {m : Mach} (hs₀ : s₀.funcs = farkasStore.funcs) {rs : WRows}
    (h : Rep rs (withMach s₀ m)) : Inv m rs := by
  obtain ⟨m', hH, hI⟩ := h
  have he : m' = m := Holds.unique hH (holds_withMach hs₀ m)
  exact he ▸ hI

variable {P : Profile} {host : HostSemantics Nat}

/-- **`row` meets its call specification.** -/
theorem spec_row (args : Typed (farkasExports.get ⟨0, by decide⟩).params) :
    FSpecValid P host (farkasI.addr ⟨0, by decide⟩) (callSpec farkasI Rep next Good ⟨⟨0, by decide⟩, args⟩) := by
  obtain ⟨fi₀, fi₁, fi₂, hfs, hm₀, -, -, hc₀, -, -, ht₀, -, -⟩ := farkasStore_funcs
  obtain ⟨y, b, hargs⟩ := typed_row args.2
  refine FSpecValid.of_body_hwp (fi := fi₀) (code := ⟨⟨0⟩, [.i64], rowBody⟩)
    (fun s _ h => by rw [pre_funcs h, hfs]; rfl) hc₀ (FnType.expand_of_ofDefType? ht₀)
    (fun _ _ h => pre_len h) (fun s args' hpre => ?_)
  obtain ⟨rfl, rs, m, ⟨s₀, hs₀, rfl⟩, hI⟩ := hpre
  rw [hm₀, hargs]
  refine row_hwp y b fun f' => ⟨rfl, fun a' ha' r _ w _ => ⟨fun h => absurd (h : (0 : Nat) = 2) (by decide : ¬ (0 : Nat) = 2), ?_⟩⟩
  have hn : next a' (I := farkasI) ⟨⟨⟨0, by decide⟩, args⟩, w⟩ = (Cmd.row y.toInt b.toInt).apply a' := by
    simp only [next, hargs, cmdOf, Val.i64]
    rfl
  rw [hn]
  exact ⟨rowM m y b, holds_withMach hs₀ _, inv_row (rep_unique hs₀ ha') y b⟩

/-- **`entry` meets its call specification.** -/
theorem spec_entry (args : Typed (farkasExports.get ⟨1, by decide⟩).params) :
    FSpecValid P host (farkasI.addr ⟨1, by decide⟩)
      (callSpec farkasI Rep next Good ⟨⟨1, by decide⟩, args⟩) := by
  obtain ⟨fi₀, fi₁, fi₂, hfs, -, hm₁, -, -, hc₁, -, -, ht₁, -⟩ := farkasStore_funcs
  obtain ⟨j, a, hargs⟩ := typed_entry args.2
  refine FSpecValid.of_body_hwp (fi := fi₁) (code := ⟨⟨1⟩, [.i32, .i64], entryBody⟩)
    (fun s _ h => by rw [pre_funcs h, hfs]; rfl) hc₁ (FnType.expand_of_ofDefType? ht₁)
    (fun _ _ h => pre_len h) (fun s args' hpre => ?_)
  obtain ⟨rfl, rs, m, ⟨s₀, hs₀, rfl⟩, hI⟩ := hpre
  rw [hm₁, hargs]
  refine entry_hwp hI.1 j a fun f' =>
    ⟨rfl, fun a' ha' r _ w _ => ⟨fun h => absurd (h : (1 : Nat) = 2) (by decide : ¬ (1 : Nat) = 2), ?_⟩⟩
  have hn : next a' (I := farkasI) ⟨⟨⟨1, by decide⟩, args⟩, w⟩ = (Cmd.entry j.toNat a.toInt).apply a' := by
    simp only [next, hargs, cmdOf, Val.i64, Val.i32]
    rfl
  rw [hn]
  exact ⟨entryM m j a, holds_withMach hs₀ _, inv_entry (rep_unique hs₀ ha') j a⟩

/-- The result `check` reports. -/
theorem check_answer {res : BitVec 32} {r : Result} {ft : FnType} {w : Answer ft}
    (hr : outcomeResult? (.normal [Val.i32 res]) = some r) (hw : Answer.ofResult? ft r = some w)
    (h1 : w.toResult = .values [Val.i32 1]) : res = 1 := by
  have hr' : r = .values [Val.i32 res] := (Option.some.inj hr).symm
  have hv : Result.values [Val.i32 res] = .values [Val.i32 1] :=
    hr' ▸ (Answer.toResult_of_ofResult? hw).symm.trans h1
  injection hv with hl
  injection hl with hv'
  injection hv' with hn
  injection hn

/-- **`check` meets its call specification.** -/
theorem spec_check (args : Typed (farkasExports.get ⟨2, by decide⟩).params) :
    FSpecValid P host (farkasI.addr ⟨2, by decide⟩)
      (callSpec farkasI Rep next Good ⟨⟨2, by decide⟩, args⟩) := by
  obtain ⟨fi₀, fi₁, fi₂, hfs, -, -, hm₂, -, -, hc₂, -, -, ht₂⟩ := farkasStore_funcs
  have hargs := typed_nil args.2
  refine FSpecValid.of_body_hwp (fi := fi₂) (code := ⟨⟨2⟩, [.i32, .i32], checkBody⟩)
    (fun s _ h => by rw [pre_funcs h, hfs]; rfl) hc₂ (FnType.expand_of_ofDefType? ht₂)
    (fun _ _ h => pre_len h) (fun s args' hpre => ?_)
  obtain ⟨rfl, rs, m, ⟨s₀, hs₀, rfl⟩, hI⟩ := hpre
  rw [hm₂, hargs]
  refine check_hwp hI.1 fun B nz f' hd => ⟨rfl, fun a' ha' r hr w hw => ⟨fun _ h1 => ?_, ?_⟩⟩
  · exact cert_of_check (rep_unique hs₀ ha') hd (check_answer hr hw h1)
  · exact ⟨checkEnd B, holds_withMach hs₀ _, inv_check hd⟩

/-- **Every export call meets its call specification**, at every profile and for every host. -/
theorem farkas_spec (f : farkasI.F.Op) :
    FSpecValid P host (farkasI.addr f.1) (callSpec farkasI Rep next Good f) := by
  obtain ⟨⟨j, hj⟩, args⟩ := f
  have hj' : j < 3 := hj
  match j, hj, hj', args with
  | 0, _, _, args => exact spec_row args
  | 1, _, _, args => exact spec_entry args
  | 2, _, _, args => exact spec_check args

end Silmaril.Wasm.Examples.Farkas