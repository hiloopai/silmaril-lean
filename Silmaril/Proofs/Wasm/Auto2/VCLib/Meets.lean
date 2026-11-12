module

public import Silmaril.Proofs.Wasm.Auto2.VCLib.Conds
public import Silmaril.Proofs.Wasm.Auto2.VCBridge.Mod

/-!
# Contracts of the VC library: entries and reference functions

The proved contracts `sumEntry`, `maxEntry`, `addEntry`, `div10Entry` (`Silmaril.Wasm.Auto2.VCBridge.VcEntry`:
their conditions are the generator's conditions on the specification library's programs, proved
in `Silmaril.Proofs.Wasm.Auto2.VCLib.Conds`), the list `entries` that `wasm-check` searches,
and the module-level results: the benchmark programs meet the reference functions of
`Silmaril.Wasm.Auto.FrontBench` at every profile (`sum_meets`, the `sum-ref` case; `max_meets'`,
`add_meets'`, `div10Mulhi_meets'`), each by one kernel evaluation of `vcCheck` and `modMeets_of_vcCheck`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCLib

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto2.VCGen Silmaril.Wasm.Auto2.VCBridge
open Silmaril.Wasm.Auto.Front (ModMeets Rel)
open Silmaril.Wasm.Auto.Equiv (TypedVals)

/-! ## Entries -/

/-- `sum n = triBV n` (total), proved on `Silmaril.WasmSpec.SumTo.sumFunc`. -/
def sumEntry : VcEntry where
  name := "sum"
  F := sumFns
  S := sumSpec
  fuel := libFuel
  conds := genFunc sumSpec Silmaril.WasmSpec.SumTo.sumFunc libFuel
  valid := sum_vcs
  total := rfl
  calls := rfl
  mem := rfl

/-- The signed maximum (total), proved on `Silmaril.WasmSpec.Max.maxFunc`. -/
def maxEntry : VcEntry where
  name := "max"
  F := {}
  S := maxSpec
  fuel := libFuel
  conds := genFunc maxSpec Silmaril.WasmSpec.Max.maxFunc libFuel
  valid := max_vcs
  total := rfl
  calls := rfl
  mem := rfl

/-- `x + y` (total), proved on `Silmaril.WasmSpec.Adder.addFunc`. -/
def addEntry : VcEntry where
  name := "add"
  F := {}
  S := addSpec
  fuel := libFuel
  conds := genFunc addSpec Silmaril.WasmSpec.Adder.addFunc libFuel
  valid := add_vcs
  total := rfl
  calls := rfl
  mem := rfl

/-- `x / 10` on `i64` (total), proved on the multiply-high kernel `div10MulhiFunc`. -/
def div10Entry : VcEntry where
  name := "div10"
  F := {}
  S := div10Spec
  fuel := libFuel
  conds := genFunc div10Spec div10MulhiFunc libFuel
  valid := div10_vcs
  total := rfl
  calls := rfl
  mem := rfl

/-- The library. -/
def entries : List VcEntry := [sumEntry, maxEntry, addEntry, div10Entry]

/-! ## Typed values -/

theorem typed1 {t : IntType} {vs : List Val} (h : TypedVals [t] vs) :
    ∃ x : BitVec t.width, vs = [.num ⟨.int t, x⟩] := by
  obtain ⟨hl, hi⟩ := h
  match vs, hl with
  | [a], _ =>
    obtain ⟨x, hx⟩ := hi 0 (by simp)
    exact ⟨x, by simpa using hx⟩

theorem typed2 {t u : IntType} {vs : List Val} (h : TypedVals [t, u] vs) :
    ∃ (x : BitVec t.width) (y : BitVec u.width), vs = [.num ⟨.int t, x⟩, .num ⟨.int u, y⟩] := by
  obtain ⟨hl, hi⟩ := h
  match vs, hl with
  | [a, b], _ =>
    obtain ⟨x, hx⟩ := hi 0 (by simp)
    obtain ⟨y, hy⟩ := hi 1 (by simp)
    exact ⟨x, y, by simp only [List.cons.injEq, and_true]; exact ⟨by simpa using hx, by simpa using hy⟩⟩

theorem res1 {t : IntType} {res : List Val} (h : res.map valTy = [some t]) :
    ∃ y : BitVec t.width, res = [.num ⟨.int t, y⟩] := by
  match res, h with
  | [r], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    unfold valTy at h
    split at h
    · rename_i t' y
      cases h
      exact ⟨y, rfl⟩
    · cases h
  | [], h => simp at h
  | _ :: _ :: _, h => simp at h

theorem typed1_32 {vs : List Val} (h : TypedVals [.i32] vs) :
    ∃ x : BitVec 32, vs = [.num ⟨.int .i32, x⟩] := typed1 h

theorem typed2_32 {vs : List Val} (h : TypedVals [.i32, .i32] vs) :
    ∃ x y : BitVec 32, vs = [.num ⟨.int .i32, x⟩, .num ⟨.int .i32, y⟩] := typed2 h

theorem typed1_64 {vs : List Val} (h : TypedVals [.i64] vs) :
    ∃ x : BitVec 64, vs = [.num ⟨.int .i64, x⟩] := typed1 h

theorem res1_64 {res : List Val} (h : res.map valTy = [some .i64]) :
    ∃ y : BitVec 64, res = [.num ⟨.int .i64, y⟩] := res1 h

theorem res1_32 {res : List Val} (h : res.map valTy = [some .i32]) :
    ∃ y : BitVec 32, res = [.num ⟨.int .i32, y⟩] := res1 h

/-! ## Reference functions -/

open Silmaril.Wasm.Auto.FrontBench (sumProg sumRef maxProg maxRef addProg addRef div10Mulhi
  div10RefFn)

/-- `sumRef` agrees with `sumEntry`'s postcondition. -/
theorem sum_ref : RefOK sumEntry sumRef := by
  intro vs res B hvs hres hpost
  obtain ⟨x, rfl⟩ := typed1_32 hvs
  obtain ⟨y, rfl⟩ := res1_32 hres
  left
  have hy : y = Silmaril.WasmSpec.SumTo.triBV x := by
    simp [sumEntry, sumSpec, sumFns, Fm.den, Tm.den, Env.get, valEnv, Fns.app1,
      Silmaril.Wasm.Auto.VCGen.relP, Silmaril.Wasm.Auto.VCGen.relW] at hpost
    exact hpost
  subst hy
  rfl

/-- `maxRef` agrees with `maxEntry`'s postcondition. -/
theorem max_ref : RefOK maxEntry maxRef := by
  intro vs res B hvs hres hpost
  obtain ⟨x, y, rfl⟩ := typed2_32 hvs
  obtain ⟨z, rfl⟩ := res1_32 hres
  left
  have hz : z = Silmaril.WasmSpec.Max.smax x y := by
    simp only [maxEntry, maxSpec, Fm.den, Tm.den, Env.get, valEnv, Silmaril.Wasm.Auto.VCGen.relP,
      Silmaril.Wasm.Auto.VCGen.relW, Silmaril.Wasm.Auto.VCGen.iteT, Silmaril.Wasm.Auto.VCGen.relV,
      Silmaril.Wasm.Auto.VCGen.nz32] at hpost
    simp [Silmaril.Wasm.Auto.VCGen.relB, Silmaril.Wasm.Numerics.bool32] at hpost
    rw [hpost]
    simp only [Silmaril.WasmSpec.Max.smax]
  subst hz
  rfl

/-- `addRef` agrees with `addEntry`'s postcondition. -/
theorem add_ref : RefOK addEntry addRef := by
  intro vs res B hvs hres hpost
  obtain ⟨x, y, rfl⟩ := typed2_32 hvs
  obtain ⟨z, rfl⟩ := res1_32 hres
  left
  have hz : z = x + y := by
    simp [addEntry, addSpec, Fm.den, Tm.den, Env.get, valEnv, Silmaril.Wasm.Auto.VCGen.relP,
      Silmaril.Wasm.Auto.VCGen.relW, Silmaril.Wasm.Auto.VCGen.binT, Silmaril.Wasm.Auto.VCGen.binW] at hpost
    exact hpost
  subst hz
  rfl

/-- `div10RefFn` agrees with `div10Entry`'s postcondition. -/
theorem div10_ref : RefOK div10Entry div10RefFn := by
  intro vs res B hvs hres hpost
  obtain ⟨x, rfl⟩ := typed1_64 hvs
  obtain ⟨y, rfl⟩ := res1_64 hres
  left
  have hy : y = x / 10#64 := by
    simp [div10Entry, div10Spec, Fm.den, Tm.den, Env.get, valEnv, Silmaril.Wasm.Auto.VCGen.relP,
      Silmaril.Wasm.Auto.VCGen.relW, Silmaril.Wasm.Auto.VCGen.binT, Silmaril.Wasm.Auto.VCGen.binW,
      Silmaril.Wasm.Auto.VCGen.litT] at hpost
    exact hpost
  subst hy
  rfl

/-- The reference contracts of the front-end benchmark, by case name (`wasm-check bench`
tries the contract of a reference-function case it leaves unknown). The reference function of
each is the case's own (`sumRef`, `maxRef`, `addRef` of `Silmaril.Wasm.Auto.FrontBench`). -/
def refEntries : List (String × RefEntry) :=
  [("sum-ref", ⟨sumEntry, sumRef, fun _ _ => trivial, sum_ref⟩),
   ("sum-offbyone-ref", ⟨sumEntry, sumRef, fun _ _ => trivial, sum_ref⟩),
   ("max-ref", ⟨maxEntry, maxRef, fun _ _ => trivial, max_ref⟩),
   ("max-unsigned-ref", ⟨maxEntry, maxRef, fun _ _ => trivial, max_ref⟩),
   ("add-ref", ⟨addEntry, addRef, fun _ _ => trivial, add_ref⟩),
   ("div10-mulhi-ref", ⟨div10Entry, div10RefFn, fun _ _ => trivial, div10_ref⟩)]

/-- The benchmark cases the VC stage proves (the summary stages of the front end leave them
`unknown`). -/
def vcProved : List String := ["sum-ref", "max-ref", "add-ref", "div10-mulhi-ref"]

/-- The `sum-ref` case: `SumTo`'s program meets the triangular numbers, at every profile (its
loop proved by the VC generator: invariant, variant, total correctness). -/
theorem sum_meets (R : Rel) (P : Profile) : ModMeets R.toProp P sumProg 0 sumRef :=
  modMeets_of_vcCheck (e := sumEntry) (Silmaril.Wasm.Auto.Bridge.rel_refl R) (by decide +kernel)
    (fun _ _ => trivial) sum_ref

/-- `Max`'s program meets the signed maximum, at every profile (by the VC generator). -/
theorem max_meets' (R : Rel) (P : Profile) : ModMeets R.toProp P maxProg 0 maxRef :=
  modMeets_of_vcCheck (e := maxEntry) (Silmaril.Wasm.Auto.Bridge.rel_refl R) (by decide +kernel)
    (fun _ _ => trivial) max_ref

/-- `Adder`'s program meets `x + y`, at every profile (by the VC generator). -/
theorem add_meets' (R : Rel) (P : Profile) : ModMeets R.toProp P addProg 0 addRef :=
  modMeets_of_vcCheck (e := addEntry) (Silmaril.Wasm.Auto.Bridge.rel_refl R) (by decide +kernel)
    (fun _ _ => trivial) add_ref

/-- The `div10` kernel (multiply-high) meets `x / 10`, at every profile (by the VC
generator). -/
theorem div10Mulhi_meets' (R : Rel) (P : Profile) :
    ModMeets R.toProp P div10Mulhi 0 div10RefFn :=
  modMeets_of_vcCheck (e := div10Entry) (Silmaril.Wasm.Auto.Bridge.rel_refl R) (by decide +kernel)
    (fun _ _ => trivial) div10_ref

end Silmaril.Wasm.Auto2.VCLib
