module

public import Silmaril.Wasm.Examples.WatSpecSt.Defs
public import Silmaril.Wasm.WatSpec.Thms

/-!
# The G accessors over the store: verification conditions and specifications

`rgetA_vc`, `rsetA_vc`, `fset6A_vc`: the verification conditions, each by `wat_vc` (globals read
and written through `globalVal`/`setGlobalIdx`, `br_table` over the 17 registers); `*_valid`:
the specifications (`AnnotatedSt.sound₀`), every profile and host relation; `rset_gv`: the
read-back form of `rset`'s postcondition (location `r` reads `v`, the others are unchanged), as
in x86-real's `rsetSpec` for `repG`.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.WatSpecSt

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.WatSpec
open Silmaril.Wasm.Logic.VC Silmaril.Wasm.Logic.Hoare

theorem rgetA_vc : rgetA.vc := by
  intro mi s args h
  obtain ⟨r, rfl, w, hr, hw⟩ := h
  refine ⟨rfl, ?_⟩
  wat_vc [rgetA, fnPost, gv_of_globalVal hw]

theorem rsetA_vc : rsetA.vc := by
  intro mi s args h
  obtain ⟨r, v, rfl, hr, hs⟩ := h
  refine ⟨rfl, ?_⟩
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hs
  wat_vc [rsetA, fnPost]

theorem fset6A_vc : fset6A.vc := by
  intro mi s args h
  obtain ⟨c, p, a, z, sg, o, rfl, hs⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
  obtain ⟨h17, h18, h19, h20, h21, h22⟩ := hs
  refine ⟨rfl, ?_⟩
  wat_vc [fset6A, fnPost, h17, h18, h19, h20, h21, h22]

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics Nat}

theorem rset_valid {fi : FuncInst Nat} {a : Nat} {ps rs : Validation.Ty (.list .val)}
    (hc : fi.code = .wasm rsetA.func) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 2) (hrs : rs.length = 0) : FSpecValid P host a (rsetA.spec fi a) :=
  rsetA.sound₀ rsetA_vc hc he hps hrs

theorem rget_valid {fi : FuncInst Nat} {a : Nat} {ps rs : Validation.Ty (.list .val)}
    (hc : fi.code = .wasm rgetA.func) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 1) (hrs : rs.length = 1) : FSpecValid P host a (rgetA.spec fi a) :=
  rgetA.sound₀ rgetA_vc hc he hps hrs

theorem fset6_valid {fi : FuncInst Nat} {a : Nat} {ps rs : Validation.Ty (.list .val)}
    (hc : fi.code = .wasm fset6A.func) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 6) (hrs : rs.length = 0) : FSpecValid P host a (fset6A.spec fi a) :=
  fset6A.sound₀ fset6A_vc hc he hps hrs

/-- `rset`'s postcondition read back through `gv`: location `r` reads `v`, every other location
is unchanged (distinct global addresses). -/
theorem rset_gv {mi : ModuleInst} {s s' : Store Nat} {r : BitVec 32} {v : BitVec 64}
    (hnd : mi.globals.Nodup) (hs : (globalVal s mi r.toNat).isSome)
    (h : s' = setGlobalIdx s mi r.toNat (Val.i64 v)) (k : Nat) :
    gv s' mi k = if k = r.toNat then v else gv s mi k := by
  subst h
  split
  · subst_vars; rw [gv_set_self hs]; rfl
  · exact gv_set_ne hnd ‹_›

end Silmaril.Wasm.Examples.WatSpecSt
