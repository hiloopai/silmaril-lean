module

public import Silmaril.Proofs.Wasm.Component.Reference.SpecToIR
public import Silmaril.Proofs.Wasm.Component.Reference.HostMap
public import Silmaril.Wasm.Binaryen.InlUnwrapClosed
public import Silmaril.Wasm.Binaryen.LinkBehaviours

/-!
# Typing of the core activation of an export call

The core activation of a lifted export of a `Simple` component runs the export of the
module's instance on lowered arguments. By type soundness of that run
(`Silmaril.Wasm.Game.ScalarInstance.answer_of_run`, `progress_hostOf`), at every profile:

* `run_results_typed`: returned values have the flat result types of the export;
* `run_no_callout`: no reached configuration is at a host call (the module has no imports),
  in the store of the instance or in any store that renames to it (`decompose?_mapH`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {H H' : Type}

/-- A host-call redex is one in the renamed store. -/
theorem decompose?_mapH (g : H → H') {s : Store H} {code : List Admin} {E : Ctx} {a : Nat}
    {hh : H} {args : List Execution.Core.Val} (hd : decompose? s code = some (E, a, hh, args)) :
    ∃ E', decompose? (Store.mapH g s) code = some (E', a, g hh, args) := by
  obtain ⟨fi, yy, ps, rs, hfi, hcode, hyy, he, hlen, rfl⟩ := decompose?_sound hd
  have hgi : (Store.mapH g s).funcs[a]? = some (FuncInst.mapH g fi) := by
    rw [Store.mapH_funcs_getElem?, hfi]
    rfl
  have hgc : (FuncInst.mapH g fi).code = .host (g hh) := by
    simp only [FuncInst.mapH, hcode, FuncCode.mapH]
  have hred := decompose?_redex hyy hgi he hlen hgc
  exact Silmaril.Wasm.Binaryen.Unwrap.redex_fill_closed hred E

/-- Flat views of typed numeric values have their types. -/
theorem toFlat?_types : ∀ (ts : List NumType) (vs : List Execution.Core.Val)
    (fvs : List Silmaril.Wasm.Execution.Runtime.Value),
    List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (ts.map .num) vs →
      vs.mapM toFlat? = some fvs → fvs.map (·.type) = ts
  | [], [], fvs, _, h => by
    cases (Option.some.inj h).symm
    rfl
  | t :: ts, v :: vs, fvs, .cons ⟨bits, hv⟩ hr, h => by
    subst hv
    obtain ⟨ws, hws, rfl⟩ : ∃ ws, vs.mapM toFlat? = some ws ∧
        fvs = (⟨t, bits⟩ : Execution.Runtime.Value) :: ws := by
      cases hm : vs.mapM toFlat? with
      | none => simp [List.mapM_cons, toFlat?, hm] at h
      | some ws =>
        refine ⟨ws, rfl, ?_⟩
        simp only [List.mapM_cons, toFlat?, hm] at h
        exact (Option.some.inj h).symm
    simp only [List.map_cons, toFlat?_types ts vs ws hr hws]
  | [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h

/-- The invocation of an export of the instance of `m` on flat values of its parameter types,
as an invocation of the instance's closed program. -/
structure TypedCall (P : Profile) (m : NumModule) (I : Silmaril.Wasm.Game.ScalarInstance)
    (k : Nat) (xs : List Flat) where
  /-- The operation of the closed program. -/
  f : I.F.Op
  /-- Its export type. -/
  hty : I.exports.get f.1 = fnOf m.exports[k]!.2
  /-- Its invocation. -/
  hinv : invoke I.store (I.addr f.1) f.2.1 =
    invoke I.store (I.addrs.getD k 0) (xs.map ofFlat)

/-- Lowered arguments of the parameter types give a typed call. -/
theorem typedCall {P : Profile} {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) {k : Nat} (hk : k < m.exports.length) {xs : List Flat}
    (hxs : xs.map (·.type) = m.exports[k].2.params) : Nonempty (TypedCall P m I k xs) := by
  let n : NumInstance :=
    { inst := I, imports := [], exports := m.exports, imports_eq := hI.2.1,
      exports_eq := hI.2.2 }
  let j : Fin I.exports.length := Fin.cast n.exports_length ⟨k, hk⟩
  have hj : I.exports.get j = fnOf m.exports[k].2 := by
    simp only [List.get_eq_getElem, j, Fin.val_cast]
    simp only [hI.2.2, List.getElem_map]
  have hparams : (I.exports.get j).params = xs.map fun x => .num x.type := by
    rw [hj]
    show m.exports[k].2.params.map _ = _
    rw [← hxs, List.map_map]
    rfl
  refine ⟨⟨⟨j, ⟨xs.map ofFlat, hparams ▸ forall₂_hasVal_ofFlat xs⟩⟩, ?_, rfl⟩⟩
  rw [hj, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

/-- The silent environment of an import-free instance throws nothing. -/
theorem throwsBelow_silent (I : Silmaril.Wasm.Game.ScalarInstance) (n : Nat) :
    Silmaril.Wasm.Game.ThrowsBelow (Silmaril.Wasm.Game.Env.silent I.E) n :=
  fun _ _ h => by cases h

/-- **Typed results**: a returned run of a lifted export returns values of its flat result
types. -/
theorem run_results_typed {P : Profile} {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) {k : Nat} (hk : k < m.exports.length) {xs : List Flat}
    (hxs : xs.map (·.type) = m.exports[k].2.params) {c' : Config Nat} {vs : List Execution.Core.Val}
    (run : Steps P Det.noHost (invoke I.store (I.addrs.getD k 0) (xs.map ofFlat)) c')
    (final : c'.code = vals vs) {fvs : List Silmaril.Wasm.Execution.Runtime.Value}
    (hf : vs.mapM toFlat? = some fvs) : fvs.map (·.type) = m.exports[k].2.results := by
  obtain ⟨tc⟩ := typedCall (P := P) hI hk hxs
  have run' : Steps P (Silmaril.Wasm.Game.hostOf I.imports (Silmaril.Wasm.Game.Env.silent _))
      (invoke I.store (I.addr tc.f.1) tc.f.2.1) c' := by
    rw [hostOf_nil hI.2.1, tc.hinv]
    exact run
  obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.answer_of_run hI.1.choose_spec.ok
    (throwsBelow_silent I _) run' (r := .values vs) final
  have ht : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (I.exports.get tc.f.1).results vs := by
    unfold Silmaril.Wasm.Game.Answer.ofResult? at hw
    dsimp only at hw
    split_ifs at hw with ht
    exact ht
  have hk' : m.exports[k]! = m.exports[k] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  rw [tc.hty, hk'] at ht
  exact toFlat?_types _ vs fvs ht hf

/-- **No callout**: a run of a lifted export never reaches a host call. -/
theorem run_no_callout {P : Profile} {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) {k : Nat} (hk : k < m.exports.length) {xs : List Flat}
    (hxs : xs.map (·.type) = m.exports[k].2.params) {c' : Config Nat}
    (run : Steps P Det.noHost (invoke I.store (I.addrs.getD k 0) (xs.map ofFlat)) c') :
    decompose? c'.store c'.code = none := by
  obtain ⟨tc⟩ := typedCall (P := P) hI hk hxs
  have run' : Steps P (Silmaril.Wasm.Game.hostOf I.imports (Silmaril.Wasm.Game.Env.silent _))
      (invoke I.store (I.addr tc.f.1) tc.f.2.1) c' := by
    rw [hostOf_nil hI.2.1, tc.hinv]
    exact run
  rcases Silmaril.Wasm.Game.ScalarInstance.progress_hostOf hI.1.choose_spec.ok
    (throwsBelow_silent I _) run' with ⟨r, hr⟩ | ⟨c'', hs⟩
  · rw [hr]
    exact Silmaril.Wasm.Binaryen.LinkBehaviours.decompose?_result r
  · rw [hostOf_nil hI.2.1] at hs
    exact decompose?_none_of_noRedex (Step.noRedex hs)

end Silmaril.Proofs.Wasm.Component.Reference
