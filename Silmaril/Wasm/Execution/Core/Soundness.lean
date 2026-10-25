module

public import Silmaril.Wasm.Execution.Core.Soundness.Preservation
public import Silmaril.Wasm.Execution.Core.Soundness.Progress
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux
public import Silmaril.Wasm.Execution.Core.Soundness.CallRefInv
public import Silmaril.Wasm.Execution.Core.Soundness.CallRefDef
public import Silmaril.Wasm.Execution.Core.Soundness.RefProgress
public import Silmaril.Wasm.Execution.Core.Soundness.AggregateProgress
public import Silmaril.Wasm.Execution.Core.Soundness.PresExn
public import Silmaril.Wasm.Execution.Core.Soundness.PresBranch
public import Silmaril.Wasm.Execution.Core.Soundness.PresBrCast
public import Silmaril.Wasm.Execution.Core.Soundness.FrameRegularity
public import Silmaril.Wasm.Execution.Core.Soundness.PresVariable
public import Silmaril.Wasm.Execution.Core.Soundness.RefRetype
public import Silmaril.Wasm.Execution.Core.Instantiation
public import Silmaril.Wasm.Execution.Core.Soundness.Instantiation

@[expose] public section

/-! # Type soundness of Core 3.0 (milestone statements, U18–U20)

The spec gives the judgments of §7 but no theorems. The statements:

* `Step.preservation` — a typed configuration steps to a typed configuration of
  the same result type, over an extended store;
* `Config.progress` — a typed configuration is terminal (values, an uncaught
  exception, or a trap) or can step;
* `Steps.safe` — the usual corollary: typed configurations never get stuck.

`Step.preservation` is in `Soundness/Preservation.lean`, `Config.progress` in
`Soundness/Progress.lean`; per-family lemmas in `Soundness/<Family>.lean`;
`ResultTyped`/`HostOk` in `Soundness/Defs.lean`.

Host functions are constrained by `HostOk`: on well-typed arguments in a valid
store the host has at least one outcome, and every returned outcome is a valid,
extended store with a result of the declared type.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- Type safety: reachable typed configurations are terminal or can step. -/
theorem Steps.safe {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {c c' : Config H} {ts : List CValType} (hc : ConfigOk c ts) (h : Steps P host c c') :
    ConfigOk c' ts ∧ (c'.Terminal ∨ ∃ c'', Step P host c' c'') := by
  have hok : ConfigOk c' ts := by
    induction h with
    | refl => exact hc
    | tail _ hstep ih => exact (Step.preservation hhost ih hstep).1
  exact ⟨hok, Config.progress hhost hok⟩

/-- Invocation of a function with well-typed arguments yields a typed configuration. -/
theorem invoke_ok {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s) (h : InvokeOk s a vs) :
    ∃ fi ps rs, s.funcs[a]? = some fi ∧ Expand fi.type (.func ps rs) ∧
      ConfigOk (invoke s a vs) rs.toList := by
  obtain ⟨fi, ps, rs, hfi, hexp, hvs⟩ := h
  refine ⟨fi, ps, rs, hfi, hexp, ?_⟩
  have hdt : TyOk {} fi.type := by
    cases hs.funcs fi (List.mem_of_getElem? hfi) <;> assumption
  have hmi : ModuleInstOk s ({} : ModuleInst)
      { types := [], recs := [], tags := [], globals := [], mems := [], tables := [],
        funcs := [], datas := ([] : List Nat).map fun _ => (), elems := [],
        refs := List.range 0 } :=
    ModuleInstOk.mk (k := 0) (by simp) .nil .nil .nil .nil .nil (by simp) .nil (by simp)
      (by simp) (by simp) (by simp)
  refine ⟨_, ⟨hs, _, [], hmi, .nil, rfl⟩, ?_⟩
  have hr : RefOk s (.func a) (.ref true (Ty.defHeap fi.type)) :=
    RefOk.sub (RefOk.func hfi) (TyOk.ref (TyOk.use (TyOk.dt hdt))) (Sub.refNull Sub.heapRefl)
  show AdminsOk s ({} : Context) _ _
  have hvals : AdminsOk s ({} : Context) (vals (vs ++ [.ref (.func a)]))
      (.plain [] (ps.toList ++ [Ty.refT true (Ty.defHeap fi.type)])) :=
    AdminsOk.of_vals (List.rel_append hvs (.cons (ValOk.ref hr) .nil))
      (ResultOk.append (Expand.resultOk hdt hexp).1 (fun t ht => by
        simp only [List.mem_singleton] at ht; subst ht
        exact TyOk.refv (TyOk.ref (TyOk.use (TyOk.dt hdt)))))
  have hcall := AdminsOk.single' (s := s) (C := {})
    (AdminOk.callRefType hdt hexp) (Expand.resultOk hdt hexp).2
  have hcode : (invoke s a vs).code =
      vals (vs ++ [.ref (.func a)]) ++ [.callRefType fi.type] := by
    simp [invoke, hfi, vals, Val.toAdmin]
  rw [hcode]
  simpa using AdminsOk.append (xs₁ := []) (xs₂ := []) hvals (by simp) hcall

/-- Instantiation of a valid module against typed imports yields a typed
configuration (of empty result type). -/
theorem Instantiate.ok {P : Profile} {host : HostSemantics H} (_hhost : HostOk host)
    {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H} (hs : StoreOk s)
    (h : Instantiate P host s m xas c) : ConfigOk c [] := by
  obtain ⟨xtE, xtI, hm, hxas⟩ := h.valid
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, hg, ht, he, ha, rfl⟩ := h.run
  cases hm with
  | mk htypes himports hC' hC htags hglobals hmems htables hfuncs hdata helems hstart
      hexports hdisjoint =>
    rename_i C' C
    obtain ⟨hs₄, hmi⟩ := Instantiate.alloc_ok hs htypes himports hC' hC htags hglobals hmems
      htables hfuncs hdata helems hstart hexports hdisjoint hxas hg ht he ha
    have hcode := InstrsOk.rangeRefs (Module.initCode_ok helems (by subst hC; rfl) hdata
      (by subst hC; rfl) hstart h.bounded.1)
    refine ⟨_, ⟨hs₄, _, [], hmi, .nil, rfl⟩, ?_⟩
    have hctx : ({ { C with refs := List.range C.funcs.length } with
        locals := ({ C with refs := List.range C.funcs.length } : Context).locals ++ [] } :
        Context) = { C with refs := List.range C.funcs.length } := by
      simp
    rw [hctx]
    convert AdminsOk.of_instrsOk (s := s₄) hcode using 1
    simp only [expression, List.map_append, Module.initCode]
    congr 1
    unfold Module.startCode
    cases m.start <;> rfl

end Silmaril.Wasm.Execution.Core
