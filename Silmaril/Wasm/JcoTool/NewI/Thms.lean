module

public import Silmaril.Wasm.JcoTool.NewI.Defs
public import Silmaril.Wasm.JcoTool.New.Thms

/-!
# What a plan of `NewI` guarantees

`plan_ok`: when `NewI.plan core wf = .ok p`,

* the module is `core`'s decoded function interface (`Lower.coreMod`, silmaril's verified
  decoder) and the world is `wf`;
* the exported functions are those of the world, at world level and in every exported
  interface (`exportFns`), and each is implemented by the module at its canonical core type
  with named types flattened by `AbiR` (`LiftOk`: `f` / `key#f`, or the async forms, with the
  callback at `callbackCore`);
* every core import, in order, is classified (`classify`: a lower of a world or interface
  function, a task.return, a resource built-in of a resource of the world, a stream or future
  built-in, or a general built-in) and has the canonical type of what it asks for (`ReqOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.NewI

open Silmaril.Wasm.Wit.Binary (Func WorldFull)
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component (CoreFuncTy)
open Silmaril.Wasm.JcoTool.New (bind_ok expectExport_ok require_ok coreExport? Lift expectExport)

/-- Silmaril.Wasm.Component.Binary.Export `x` is implemented by the module at its canonical core type. -/
inductive LiftOk (wf : WorldFull) (m : CoreMod) (x : XFn) : Lift → Prop
  | sync (t : CoreFuncTy) (pr : Option String) :
      x.f.async = false → liftCoreR (rho wf) x.sc x.f = .ok t → coreExport? m x.core = some t →
      LiftOk wf m x (.sync x.core pr)
  | stackful (t : CoreFuncTy) :
      x.f.async = true → liftAsyncCoreR (rho wf) x.sc x.f false = .ok t →
      coreExport? m ("[async-lift-stackful]" ++ x.core) = some t →
      LiftOk wf m x (.stackful ("[async-lift-stackful]" ++ x.core))
  | callback (t : CoreFuncTy) :
      x.f.async = true → liftAsyncCoreR (rho wf) x.sc x.f true = .ok t →
      coreExport? m ("[async-lift]" ++ x.core) = some t →
      coreExport? m ("[callback][async-lift]" ++ x.core) = some callbackCore →
      LiftOk wf m x (.callback ("[async-lift]" ++ x.core) ("[callback][async-lift]" ++ x.core))

theorem liftSync_ok {wf : WorldFull} {m : CoreMod} {x : XFn} {l : Lift} (ha : x.f.async = false)
    (h : liftSync wf m x = .ok l) : LiftOk wf m x l := by
  obtain ⟨t, ht, h₁⟩ := bind_ok h
  obtain ⟨_, he, h₂⟩ := bind_ok h₁
  have hl : ∃ pr, l = .sync x.core pr := by
    split at h₂
    · split at h₂
      · cases h₂
        exact ⟨_, rfl⟩
      · cases h₂
    · cases h₂
      exact ⟨_, rfl⟩
  obtain ⟨pr, rfl⟩ := hl
  exact .sync t pr ha ht (expectExport_ok he)

theorem liftCallback_ok {wf : WorldFull} {m : CoreMod} {x : XFn} {l : Lift} (ha : x.f.async = true)
    (h : liftCallback wf m x = .ok l) : LiftOk wf m x l := by
  obtain ⟨t, ht, h₁⟩ := bind_ok h
  obtain ⟨_, he, h₂⟩ := bind_ok h₁
  obtain ⟨_, hc, h₃⟩ := bind_ok h₂
  cases h₃
  exact .callback t ha ht (expectExport_ok he) (expectExport_ok hc)

theorem liftStackful_ok {wf : WorldFull} {m : CoreMod} {x : XFn} {l : Lift} (ha : x.f.async = true)
    (h : liftStackful wf m x = .ok l) : LiftOk wf m x l := by
  obtain ⟨t, ht, h₁⟩ := bind_ok h
  obtain ⟨_, he, h₂⟩ := bind_ok h₁
  cases h₂
  exact .stackful t ha ht (expectExport_ok he)

/-- `liftOf` is sound for `LiftOk`. -/
theorem liftOf_ok {wf : WorldFull} {m : CoreMod} {x : XFn} {l : Lift} (h : liftOf wf m x = .ok l) :
    LiftOk wf m x l := by
  unfold liftOf at h
  cases ha : x.f.async
  · rw [ha] at h
    exact liftSync_ok ha h
  · rw [ha] at h
    by_cases hc : (coreExport? m ("[async-lift]" ++ x.core)).isSome
    · exact liftCallback_ok ha (by simpa [hc] using h)
    · exact liftStackful_ok ha (by simpa [hc] using h)

/-- Core import `x` (module and field name, core type) is the request `y.2` at its
canonical type. -/
def ReqOk (wf : WorldFull) (tb : Tables) (x : (String × String) × (String × CoreFuncTy))
    (y : (String × String) × IReq) : Prop :=
  y.1 = x.1 ∧ classify wf tb x.1.1 x.1.2 = .ok y.2 ∧ y.2.coreTy wf = .ok x.2.2

theorem reqOf_ok {wf : WorldFull} {tb : Tables} {x : (String × String) × (String × CoreFuncTy)}
    {y : (String × String) × IReq} (h : reqOf wf tb x = .ok y) : ReqOk wf tb x y := by
  obtain ⟨r, hr, h₁⟩ := bind_ok h
  obtain ⟨t', ht', h₂⟩ := bind_ok h₁
  obtain ⟨_, hq, h₃⟩ := bind_ok h₂
  cases h₃
  have e : x.2.2 = t' := of_decide_eq_true (require_ok hq)
  exact ⟨rfl, hr, e ▸ ht'⟩

/-- **What a plan guarantees.** -/
theorem plan_ok {core : ByteArray} {wf : WorldFull} {p : Plan} (h : plan core wf = .ok p) :
    Lower.coreMod core = .ok p.mod ∧ p.core = core ∧ p.wf = wf ∧ p.fns = exportFns wf ∧
      List.Forall₂ (LiftOk wf p.mod) p.fns p.lifts ∧
      List.Forall₂ (ReqOk wf p.tables) (p.mod.importNames.zip p.mod.imports) p.reqs := by
  obtain ⟨m, hm, h₁⟩ := bind_ok h
  obtain ⟨reqs, hreqs, h₂⟩ := bind_ok h₁
  obtain ⟨lifts, hlifts, h₃⟩ := bind_ok h₂
  obtain ⟨dtors, _, h₄⟩ := bind_ok h₃
  obtain ⟨⟨mem, ra⟩, _, h₅⟩ := bind_ok h₄
  obtain ⟨_, _, h₆⟩ := bind_ok h₅
  obtain ⟨_, _, h₇⟩ := bind_ok h₆
  cases h₇
  have hl : List.Forall₂ (fun a b => liftOf wf m a = .ok b) (exportFns wf) lifts :=
    List.mapM_eq_ok_iff_forall₂.mp hlifts
  have hr := List.mapM_eq_ok_iff_forall₂.mp hreqs
  exact ⟨(congrFun Silmaril.Wasm.Perf.CoreMod.coreModF_eq core).symm.trans hm, rfl, rfl, rfl,
    hl.imp fun _ _ => liftOf_ok, hr.imp fun _ _ hy => reqOf_ok hy⟩

end Silmaril.Wasm.JcoTool.NewI
