module

public import Silmaril.Wasm.JcoTool.New.Defs
public import Silmaril.Wasm.Perf.CoreMod.Thms
import Batteries.Data.List.Lemmas

/-!
# What a plan of `wasm-jco new` guarantees

`plan core w = .ok p` (`Silmaril.Wasm.JcoTool.New.plan`) gives:

* `plan_mod`: the plan's module is the decoded interface of `core` (`Lower.coreMod core`);
* `plan_lifts`: every world export is implemented by a core export of the module at the
  canonical ABI's core type (`LiftOk`): `f` at `liftCore f` for a sync export, with a
  post-return of the right type when there is one; `[async-lift-stackful]f` at
  `liftAsyncCore f false`, or `[async-lift]f` at `liftAsyncCore f true` with its callback at
  `callbackCore`, for an async export;
* `plan_reqs`: every core import of the module, in order, is classified (`classify`) under
  its module and field name, and its core type is the canonical type of what it asks for
  (`Req.coreTy`).

These are the canonical-ABI side conditions of the thin wrapper: they say that the
component `emit p` lifts and lowers at the right core types. That `emit` places them in the
sections as described is checked by validation (`tools/wasm-jco/tests`) and, for
memory-free synchronous worlds, by the read-back theorem `Check.irCheck_sound`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.New

open Silmaril.Wasm.Wit.Binary (Ty Func World WorldItem)
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component (CoreFuncTy)

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Export `f` is implemented by the module at the canonical core type. -/
inductive LiftOk (m : CoreMod) (f : Silmaril.Wasm.Wit.Binary.Func) : Lift → Prop
  | sync (t : CoreFuncTy) (pr : Option String) :
      f.async = false → liftCore f = .ok t → coreExport? m f.name = some t →
      LiftOk m f (.sync f.name pr)
  | stackful (t : CoreFuncTy) :
      f.async = true → liftAsyncCore f false = .ok t →
      coreExport? m ("[async-lift-stackful]" ++ f.name) = some t →
      LiftOk m f (.stackful ("[async-lift-stackful]" ++ f.name))
  | callback (t : CoreFuncTy) :
      f.async = true → liftAsyncCore f true = .ok t →
      coreExport? m ("[async-lift]" ++ f.name) = some t →
      coreExport? m ("[callback][async-lift]" ++ f.name) = some callbackCore →
      LiftOk m f (.callback ("[async-lift]" ++ f.name) ("[callback][async-lift]" ++ f.name))

theorem expectExport_ok {m : CoreMod} {n : String} {t : CoreFuncTy} {u : Unit}
    (h : expectExport m n t = .ok u) : coreExport? m n = some t := by
  unfold expectExport at h
  split at h
  · rename_i t' ht'
    by_cases e : t' = t
    · rw [ht', e]
    · simp [e] at h
  · cases h

theorem require_ok {b : Bool} {msg : String} {u : Unit} (h : require b msg = .ok u) : b = true := by
  cases b
  · cases h
  · rfl

theorem postReturn_ok {m : CoreMod} {f : Silmaril.Wasm.Wit.Binary.Func} {t : CoreFuncTy} {l : Lift}
    (h : postReturn m f t = .ok l) : ∃ pr, l = .sync f.name pr := by
  unfold postReturn at h
  split at h
  · split at h
    · cases h
      exact ⟨_, rfl⟩
    · cases h
  · cases h
    exact ⟨_, rfl⟩

theorem liftSync_ok {m : CoreMod} {f : Silmaril.Wasm.Wit.Binary.Func} {l : Lift} (ha : f.async = false)
    (h : liftSync m f = .ok l) : LiftOk m f l := by
  obtain ⟨t, ht, h₁⟩ := bind_ok h
  obtain ⟨_, he, h₂⟩ := bind_ok h₁
  obtain ⟨pr, rfl⟩ := postReturn_ok h₂
  exact .sync t pr ha ht (expectExport_ok he)

theorem liftCallback_ok {m : CoreMod} {f : Silmaril.Wasm.Wit.Binary.Func} {l : Lift} (ha : f.async = true)
    (h : liftCallback m f = .ok l) : LiftOk m f l := by
  obtain ⟨t, ht, h₁⟩ := bind_ok h
  obtain ⟨_, he, h₂⟩ := bind_ok h₁
  obtain ⟨_, hc, h₃⟩ := bind_ok h₂
  cases h₃
  exact .callback t ha ht (expectExport_ok he) (expectExport_ok hc)

theorem liftStackful_ok {m : CoreMod} {f : Silmaril.Wasm.Wit.Binary.Func} {l : Lift} (ha : f.async = true)
    (h : liftStackful m f = .ok l) : LiftOk m f l := by
  obtain ⟨t, ht, h₁⟩ := bind_ok h
  obtain ⟨_, he, h₂⟩ := bind_ok h₁
  cases h₂
  exact .stackful t ha ht (expectExport_ok he)

/-- `liftOf` is sound for `LiftOk`. -/
theorem liftOf_ok {m : CoreMod} {f : Silmaril.Wasm.Wit.Binary.Func} {l : Lift} (h : liftOf m f = .ok l) : LiftOk m f l := by
  unfold liftOf at h
  cases ha : f.async
  · rw [ha] at h
    exact liftSync_ok ha h
  · rw [ha] at h
    by_cases hc : (coreExport? m ("[async-lift]" ++ f.name)).isSome
    · exact liftCallback_ok ha (by simpa [hc] using h)
    · exact liftStackful_ok ha (by simpa [hc] using h)

/-- Core import `x` (module and field name, and core type) is the request `y.2` at its
canonical type. -/
def ReqOk (imps exps : List Silmaril.Wasm.Wit.Binary.Func) (x : (String × String) × (String × CoreFuncTy))
    (y : (String × String) × Req) : Prop :=
  y.1 = x.1 ∧ classify imps exps x.1.1 x.1.2 = .ok y.2 ∧ y.2.coreTy = .ok x.2.2

theorem reqOf_ok {imps exps : List Silmaril.Wasm.Wit.Binary.Func} {x : (String × String) × (String × CoreFuncTy)}
    {y : (String × String) × Req} (h : reqOf imps exps x = .ok y) : ReqOk imps exps x y := by
  obtain ⟨r, hr, h₁⟩ := bind_ok h
  obtain ⟨t', ht', h₂⟩ := bind_ok h₁
  obtain ⟨_, hq, h₃⟩ := bind_ok h₂
  cases h₃
  have e : x.2.2 = t' := of_decide_eq_true (require_ok hq)
  exact ⟨rfl, hr, e ▸ ht'⟩

/-- **What a plan guarantees.** -/
theorem plan_ok {core : ByteArray} {w : World} {p : Plan} (h : plan core w = .ok p) :
    Lower.coreMod core = .ok p.mod ∧ p.core = core ∧
      List.Forall₂ (LiftOk p.mod) p.exports p.lifts ∧
      List.Forall₂ (ReqOk p.imports p.exports) (p.mod.importNames.zip p.mod.imports) p.reqs := by
  obtain ⟨m, hm, h₁⟩ := bind_ok h
  obtain ⟨imps, _, h₂⟩ := bind_ok h₁
  obtain ⟨exps, _, h₃⟩ := bind_ok h₂
  obtain ⟨reqs, hreqs, h₄⟩ := bind_ok h₃
  obtain ⟨lifts, hlifts, h₅⟩ := bind_ok h₄
  obtain ⟨⟨mem, ra⟩, _, h₆⟩ := bind_ok h₅
  obtain ⟨_, _, h₇⟩ := bind_ok h₆
  obtain ⟨_, _, h₈⟩ := bind_ok h₇
  cases h₈
  have hl : List.Forall₂ (fun a b => liftOf m a = .ok b) exps lifts :=
    List.mapM_eq_ok_iff_forall₂.mp hlifts
  have hr := List.mapM_eq_ok_iff_forall₂.mp hreqs
  exact ⟨(congrFun Silmaril.Wasm.Perf.CoreMod.coreModF_eq core).symm.trans hm, rfl,
    hl.imp fun _ _ => liftOf_ok, hr.imp fun _ _ hy => reqOf_ok hy⟩

theorem plan_mod {core : ByteArray} {w : World} {p : Plan} (h : plan core w = .ok p) :
    Lower.coreMod core = .ok p.mod := (plan_ok h).1

theorem plan_lifts {core : ByteArray} {w : World} {p : Plan} (h : plan core w = .ok p) :
    List.Forall₂ (LiftOk p.mod) p.exports p.lifts := (plan_ok h).2.2.1

theorem plan_reqs {core : ByteArray} {w : World} {p : Plan} (h : plan core w = .ok p) :
    List.Forall₂ (ReqOk p.imports p.exports) (p.mod.importNames.zip p.mod.imports) p.reqs :=
  (plan_ok h).2.2.2

end Silmaril.Wasm.JcoTool.New
