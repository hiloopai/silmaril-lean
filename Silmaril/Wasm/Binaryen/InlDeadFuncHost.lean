module

public import Silmaril.Wasm.Binaryen.InlAssemble

@[expose] public section

/-! # Code-respecting typed hosts never return, in any valid store

`InlS.host_no_return` needs a Wasm function in the store. The host function being called
suffices instead: the validity of a host function instance does not look at its `module`
field, so the store where the called function's `module` is changed is valid too, and it
agrees with the original one up to code. A code-respecting host may return the same
outcome there; `HostOk` then makes the new store extend both stores, but extension keeps
the `module` field of functions (`host_never_returns`).

So typed runs are classified (`classif_of_ok_any`, `reach_classif_any`) without any
assumption on the functions of the store.
-/

namespace Silmaril.Wasm.Binaryen.InlDF

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- A module instance different from `mi`. -/
def otherModule (mi : ModuleInst) : ModuleInst := { mi with datas := 0 :: mi.datas }

theorem otherModule_ne (mi : ModuleInst) : otherModule mi ≠ mi := by
  intro h
  have := congrArg (fun m => m.datas.length) h
  simp [otherModule] at this

/-- The function list with the `module` field of the function at `a` changed. -/
def otherFuncs (fs : List (FuncInst H)) (a : Nat) (fi : FuncInst H) : List (FuncInst H) :=
  fs.set a ⟨fi.type, otherModule fi.module, fi.code⟩

theorem sameTypes_otherFuncs {fs : List (FuncInst H)} {a : Nat} {fi : FuncInst H}
    (hfi : fs[a]? = some fi) : SameTypes (otherFuncs fs a fi) fs := by
  unfold SameTypes otherFuncs
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, List.getElem?_set]
  obtain ⟨ha, hfa⟩ := List.getElem?_eq_some_iff.mp hfi
  split
  · subst_vars
    simp [ha]
  · rfl

/-- **A code-respecting typed host never returns** from a typed host call in a valid
store. -/
theorem host_never_returns {host : HostSemantics H} (hR : HostRespectsCode host)
    (hok : HostOk host) {s : Store H} (hs : StoreOk s) {hh : H} {args : List Val}
    (hargs : ArgsOk s hh args) {s' : Store H} {r : Result}
    (hret : host hh s args (.returned s' r)) : False := by
  obtain ⟨fi, hfi, hc, ps, rs, he, hvs⟩ := hargs
  obtain ⟨a, ha⟩ := List.getElem?_of_mem hfi
  set fi₂ : FuncInst H := ⟨fi.type, otherModule fi.module, fi.code⟩ with hfi₂def
  set s₂ := withFuncs s (otherFuncs s.funcs a fi) with hs₂
  have hT := sameTypes_otherFuncs ha
  have hlt := (List.getElem?_eq_some_iff.mp ha).1
  have ha₂ : s₂.funcs[a]? = some fi₂ := by
    show (otherFuncs s.funcs a fi)[a]? = _
    unfold otherFuncs
    rw [List.getElem?_set_self hlt]
  have hs₂ok : StoreOk s₂ := by
    refine storeOk_withFuncs hs hT fun g hg => ?_
    unfold otherFuncs at hg
    rcases List.mem_or_eq_of_mem_set hg with hg | rfl
    · exact funcInstOk_withFuncs hT (hs.funcs g hg)
    · cases hs.funcs fi hfi with
      | wasm _ _ hcode => rw [hcode] at hc; cases hc
      | host hdt he' hcode => exact .host hdt he' hcode
  have hret₂ : host hh s₂ args (.returned s' r) :=
    hR hh s s₂ args _ ⟨hT.symm, rfl⟩ hret
  have h₁ := (hok s fi hh args ps rs hs hfi hc he hvs).2 _ hret
  have h₂ := (hok s₂ fi₂ hh args ps rs hs₂ok (List.mem_of_getElem? ha₂) hc he
    (hvs.imp fun _ _ h => valOk_withFuncs hT h)).2 _ hret₂
  obtain ⟨-, hE₁, -⟩ := h₁
  obtain ⟨-, hE₂, -⟩ := h₂
  obtain ⟨y₁, hy₁, -, hm₁, -⟩ := hE₁.funcs.get ha
  obtain ⟨y₂, hy₂, -, hm₂, -⟩ := hE₂.funcs.get ha₂
  rw [hy₁] at hy₂
  cases hy₂
  exact otherModule_ne fi.module (hm₂.trans hm₁.symm)

/-- **Typed configurations are classified**, in any valid store. -/
theorem classif_of_ok_any {P : Numerics.Profile} {host : HostSemantics H}
    (hR : HostRespectsCode host) (hok : HostOk host) {c : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) : Classif P host c := by
  intro c' hs
  rcases Step.split_host hs with hn | ⟨E, a, hh, args, hd, ⟨s', r, hret, -⟩ | ⟨hdiv, rfl⟩⟩
  · exact .inl hn
  · exact absurd hret fun h => host_never_returns hR hok (ConfigOk.storeOk hc)
      (argsOk_of_redex (P := P) hc hd) h
  · exact .inr ⟨rfl, E, a, hh, args, hd, hdiv⟩

section det

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

/-- **Typed runs are classified** and keep the functions of the store. -/
theorem reach_classif_any {host : HostSemantics H} (hR : HostRespectsCode host)
    (hok : HostOk host) {c : Config H} {ts : List CValType} (hc : ConfigOk c ts) :
    ∀ x, Steps PD host c x → Classif PD host x ∧ x.store.funcs = c.store.funcs := by
  intro x hx
  induction hx with
  | refl => exact ⟨classif_of_ok_any hR hok hc, rfl⟩
  | @tail y z hy hst ih =>
    obtain ⟨hcl, hfs⟩ := ih
    have hfz : z.store.funcs = c.store.funcs := by
      rcases hcl z hst with hn | ⟨rfl, -⟩
      · rw [noHost_funcs hn, hfs]
      · exact hfs
    exact ⟨classif_of_ok_any hR hok (Steps.safe hok hc (hy.tail hst)).1, hfz⟩

end det

end Silmaril.Wasm.Binaryen.InlDF
