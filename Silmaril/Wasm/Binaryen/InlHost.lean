module

public import Silmaril.Wasm.Binaryen.InlStore
public import Silmaril.Wasm.Binaryen.Equiv
public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.Execution.Core.Soundness

@[expose] public section

/-! # Code-respecting typed hosts never return

A host relation that respects code (`HostRespectsCode`) and is typed (`HostOk`) cannot
return from a call in a valid store that contains a Wasm function: the same outcome is
then allowed in the store where that function's body is prefixed by `nop`, which is
also valid, and `HostOk` makes the new store extend both, but extension keeps function
code. So such a host only diverges (`host_no_return`).

The argument types of a host call in a typed configuration come from progress for the
host `argHost`, which diverges exactly on typed arguments.
-/

namespace Silmaril.Wasm.Binaryen.InlS

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- The arguments of a host call are typed. -/
def ArgsOk (s : Store H) (h : H) (vs : List Val) : Prop :=
  ∃ fi ∈ s.funcs, fi.code = .host h ∧ ∃ ps rs, Expand fi.type (.func ps rs) ∧
    List.Forall₂ (ValOk s) vs ps.toList

/-- The host that diverges exactly on typed arguments. -/
def argHost : HostSemantics H := fun h s vs out => out = .diverged ∧ ArgsOk s h vs

theorem argHost_ok : HostOk (argHost (H := H)) := by
  intro s fi h vs ps rs _ hfi hc he hvs
  refine ⟨⟨.diverged, rfl, fi, hfi, hc, ps, rs, he, hvs⟩, fun out hout => ?_⟩
  obtain ⟨rfl, -⟩ := hout
  trivial

theorem decompose?_terminal {s : Store H} {c : Config H} (h : c.Terminal) :
    decompose? s c.code = none := by
  obtain ⟨r, hr⟩ := h
  rw [hr]
  cases r with
  | values vs => exact decompose?_vals_nil
  | trap =>
    exact decompose?_vals_cons_none (vs := []) (r := []) rfl (fun _ _ => decompHead_trap)
  | throw a =>
    exact decompose?_vals_cons_none (vs := [.ref (.exn a)]) (r := []) rfl
      (fun _ _ => decompHead_plain rfl)

/-- At a host-call redex of a typed configuration, the arguments are typed. -/
theorem argsOk_of_redex {P : Numerics.Profile} {c : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) {E : Ctx} {a : Nat} {hh : H} {args : List Val}
    (hd : decompose? c.store c.code = some (E, a, hh, args)) : ArgsOk c.store hh args := by
  rcases Config.progress (P := P) (host := argHost) argHost_ok hc with ht | ⟨c', hs⟩
  · rw [decompose?_terminal ht] at hd; cases hd
  · rcases Step.split_host hs with hn | ⟨E', a', hh', args', hd', hcase⟩
    · rw [decompose?_none_of_noRedex (Step.noRedex hn)] at hd; cases hd
    · rw [hd] at hd'
      simp only [Option.some.injEq, Prod.mk.injEq] at hd'
      obtain ⟨-, -, rfl, rfl⟩ := hd'
      rcases hcase with ⟨s', r, ⟨h, -⟩, -⟩ | ⟨⟨-, h⟩, -⟩
      · cases h
      · exact h

/-- The function list with the body of the Wasm function at `a` prefixed by `nop`. -/
def nopFuncs (fs : List (FuncInst H)) (a : Nat) (fi : FuncInst H) (code : Func) :
    List (FuncInst H) :=
  fs.set a ⟨fi.type, fi.module, .wasm { code with body := .nop :: code.body }⟩

theorem funcOk_nop {C : Context} {code : Func} {d : DefType} (h : FuncOk C code d) :
    FuncOk C { code with body := .nop :: code.body } d := by
  cases h with
  | mk hd he hl hb =>
    exact .mk hd he hl (InstrsOk.cons (xs₁ := []) (xs₂ := []) (.parametric .nop)
      (fun _ h => by cases h) hb)

theorem sameTypes_nopFuncs {fs : List (FuncInst H)} {a : Nat} {fi : FuncInst H} {code : Func}
    (hfi : fs[a]? = some fi) : SameTypes (nopFuncs fs a fi code) fs := by
  unfold SameTypes nopFuncs
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, List.getElem?_set]
  obtain ⟨ha, hfa⟩ := List.getElem?_eq_some_iff.mp hfi
  split
  · subst_vars
    simp [ha]
  · rfl

theorem storeOk_nop {s : Store H} (hs : StoreOk s) {a : Nat} {fi : FuncInst H} {code : Func}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code) :
    StoreOk (withFuncs s (nopFuncs s.funcs a fi code)) := by
  have hT := sameTypes_nopFuncs (code := code) hfi
  refine storeOk_withFuncs hs hT fun g hg => ?_
  unfold nopFuncs at hg
  rcases List.mem_or_eq_of_mem_set hg with hg | rfl
  · exact funcInstOk_withFuncs hT (hs.funcs g hg)
  · have hok := hs.funcs fi (List.mem_of_getElem? hfi)
    cases hok with
    | host _ _ hc => rw [hcode] at hc; cases hc
    | wasm hdt hm hc hf hsub =>
      rw [hcode] at hc
      cases hc
      exact .wasm hdt (moduleInstOk_withFuncs hT hm) rfl (funcOk_nop hf) hsub

/-- **A code-respecting typed host never returns** from a typed host call in a valid
store that contains a Wasm function. -/
theorem host_no_return {host : HostSemantics H} (hR : HostRespectsCode host)
    (hok : HostOk host) {s : Store H} (hs : StoreOk s) {aw : Nat} {fw : FuncInst H} {cw : Func}
    (hfw : s.funcs[aw]? = some fw) (hcw : fw.code = .wasm cw) {hh : H} {args : List Val}
    (hargs : ArgsOk s hh args) {s' : Store H} {r : Result}
    (hret : host hh s args (.returned s' r)) : False := by
  obtain ⟨fi, hfi, hc, ps, rs, he, hvs⟩ := hargs
  set s₂ := withFuncs s (nopFuncs s.funcs aw fw cw) with hs₂
  have hT := sameTypes_nopFuncs (code := cw) hfw
  have hs₂ok : StoreOk s₂ := storeOk_nop hs hfw hcw
  have hret₂ : host hh s₂ args (.returned s' r) :=
    hR hh s s₂ args _ ⟨hT.symm, rfl⟩ hret
  have h₁ := (hok s fi hh args ps rs hs hfi hc he hvs).2 _ hret
  have hfi₂ : fi ∈ s₂.funcs := by
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hfi
    show fi ∈ nopFuncs s.funcs aw fw cw
    unfold nopFuncs
    by_cases hia : aw = i
    · subst hia
      rw [hfw] at hi
      cases hi
      rw [hcw] at hc
      cases hc
    · exact List.mem_of_getElem? (by rw [List.getElem?_set_ne hia]; exact hi)
  have h₂ := (hok s₂ fi hh args ps rs hs₂ok hfi₂ hc he
    (hvs.imp fun _ _ h => valOk_withFuncs hT h)).2 _ hret₂
  obtain ⟨-, hE₁, -⟩ := h₁
  obtain ⟨-, hE₂, -⟩ := h₂
  obtain ⟨y₁, hy₁, -, -, hc₁, -⟩ := hE₁.funcs.get hfw
  have hfw₂ : s₂.funcs[aw]? = some ⟨fw.type, fw.module, .wasm { cw with body := .nop :: cw.body }⟩ := by
    show (nopFuncs s.funcs aw fw cw)[aw]? = _
    unfold nopFuncs
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hfw).1]
  obtain ⟨y₂, hy₂, -, -, hc₂, -⟩ := hE₂.funcs.get hfw₂
  rw [hy₁] at hy₂
  cases hy₂
  have e₁ := hc₁ cw hcw
  have e₂ := hc₂ _ rfl
  rw [e₁] at e₂
  injection e₂ with heq
  have := congrArg Func.body heq
  simp at this

end Silmaril.Wasm.Binaryen.InlS
