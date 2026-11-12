module

public import Silmaril.Wasm.Wac.Bridge.DecodeImpl.Defs
public import Silmaril.Wasm.Wac.Bridge.DecodeNamed.Thms

/-!
# WAC bridge: component (implementation) binaries, proofs

* `replay_impl`: the projection replays sections that `Impl` relates to `ds` to the
  normal form of `ds`, from any state;
* `project_impl`: so a component that `Implements ds` projects to `normComponentDecls ds`;
* `code_silent`: code sections are silent.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat (normComponentDecls normComponentDecl normInstanceDecl normName)
open Wit.Project (PState step replay)

namespace DecodeImpl

theorem step_imp (st : PState) {i : Silmaril.Wasm.Component.Binary.Import} (hv : Wit.Project.isValueEq i.desc = false) :
    ∃ st', step st (.imports [i]) = some st' ∧
      st'.decls = st.decls ++ [normComponentDecl (.import i.name i.desc)] := by
  simp only [step, hv, Bool.false_eq_true, ite_false]
  split <;> exact ⟨_, rfl, by simp [PState.inst, PState.emit, normComponentDecl]⟩

theorem step_ty (st : PState) {t : DefType} (hr : Wit.Project.isResource t = false) :
    ∃ st', step st (.types [t]) = some st' ∧ st'.decls = st.decls ++ [normComponentDecl (.inst (.type t))] := by
  simp only [step, hr, Bool.false_eq_true, ite_false]
  exact ⟨_, rfl, rfl⟩

theorem step_exp (st : PState) {e : Silmaril.Wasm.Component.Binary.Export} {d : ExternDesc} (he : Wit.Project.exportDesc e = some d)
    (hv : Wit.Project.isValueEq d = false) :
    ∃ st', step st (.exports [e]) = some st' ∧
      st'.decls = st.decls ++ [normComponentDecl (.inst (.export e.name d))] := by
  simp only [step, he, hv, Bool.false_eq_true, ite_false]
  split <;> exact ⟨_, rfl, by simp [PState.inst, PState.emit, normComponentDecl, normInstanceDecl]⟩

/-- **The projection replays an implementation** to the normal form of its declarations. -/
theorem replay_impl {ss : List Section} {ds : List ComponentDecl} (h : Impl ss ds) :
    ∀ st : PState, ∃ st', replay st ss = some st' ∧ st'.decls = st.decls ++ normComponentDecls ds := by
  induction h with
  | nil => exact fun st => ⟨st, rfl, by simp [normComponentDecls]⟩
  | silent hs _ ih =>
    intro st
    obtain ⟨st1, h1, hd1⟩ := hs st
    obtain ⟨st', h', hd'⟩ := ih st1
    exact ⟨st', by simp [replay, h1, h'], by rw [hd', hd1]⟩
  | imp hv _ ih =>
    intro st
    obtain ⟨st1, h1, hd1⟩ := step_imp st hv
    obtain ⟨st', h', hd'⟩ := ih st1
    exact ⟨st', by simp [replay, h1, h'], by rw [hd', hd1]; simp [normComponentDecls]⟩
  | ty hr _ ih =>
    intro st
    obtain ⟨st1, h1, hd1⟩ := step_ty st hr
    obtain ⟨st', h', hd'⟩ := ih st1
    exact ⟨st', by simp [replay, h1, h'], by rw [hd', hd1]; simp [normComponentDecls]⟩
  | exp he hv _ ih =>
    intro st
    obtain ⟨st1, h1, hd1⟩ := step_exp st he hv
    obtain ⟨st', h', hd'⟩ := ih st1
    exact ⟨st', by simp [replay, h1, h'], by rw [hd', hd1]; simp [normComponentDecls]⟩

/-- **A component that implements `ds` projects to them** (in normal form). -/
theorem project_impl {c : Ast} {ds : List ComponentDecl} (h : Implements c ds) :
    Wit.Project.project c = some (normComponentDecls ds) := by
  obtain ⟨st', h', hd'⟩ := replay_impl h {}
  simp [Wit.Project.project, h', hd']

set_option linter.unusedTactic false in
/-- **Code is silent.** -/
theorem code_silent {s : Section} (h : Wit.Project.isCode s = true) : ∀ x ∈ Wit.Project.splitSection s, Silent x := by
  intro x hx st
  cases s <;> simp [Wit.Project.isCode] at h <;>
    simp [Wit.Project.splitSection] at hx <;> (try obtain ⟨_, _, rfl⟩ := hx) <;>
    exact ⟨st, by simp [step], rfl⟩

theorem impl_silents {ss : List Section} {ds : List ComponentDecl} (h : Impl ss ds) :
    ∀ {xs : List Section}, (∀ x ∈ xs, Silent x) → Impl (xs ++ ss) ds
  | [], _ => h
  | x :: _, hx => .silent (hx x List.mem_cons_self) (impl_silents h fun y hy => hx y (List.mem_cons_of_mem _ hy))

theorem impl_code {cs ss : List Section} {ds : List ComponentDecl} (hc : ∀ c ∈ cs, Wit.Project.isCode c = true)
    (h : Impl ss ds) : Impl (cs.flatMap Wit.Project.splitSection ++ ss) ds := by
  refine impl_silents h fun x hx => ?_
  obtain ⟨c, hc', hx'⟩ := List.mem_flatMap.1 hx
  exact code_silent (hc c hc') x hx'

theorem impl_shell : ∀ {ds : List ComponentDecl}, ds.all shellOk = true →
    Impl ((ds.filterMap shellSec).flatMap Wit.Project.splitSection) ds
  | [], _ => .nil
  | d :: ds, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := impl_shell h.2
    match d, h.1 with
    | .import n x, hx =>
      simp only [shellOk, Bool.not_eq_eq_eq_not, Bool.not_true] at hx
      simpa [shellSec, Wit.Project.splitSection] using Impl.imp (i := ⟨n, x⟩) hx ih
    | .inst (.type t), hx =>
      simp only [shellOk, Bool.not_eq_eq_eq_not, Bool.not_true] at hx
      simpa [shellSec, Wit.Project.splitSection] using Impl.ty hx ih
    | .inst (.export n x), hx =>
      simp only [shellOk, Bool.not_eq_eq_eq_not, Bool.not_true] at hx
      simpa [shellSec, Wit.Project.splitSection] using
        Impl.exp (e := ⟨n, ⟨descSort x, 0⟩, some x⟩) rfl hx ih

/-- **A shell implements its declarations**, whatever code precedes them. -/
theorem implements_shell {code : List Section} {ds : List ComponentDecl}
    (hc : ∀ c ∈ code, Wit.Project.isCode c = true) (h : ds.all shellOk = true) :
    Implements (shell code ds) ds := by
  unfold Implements shell
  rw [Ast.sections, List.flatMap_append]
  exact impl_code hc (impl_shell h)

end DecodeImpl

end Silmaril.Wasm.Wac.Bridge
