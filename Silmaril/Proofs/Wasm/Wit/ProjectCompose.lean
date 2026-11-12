module

public import Silmaril.Wasm.Wit.Project.Compose.Defs
public import Silmaril.Wasm.Wit.Project.Infer.Thms

/-!
# The projection and composition: proofs

* `projState_extend`: the projection of an extended component continues from the
  state of the component (the look-ahead for resource exports only grows);
* `projectI_instantiateC`, `projectI_aliasC_func`, `projectI_aliasC_created`: an
  instantiation, an alias of a function, and an alias of an instance export of a
  created instance keep the world;
* `projectI_aliasC_world`: an alias of an instance export of an imported or exported
  instance adds the alias to the world;
* `projectI_exportC`: an export of a function, instance or component adds an export
  declaration with the (ascribed or inferred) type.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat (normName)

/-! ## Extension -/

theorem resExport_append_of_some (t : Nat) (n : ExternName) (more : List Section) :
    ∀ rest : List Section, resExport t rest = some n → resExport t (rest ++ more) = some n
  | [], h => nomatch h
  | x :: rest, h => by
    have ih := resExport_append_of_some t n more rest
    cases x with
    | exports xs =>
      rcases xs with _ | ⟨e, _ | ⟨f, r⟩⟩
      · exact ih h
      · by_cases he : e.item = ⟨.type, t⟩
        · simpa [resExport, he] using h
        · have h' : resExport t rest = some n := by simpa [resExport, he] using h
          simpa [resExport, he] using ih h'
      · exact ih h
    | _ => exact ih h

theorem stepX_append_rest {s y : XState} {rest : List Section} {x : Section}
    (more : List Section) (h : stepX s rest x = some y) : stepX s (rest ++ more) x = some y := by
  rcases em (∃ t, x = .types [t]) with ⟨t, rfl⟩ | h1
  · rw [stepX_types_eq] at h ⊢
    by_cases hr : isResource t = true
    · rw [ite_eq_left hr] at h ⊢
      obtain ⟨n, hn, hy⟩ := Option.map_eq_some_iff.mp h
      rw [resExport_append_of_some _ _ more rest hn]
      exact congrArg some hy
    · rw [ite_eq_right hr] at h ⊢
      exact h
  · rcases em (∃ e, x = .exports [e]) with ⟨e, rfl⟩ | h2
    · rw [stepX_exports_eq] at h ⊢
      exact h
    · have h1' : ∀ t, x ≠ .types [t] := fun t he => h1 ⟨t, he⟩
      have h2' : ∀ e, x ≠ .exports [e] := fun e he => h2 ⟨e, he⟩
      rw [stepX_other h1' h2'] at h ⊢
      exact h

theorem stepI_append_rest {s y : IState} {rest : List Section} {x : Section}
    (more : List Section) (h : stepI s rest x = some y) : stepI s (rest ++ more) x = some y := by
  unfold stepI stepBase at h ⊢
  by_cases hc : createdAlias s x = true
  · simpa [hc] using h
  · have hc' : createdAlias s x = false := by simpa using hc
    rw [hc'] at h ⊢
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [stepX_append_rest more hz]

theorem replayI_append : ∀ (a b : List Section) (s s' : IState),
    replayI s a = some s' → replayI s (a ++ b) = replayI s' b
  | [], _, s, s', h => by cases Option.some.inj h; rfl
  | x :: a, b, s, s', h => by
    have h1 : (stepI s a x).bind (fun s1 => replayI s1 a) = some s' := h
    obtain ⟨s1, hs1, h2⟩ := Option.bind_eq_some_iff.mp h1
    have hs1' : stepI s (a ++ b) x = some s1 := stepI_append_rest b hs1
    show (stepI s (a ++ b) x).bind (fun s1 => replayI s1 (a ++ b)) = _
    rw [hs1', Option.bind_some]
    exact replayI_append a b s1 s' h2

/-- **Extension**: the projection of `c` extended by `secs` continues from the state
after `c`. -/
theorem projState_extend {c : Ast} {s : IState} (h : projState c = some s) (secs : List Section) :
    projState (extendC c secs) = replayI s (secs.flatMap splitSection) := by
  show replayI {} ((c.sections ++ secs).flatMap splitSection) = _
  rw [List.flatMap_append]
  exact replayI_append _ _ _ _ h

theorem projectI_eq (c : Ast) : projectI c = (projState c).map (·.x.base.decls) := rfl

theorem infer_base (s : IState) (sec : Section) (y : XState) : (infer s sec y).base = y.base := by
  unfold infer
  split <;> rfl

/-- One step from a known state. -/
theorem projState_extend_one {c : Ast} {s : IState} (h : projState c = some s) (sec : Section)
    (hs : splitSection sec = [sec]) :
    projState (extendC c [sec]) = stepI s [] sec := by
  rw [projState_extend h, List.flatMap_cons, hs, List.flatMap_nil, List.append_nil]
  show (stepI s [] sec).bind (fun s' => replayI s' []) = _
  cases stepI s [] sec <;> rfl

/-! ## The operations -/

/-- **Instantiation keeps the world**: the created instance has no counterpart in it. -/
theorem projectI_instantiateC {c : Ast} {s : IState} (h : projState c = some s) (k : Nat)
    (args : List (String × SortIdx)) :
    projectI (instantiateC c k args) = some s.x.base.decls := by
  rw [projectI_eq, instantiateC, projState_extend_one h _ rfl]
  simp [stepI, stepBase, createdAlias, stepX, step, finish, infer_base, PState.inst]

/-- **An alias of a function keeps the world**: functions enter it only when exported. -/
theorem projectI_aliasC_func {c : Ast} {s : IState} (h : projState c = some s) (i : Nat)
    (n : String) : projectI (aliasC c .func i n) = some s.x.base.decls := by
  rw [projectI_eq, aliasC, projState_extend_one h _ rfl]
  simp [stepI, stepBase, createdAlias, stepX, step, finish, infer_base]

/-- **An alias of an instance export of a created instance keeps the world.** -/
theorem projectI_aliasC_created {c : Ast} {s : IState} (h : projState c = some s) (i : Nat)
    (n : String) (hi : s.x.base.lookup i = none) :
    projectI (aliasC c .instance i n) = some s.x.base.decls := by
  rw [projectI_eq, aliasC, projState_extend_one h _ rfl]
  simp [stepI, stepBase, createdAlias, hi, finish, infer_base, PState.inst]

/-- **An alias of an instance export of an instance of the world** adds the alias. -/
theorem projectI_aliasC_world {c : Ast} {s : IState} (h : projState c = some s) (i j : Nat)
    (n : String) (hi : s.x.base.lookup i = some j) :
    projectI (aliasC c .instance i n) =
      some (s.x.base.decls ++ [.inst (.alias ⟨.instance, .export j n⟩)]) := by
  rw [projectI_eq, aliasC, projState_extend_one h _ rfl]
  simp [stepI, stepBase, createdAlias, hi, stepX, step, finish, infer_base, PState.inst,
    PState.emit]

/-- **An export adds its declaration**, with the ascribed or inferred type
(`exportDescX`, which reads the inferred tables), for a function, instance or
component. -/
theorem projectI_exportC {c : Ast} {s : IState} (h : projState c = some s) (e : Export)
    (d : ExternDesc) (hd : exportDescX s.x e = some d) (hv : isValueEq d = false)
    (hsort : e.item.sort = .func ∨ e.item.sort = .instance ∨ e.item.sort = .component) :
    projectI (exportC c e) = some (s.x.base.decls ++ [.inst (.export (normName e.name) d)]) := by
  have hnt : e.item.sort ≠ .type := by rcases hsort with h | h | h <;> simp [h]
  rw [projectI_eq, exportC, projState_extend_one h _ rfl]
  have hx : stepX s.x [] (.exports [e]) =
      (step s.x.base (.exports [{ e with desc := some d }])).map fun b =>
        { track s.x (.exports [e]) with base := b } := by
    rw [stepX_exports_eq]
    simp [hnt, hd]
  have hdesc : exportDesc { e with desc := some d } = some d := rfl
  rcases hsort with hs | hs | hs <;>
    simp [stepI, stepBase, createdAlias, hx, step, hdesc, hv, hs, finish, infer_base,
      PState.inst, PState.emit]

/-! ## A composition, operation by operation -/

/-- The imports and types of `composeExample`. -/
def composeBase : Ast :=
  .mk [.types [.func ⟨[("x", .prim .u32)], none, false⟩,
      .instance [.alias ⟨.type, .outer 1 0⟩, .export "f" (.func 0)],
      .component [.inst (.alias ⟨.type, .outer 1 1⟩), .import "dep" (.instance 0),
        .inst (.export "api" (.instance 0))]],
    .imports [⟨"c", .component 2⟩, ⟨"dep", .instance 1⟩]]

/-- `composeExample` is `composeBase` composed by the operations, up to section
grouping, so it has the same projection. -/
theorem composeExample_ops :
    projectI composeExample = projectI (exportC (exportC (aliasC (aliasC (instantiateC composeBase 0
      [("dep", ⟨.instance, 0⟩)]) .instance 1 "api") .func 2 "f") ⟨"f", ⟨.func, 0⟩, none⟩)
      ⟨"api", ⟨.instance, 2⟩, none⟩) := by
  have h : composeExample.sections.flatMap splitSection = (exportC (exportC (aliasC (aliasC
      (instantiateC composeBase 0 [("dep", ⟨.instance, 0⟩)]) .instance 1 "api") .func 2 "f")
      ⟨"f", ⟨.func, 0⟩, none⟩) ⟨"api", ⟨.instance, 2⟩, none⟩).sections.flatMap splitSection := rfl
  unfold projectI
  rw [h]

end Silmaril.Wasm.Wit.Project
