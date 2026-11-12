module

public import Silmaril.Wasm.Wit.Project.Ext.Defs

/-!
# The extended projection: conservative, and strictly larger

* `projectX_of_project`: where `project` is defined, `projectX` is defined and equal;
* `projectX_resource`: a component that defines a resource, lifts a constructor for
  it and exports both without type ascriptions projects to the world exporting
  `(type (sub resource))` and the function, while `project` of it is `none`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component.Binary

theorem step_withDesc (s : PState) (e : Export) (d : ExternDesc) (h : exportDesc e = some d) :
    step s (.exports [{ e with desc := some d }]) = step s (.exports [e]) := by
  have h2 : exportDesc { e with desc := some d } = some d := rfl
  simp only [step, h, h2]

theorem track_hoisted (x : XState) (sec : Section) : (track x sec).hoisted = x.hoisted := by
  unfold track
  split <;> (try split) <;> rfl

theorem stepX_types (x : XState) (hh : x.hoisted = []) (rest : List Section) (t : DefType)
    (p : PState) (hp : step x.base (.types [t]) = some p) :
    ∃ y, stepX x rest (.types [t]) = some y ∧ y.base = p ∧ y.hoisted = [] := by
  have hr : isResource t = false := by
    cases ht : isResource t
    · rfl
    · simp [step, ht] at hp
  simp only [stepX, hr, Bool.false_eq_true, ite_false, hp, Option.map_some]
  exact ⟨_, rfl, rfl, by rw [track_hoisted, hh]⟩

theorem stepX_exports (x : XState) (hh : x.hoisted = []) (rest : List Section) (e : Export)
    (p : PState) (hp : step x.base (.exports [e]) = some p) :
    ∃ y, stepX x rest (.exports [e]) = some y ∧ y.base = p ∧ y.hoisted = [] := by
  obtain ⟨d, hd⟩ : ∃ d, exportDesc e = some d := by
    cases he : exportDesc e
    · simp [step, he] at hp
    · exact ⟨_, rfl⟩
  have hx : exportDescX x e = some d := by simp [exportDescX, hd]
  simp only [stepX, hh, List.not_mem_nil, and_false, ite_false, hx, step_withDesc _ _ _ hd, hp,
    Option.map_some]
  exact ⟨_, rfl, rfl, by rw [track_hoisted, hh]⟩

theorem stepX_of_step (x : XState) (hh : x.hoisted = []) (rest : List Section) (sec : Section)
    (p : PState) (hp : step x.base sec = some p) :
    ∃ y, stepX x rest sec = some y ∧ y.base = p ∧ y.hoisted = [] := by
  unfold stepX
  split
  · exact stepX_types x hh rest _ p hp
  · exact stepX_exports x hh rest _ p hp
  · rw [hp]
    exact ⟨_, rfl, rfl, by rw [track_hoisted, hh]⟩

theorem replayX_of_replay : ∀ (xs : List Section) (x : XState) (p : PState),
    x.hoisted = [] → replay x.base xs = some p →
      ∃ y, replayX x xs = some y ∧ y.base = p
  | [], x, p, _, h => by simp [replay] at h; exact ⟨x, rfl, h⟩
  | sec :: xs, x, p, hh, h => by
    simp only [replay] at h
    cases hs : step x.base sec with
    | none => simp [hs] at h
    | some q =>
      rw [hs, Option.bind_some] at h
      obtain ⟨y, hy, hyb, hyh⟩ := stepX_of_step x hh xs sec q hs
      obtain ⟨z, hz, hzb⟩ := replayX_of_replay xs y p hyh (by rw [hyb]; exact h)
      exact ⟨z, by simp [replayX, hy, hz], hzb⟩

/-- `projectX` extends `project`. -/
theorem projectX_of_project {c : Ast} {w : WorldType} (h : project c = some w) :
    projectX c = some w := by
  unfold project at h
  cases hr : replay {} (c.sections.flatMap splitSection) with
  | none => simp [hr] at h
  | some p =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨y, hy, hyb⟩ := replayX_of_replay _ ({} : XState) p rfl hr
    simp [projectX, hy, hyb, h]

/-- A component defining a resource `r` (type 0), `own<r>` (type 1), a constructor type
(type 2), a lifted constructor (function 0), and exporting the resource and the
constructor without type ascriptions. -/
def resComponent : Ast :=
  .mk [.types [.resource .i32 none, .val (.own 0),
      .func ⟨[("rep", .prim .u32)], some (.idx 1), false⟩],
    .canons [.lift 0 [] 2],
    .exports [⟨"r", ⟨.type, 0⟩, none⟩, ⟨"[constructor]r", ⟨.func, 0⟩, none⟩]]

theorem project_resComponent : project resComponent = none := by decide

/-- Its world: the resource is exported abstractly at its definition's index (type 0),
`own<r>` and the constructor type keep their indices, the component's export of the
resource is the alias type 3, and the constructor is exported with its lifted type. -/
theorem projectX_resComponent : projectX resComponent = some
    [.inst (.export "r" (.type .subResource)),
     .inst (.type (.val (.own 0))),
     .inst (.type (.func ⟨[("rep", .prim .u32)], some (.idx 1), false⟩)),
     .inst (.alias ⟨.type, .outer 0 0⟩),
     .inst (.export "[constructor]r" (.func 2))] := rfl

end Silmaril.Wasm.Wit.Project
