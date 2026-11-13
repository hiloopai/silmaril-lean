module

public import Silmaril.Wasm.Wac.Bridge.EncodeUse.Defs
public import Silmaril.Wasm.Wit.Project.Infer.Thms
public import Silmaril.Wasm.Wac.Bridge.DecodeUse.Thms

/-!
# WAC bridge: components that define resources, projected and decoded

* `projectX_resComp`, `projectI_resComp`: the world of `resComp rs` is `resWorld 0 rs`
  (each resource hoisted as an export, the component's export as `alias outer 0`);
* `decCDeclsU_resWorld`: `decodePkgU`'s declaration reader on that world: each hoisted
  export is the resource, each `alias outer 0` pushes it again;
* `decCDecls_resWorld`: `decodePkg`'s reader fails on it as soon as there is a resource
  (the first `alias outer 0` looks for an enclosing scope).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Project
open Silmaril.Wasm.Component.Wat (normName)

namespace EncodeUse

theorem split_resSecs : ∀ (k : Nat) (rs : List String), (resSecs k rs).flatMap splitSection = resSecs k rs
  | _, [] => rfl
  | k, r :: rs => by
    simp [resSecs, splitSection, split_resSecs (k + 1) rs]

theorem replayX_resSecs : ∀ (k : Nat) (rs : List String) (s : XState), s.tCount = 2 * k → s.hoisted = [] →
    ∃ s', replayX s (resSecs k rs) = some s' ∧ s'.base.decls = s.base.decls ++ resWorld k rs
  | _, [], s, _, _ => ⟨s, rfl, by simp [resWorld]⟩
  | k, r :: rs, s, ht, hh => by
    obtain ⟨s', hs', hd⟩ := replayX_resSecs (k + 1) rs
      { track { track s (.types [.resource .i32 none]) with
          base := s.base.emit (.inst (.export ↑r (.type .subResource))), hoisted := [2 * k] }
          (.exports [⟨↑r, ⟨.type, 2 * k⟩, none⟩]) with
        base := (s.base.emit (.inst (.export ↑r (.type .subResource)))).emit
          (.inst (.alias ⟨.type, .outer 0 (2 * k)⟩)), hoisted := [] }
      (by simp [track, ht]; omega) rfl
    refine ⟨s', ?_, ?_⟩
    · simp only [resSecs, replayX, stepX, isResource, ite_true, resExport, ht, Option.map_some,
        Option.bind_some]
      simp [Option.bind, hh]
      simpa [normName] using hs'
    · rw [hd]; simp [PState.emit, resWorld]

/-- **The world of a component defining resources.** -/
theorem projectX_resComp (rs : List String) : projectX (resComp rs) = some (resWorld 0 rs) := by
  obtain ⟨s', hs', hd⟩ := replayX_resSecs 0 rs {} rfl rfl
  simp only [projectX, resComp, Ast.sections, split_resSecs, hs', Option.map_some, hd]
  rfl

theorem projectI_resComp (rs : List String) : projectI (resComp rs) = some (resWorld 0 rs) :=
  projectI_of_projectX (projectX_resComp rs)

open DecodeUse

attribute [local simp] ok_bindE' pure_okE Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind DecodeNamed.throw_run

theorem decCDeclsU_resWorld : ∀ (k : Nat) (rs : List String) (u : UScope) (es : Externs),
    u.base.types.size = 2 * k → ∃ u', (decCDeclsU (resWorld k rs) [] es).run u =
      .ok (([], es ++ rs.map fun r => (r, .type (.resource r))), u') ∧ u'.base.nom = u.base.nom
  | _, [], u, es, _ => ⟨u, by simp [resWorld, decCDeclsU], rfl⟩
  | k, r :: rs, u, es, h => by
    obtain ⟨u', hu', hn⟩ := decCDeclsU_resWorld (k + 1) rs
      { u with base := { u.base with types := (u.base.types.push (.res r)).push (.res r) } }
      (es ++ [(r, .type (.resource r))]) (by simp [h]; omega)
    refine ⟨u', ?_, hn⟩
    simp [resWorld, decCDeclsU, decIDeclU, decExternU, decExtern, decAliasU, onBase_run, pushTy,
      StateT.run_bind, StateT.run_get, ← h]
    simpa using hu'

/-- `decodePkg`'s reader: the first `alias outer 0` of a top-level world fails. -/
theorem decCDecls_resWorld (r : String) (rs : List String) (es : Externs) :
    ∃ e, (decCDecls (resWorld 0 (r :: rs)) [] es).run {} = .error e := by
  simp [resWorld, decCDecls, decIDecl, decExtern, decAlias, pushTy, StateT.run_bind, StateT.run_get,
    StateT.run_modify]

end EncodeUse

end Silmaril.Wasm.Wac.Bridge
