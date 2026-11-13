module

public import Silmaril.Wasm.Wac.TypeOfW.Defs
public import Silmaril.Wasm.Wac.Bridge.DecodeAnon.Thms
public import Silmaril.Proofs.Wasm.Wac.TypeOfW.Sim

/-!
# WAC: the kinds `TypeOf` infers are those of the world decoder

* `typeOf_world`: on a **world-shaped** component (`worldDecls`: imports, type definitions,
  type and instance aliases, core types, ascribed exports, and core modules, core instances and
  custom sections) whose declarations the world decoder reads, `pkgOfWorld ds = .ok r`,
  **`typeOf` infers exactly `r`**: the same imports and exports with the same kinds, the same
  definitions and the same nominal table. The inference is a step-by-step simulation of the
  decoder (`Silmaril.Proofs.Wasm.Wac.TypeOfW.Sim`: `decls_sim`).
* `worldDecls_worldSecs`, `typeOf_worldSecs`: a world's declarations written as sections are
  such a component.
* `typeOf_encode_anon`: with `Bridge.DecodeAnon.decode_encode_anon` (decoding inverts the WIT
  encoder on functions over anonymous value types), the component of the encoder's world
  declarations is inferred to have exactly the imports and exports `is`, `es` it encoded,
  provided its aliases are of the kinds both sides read alike (`DeclOk`, decidable on a
  concrete world; not proved of the encoder in general).

Not covered: the components wit-component writes are not world-shaped (`canon lift`, core
instantiation, shim components and inline instances); their kinds are compared with `wac` in
the tests (`tools/wac/tests/{differential,streams,builtins,resources}.sh`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.TypeOf

open Silmaril.Wasm Silmaril.Wasm.Component.Binary

/-- **The kinds `typeOf` infers are those of the world decoder** on world-shaped components. -/
theorem typeOf_world {c : Ast} {ds : List ComponentDecl} (hw : worldDecls c.sections = some ds)
    (hok : ∀ d ∈ ds, DeclOk d) {r : PkgType × Bridge.NomTable} (h : Bridge.pkgOfWorld ds = .ok r) :
    typeOf c = .ok r := by
  obtain ⟨ss⟩ := c
  simp only [Bridge.pkgOfWorld, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    obtain ⟨s', h1, hr⟩ := W.decls_sim ds hok {} hp
    have ho : (ofAst (.mk ss)).run {} = .ok ((s'.imports, s'.exports), s') := by
      simp only [ofAst, StateT.run_bind, W.ofSecs_eq ss hw, h1, W.ok_bindE]
      rfl
    simp only [typeOf, bind, Except.bind, ho, hr.imports, hr.exports, hr.sc]
    exact h

theorem worldDecls_worldSecs : ∀ ds : List ComponentDecl, worldDecls (worldSecs ds) = some ds
  | [] => rfl
  | d :: ds => by
    have hd : secDecls (declSec d) = some [d] := by
      rcases d with ⟨n, e⟩ | ⟨t⟩ | ⟨t⟩ | ⟨a⟩ | ⟨n, e⟩ <;> rfl
    have ih := worldDecls_worldSecs ds
    simp only [worldDecls, Option.map_eq_some_iff] at ih
    obtain ⟨ls, hls, hf⟩ := ih
    simp only [worldDecls, worldSecs, List.map_cons, List.mapM_cons, hd]
    simp only [worldSecs] at hls
    simp [hls, hf]

/-- A world written as a component is inferred to have the world decoder's type. -/
theorem typeOf_worldSecs {ds : List ComponentDecl} (hok : ∀ d ∈ ds, DeclOk d)
    {r : PkgType × Bridge.NomTable} (h : Bridge.pkgOfWorld ds = .ok r) :
    typeOf (.mk (worldSecs ds)) = .ok r :=
  typeOf_world (c := .mk (worldSecs ds)) (worldDecls_worldSecs ds) hok h

/-- **Against the WIT encoder**: the world the encoder writes for imports `is` and exports `es`
(functions over anonymous value types), written as a component, is inferred to have exactly
those imports and exports (when its aliases are of the kinds `DeclOk` allows). -/
theorem typeOf_encode_anon {is es : Externs} (his : Bridge.DecodeAnon.AnonFns is)
    (hes : Bridge.DecodeAnon.AnonFns es) :
    ∃ σ : Bridge.Scope,
      ((do Bridge.importDecls is; Bridge.exportDecls es : Bridge.TM Unit)).run { share := true } =
        .ok ((), σ) ∧
      ((∀ d ∈ σ.decls, DeclOk d) →
        typeOf (.mk (worldSecs σ.decls)) = .ok ({ imports := is, exports := es }, [])) := by
  obtain ⟨σ, hr, hp⟩ := Bridge.DecodeAnon.decode_encode_anon his hes
  exact ⟨σ, hr, fun hok => typeOf_worldSecs hok hp⟩

end Silmaril.Wasm.Wac.TypeOf
