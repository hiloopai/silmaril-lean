module

public import Silmaril.Wasm.SpecTec.Sim.Integrate.Defs
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms

/-!
# Round 2 integration: the fragment hypotheses are satisfiable

`forward_concrete` and `backward_concrete` take, besides the named bundles `Residue`, `Extra`
and `BwdOpen`, the hypotheses `HostFinite host`, `HostRespects hn host`, `Covered c` and
`Typed (simEnv B) hn c`. This file shows those are jointly satisfiable, for every `B`: the host
with no outcomes is finite and respects every encoding, and the configuration with the empty
store, any locals over the empty module instance and any value constants is `Covered` and
`Typed`. It does **not** show `Residue`, `Extra` or `BwdOpen` inhabited
(`docs/projects/spectec/README.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Integrate

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The host with no outcomes. -/
def emptyHost : HostSemantics H := fun _ _ _ _ => False

/-- The host with no outcomes is finite. -/
theorem hostFinite_emptyHost : HostFinite (emptyHost (H := H)) :=
  fun _ _ _ => ⟨[], fun _ => by simp [emptyHost]⟩

/-- The host with no outcomes respects every encoding. -/
theorem hostRespects_emptyHost (hn : H → String) : Prims.HostRespects hn (emptyHost (H := H)) :=
  fun _ _ _ _ _ _ _ _ ho => ho.elim

/-- Value constants hold no open instruction and no frame. -/
theorem codeOk_vals (vs : List Val) : CodeOk (vals vs) := by
  induction vs with
  | nil => exact .nil
  | cons v vs ih =>
    refine .cons ?_ ?_ ?_ ih
    · rcases v with ⟨⟨_⟩ | ⟨_⟩, _⟩ | _ | _ <;> rfl
    · intro n fi body h
      rcases v with ⟨⟨_⟩ | ⟨_⟩, _⟩ | _ | _ <;> cases h
    · rcases v with ⟨⟨_⟩ | ⟨_⟩, _⟩ | _ | _ <;> exact .nil

/-- A frame over the empty module instance names no aggregate type. -/
theorem unpacked_empty (ls : List (Option Val)) : Aggregates.Unpacked ⟨ls, {}⟩ :=
  fun x d _ hx _ => by simp [Frame.type?] at hx

/-- The empty store satisfies the store bounds. -/
theorem storeOk_empty : StoreOk ({} : Store H) :=
  ⟨⟨by simp, by simp⟩, ⟨by simp, by simp, by simp⟩, by simp⟩

/-- **The fragment hypotheses of `forward_concrete`/`backward_concrete` are satisfiable**, for
every `B` and encoding `hn`: a finite host respecting `hn`, and a configuration that is both
`Covered` and `Typed`. -/
theorem fragment_inhabited (B : Builtins) (hn : H → String) :
    ∃ host : HostSemantics H, HostFinite host ∧ Prims.HostRespects hn host ∧
      ∃ c : Config H, Covered c ∧ Typed (simEnv B) hn c :=
  ⟨emptyHost, hostFinite_emptyHost, hostRespects_emptyHost hn, ⟨{}, ⟨[], {}⟩, vals []⟩,
    ⟨codeOk_vals [], unpacked_empty [], storeOk_empty⟩, Typing.typed_vals hn [] []⟩

end Silmaril.Wasm.SpecTec.Sim.Integrate
