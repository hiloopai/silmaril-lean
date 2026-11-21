module

import Silmaril.Formats.Dasl.Arena.Prolly.Index.Defs
import Silmaril.Semantics.Arena.Traits.Parsed.Thms

namespace Silmaril.Formats.Dasl.Arena.Prolly.Parsed.Examples

open Silmaril.Semantics.Arena
open Silmaril.Semantics.Arena.Traits
open Silmaril.Semantics.Prolly (Block)

private abbrev Node := Block (Handle Nat) Nat Nat

private def profile : Cas.Profile Nat Node := ⟨fun _ => none, fun _ => none⟩

private def initial : Cas.State Nat Nat Node := ⟨State.empty, fun _ => none⟩

private def leaf : Node := .leaf [(10, 25), (30, 55)]

private def root : Node := .branch 1 [(10, .local 0)]

private def api := CasArena.model (Key := Nat) profile

private def build : Step (Cas.State Nat Nat Node) SlotFault Empty Unit :=
  (api.toArena.insert 0 leaf).bind fun _ => api.toArena.insert 1 root

private def read (state : Cas.State Nat Nat Node) : Reader (Handle Nat) Nat Nat
  | .local index => match api.toArena.read state index with
    | some (some node) => .ok node
    | _ => .error (.missing (.local index))
  | .external name => .error (.missing (.external name))

example : (build initial).map (fun (_, state) =>
    (read state (.local 1), read state (.local 0), api.keyName state 1, api.get state 1)) =
    .ok (.ok root, .ok leaf, none, .ok none) := rfl

end Silmaril.Formats.Dasl.Arena.Prolly.Parsed.Examples
