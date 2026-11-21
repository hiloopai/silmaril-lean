module

public import Silmaril.Formats.Dasl.Arena.Prolly.Surface.Defs
public import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Thms
import Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Surface

public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.Surface

open Silmaril.Semantics.Prolly (Policy)

variable {Owner Kind Name Key Payload Authority : Type} {basis : Indexed Name Key Payload}
variable {view next : View Owner Kind basis}

theorem mount_valid {owner : Owner} {kind : Kind} (mounted : mount basis owner kind = some view) :
    view.Valid := Proofs.Formats.Dasl.Arena.Prolly.Surface.mount_valid mounted

theorem wrongArena [DecidableEq Owner] [DecidableEq Kind] {token : Token Owner Kind}
    (wrong : token.owner ≠ view.owner) : view.resolve (.local token) = .error .wrongArena := by
  simp [View.resolve, wrong]

theorem wrongKind [DecidableEq Owner] [DecidableEq Kind] {token : Token Owner Kind}
    (owner : token.owner = view.owner) (wrong : token.kind ≠ view.kind) :
    view.resolve (.local token) = .error .wrongKind := by simp [View.resolve, owner, wrong]

theorem resolve_local_iff [DecidableEq Owner] [DecidableEq Kind] (valid : view.Valid)
    (token : Token Owner Kind) (ref : Handle Name) :
    view.resolve (.local token) = .ok ref ↔
      token.owner = view.owner ∧ token.kind = view.kind ∧ token.index ∈ view.retained ∧ ref = .local token.index :=
  Proofs.Formats.Dasl.Arena.Prolly.Surface.resolve_local_iff valid token ref

theorem register_spec [DecidableEq Owner] [DecidableEq Kind] (valid : view.Valid)
    {target : Target Owner Kind Name} (registered : view.register target = .ok next) :
    ∃ ref, view.resolve target = .ok ref ∧ next = {view with roots := ref :: view.roots} ∧ next.Valid :=
  Proofs.Formats.Dasl.Arena.Prolly.Surface.register_spec valid registered

theorem unregister_spec [DecidableEq Owner] [DecidableEq Kind] [DecidableEq Name] (valid : view.Valid)
    {target : Target Owner Kind Name} (unregistered : view.unregister target = .ok next) :
    ∃ ref, view.resolve target = .ok ref ∧ next = {view with roots := view.roots.filter (· != ref)} ∧ next.Valid :=
  Proofs.Formats.Dasl.Arena.Prolly.Surface.unregister_spec valid unregistered

theorem collect_spec (collected : view.collect = some next) :
    Sweep.markAndSweep? basis view.roots = some next.resident ∧
      next = {view with retained := Sweep.mark basis view.roots, resident := next.resident} ∧
      (∀ index ∈ next.retained, index ∈ view.retained) ∧ next.Valid :=
  Proofs.Formats.Dasl.Arena.Prolly.Surface.collect_spec collected

theorem collect_exists (valid : view.Valid) (ready : Sweep.Markable basis view.roots) :
    ∃ next, view.collect = some next := Proofs.Formats.Dasl.Arena.Prolly.Surface.collect_exists valid ready

/-- Exact results (including faults) survive for every registered target
when the backing reader and routing policy are fixed. -/
theorem lookup_registered [DecidableEq Owner] [DecidableEq Kind] [LinearOrder Key]
    (valid : view.Valid) (collected : view.collect = some next) (external : Reader Name Key Payload)
    (policy : Policy Key) (fuel : Nat) (key : Key) {target : Target Owner Kind Name} {ref : Handle Name}
    (resolved : view.resolve target = .ok ref) (registered : ref ∈ view.roots) :
    next.lookup external policy fuel target key = view.lookup external policy fuel target key :=
  Proofs.Formats.Dasl.Arena.Prolly.Surface.lookup_registered valid collected external policy fuel key resolved registered

theorem collect_stale [DecidableEq Owner] [DecidableEq Kind] (collected : view.collect = some next)
    (token : Token Owner Kind) (owner : token.owner = view.owner) (kind : token.kind = view.kind)
    (inside : token.index < basis.blocks.size) (retired : token.index ∉ next.retained) :
    next.resolve (.local token) = .error .stale :=
  Proofs.Formats.Dasl.Arena.Prolly.Surface.collect_stale collected token owner kind inside retired

theorem stale_persists [DecidableEq Owner] [DecidableEq Kind] (valid : view.Valid)
    (collected : view.collect = some next) {token : Token Owner Kind}
    (stale : view.resolve (.local token) = .error .stale) : next.resolve (.local token) = .error .stale :=
  Proofs.Formats.Dasl.Arena.Prolly.Surface.stale_persists valid collected stale

theorem layer_collect_spec {layer next : Layer Owner Kind Authority basis}
    (collected : layer.collect = some next) :
    layer.surface.collect = some next.surface ∧ next.authority = layer.authority :=
  Proofs.Formats.Dasl.Arena.Prolly.Surface.layer_collect_spec collected

theorem layer_lookup_registered [DecidableEq Owner] [DecidableEq Kind] [LinearOrder Key]
    {layer next : Layer Owner Kind Authority basis} (valid : layer.surface.Valid)
    (collected : layer.collect = some next) (read : Authority → Reader Name Key Payload)
    (policy : Policy Key) (fuel : Nat) (key : Key) {target : Target Owner Kind Name} {ref : Handle Name}
    (resolved : layer.surface.resolve target = .ok ref) (registered : ref ∈ layer.surface.roots) :
    next.surface.lookup (read next.authority) policy fuel target key =
      layer.surface.lookup (read layer.authority) policy fuel target key := by
  obtain ⟨surface, authority⟩ := layer_collect_spec collected
  rw [authority]; exact lookup_registered valid surface _ policy fuel key resolved registered

end Silmaril.Formats.Dasl.Arena.Prolly.Surface
