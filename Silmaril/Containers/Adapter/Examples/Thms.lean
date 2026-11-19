module

public import Silmaril.Containers.Adapter.Examples.Defs
public import Silmaril.Containers.Category.Thms
public import Silmaril.Containers.Events.Thms
public import Silmaril.Containers.Outcome.Thms
public import Silmaril.Containers.Posix.Thms
public import Silmaril.Containers.Signals.Thms
public import Silmaril.Containers.Executor.Thms
import Silmaril.Proofs.Containers.Adapter.Examples.Basic

public section
namespace Silmaril.Containers.Adapter.Examples

theorem abstract_load : abstractRuntime.load manifest = .ok (Fixtures.Tiny.exit 0) := rfl

theorem abstract_safe :
    (abstractRuntime.beh manifest).Sat (fun b => Spec.noUB b ∧ b = .done [] (.exited 0)) :=
  Silmaril.Proofs.Containers.Adapter.Examples.abstract_safe

theorem small_stdio : stdioCodec.finite [.stdout [111, 107]] (.exited 0) =
    .done [.output [111, 107]] (.exited 0) := rfl

theorem unsupported_stdio : stdioCodec.finite [.stdout [111], .clock 0] (.exited 0) =
    .done [.output [111]] (.undefined .unmodeled) := rfl

theorem trap_default : (Outcome.trapped (U := UB) 0).NoUB := trivial

theorem trap_moreUB : ¬ ((Outcome.trapped (U := UB) 0).trapAsUB .unmodeled).NoUB := _root_.id

theorem alias_offset :
    ((Posix.readStep aliases 3 1 (.bytes [65] (by decide))).bind (·.lookup 4)) = some ⟨91, 1⟩ := rfl

theorem partial_write_effect :
    ((Posix.respond aliases (.write 4 [88, 89]) (.accepted 1 (by decide))).map (·.2)) =
      some (.write 91 0 [88]) := rfl

theorem cancel_cleanup : cancelled.effects = [.close cleanupSocket] ∧
    cancelled.stop = some (.exited 130) ∧ Spec.noUB (Signals.observe cancelled) :=
  ⟨rfl, rfl, trivial⟩

theorem residual_cleanup : Signals.execute (Signals.execute {} cancelPrefix) cleanup = cancelled :=
  (Signals.execute_append {} cancelPrefix cleanup).symm

theorem buggy_handler : ¬ Spec.noUB (Signals.observe buggy) := _root_.id

theorem normal_no_delivery :
    Signals.NoDelivery [.effect (.stdout [111, 107]), .exit 0] := by
  simp [Signals.NoDelivery]

theorem default_signal_defined : Spec.noUB (Signals.observe
    (Signals.execute {} [.arrive 15, .deliver 15, .defaultTerminate])) := trivial

theorem masked_delivery_unsupported : (Signals.execute {}
    [.mask 2 true, .arrive 2, .deliver 2]).stop = some (.undefined .unmodeled) := rfl

theorem toy_certificate : toyExecutor.Certificate :=
  Silmaril.Proofs.Containers.Adapter.Examples.toy_certificate

theorem wellformed_resource_refusal :
    (fun _ : Unit => True) () ∧ resourceLoader.load () = .error .resources := ⟨trivial, rfl⟩

end Silmaril.Containers.Adapter.Examples
