module

public import Silmaril.Containers.Cli.Defs
import Silmaril.Proofs.Containers.Cli.Basic

public section
namespace Silmaril.Containers.Cli

theorem stdioView_exit (i : Silmaril.Cli.Input) (t : List (Check.Obs Ev)) (c : UInt8) :
    (stdioView i (t ++ [.stop (.exited c)])).exit = some c := by
  simp [stdioView, List.foldl_append, stdioStep]

theorem stdioView_output (i : Silmaril.Cli.Input) :
    (stdioView i [.ev (.stdout [111]), .ev (.stdout [107]), .stop (.exited 0)]).stdout =
      [111, 107] := rfl

/-- Satisfaction of an exit specification constrains the observed terminal status. -/
theorem stdioView_exit_matches (i : Silmaril.Cli.Input) (t : List (Check.Obs Ev))
    (c expected : UInt8)
    (h : (Silmaril.Cli.Spec.exits expected).Partial i
      (stdioView i (t ++ [.stop (.exited c)]))) : c = expected :=
  Silmaril.Proofs.Containers.Cli.stdioView_exit_matches i t c expected h

theorem of_wasi {I P St : Type} {W : Silmaril.Wasi.World} {R : Runtime I P Ev}
    {image : Silmaril.Cli.Input → I} {view : View} {component : W.Model}
    {theory : Silmaril.Cli.Input → Silmaril.Wasm.Resource.Protocol St Silmaril.Wasi.WEv}
    {wasiView : Silmaril.Wasi.Cli.View} {spec : Silmaril.Cli.Spec}
    (bridge : Realizes R image view component theory wasiView)
    (sat : Silmaril.Wasi.Cli.CliSat component theory wasiView spec) : Sat R image view spec :=
  Silmaril.Proofs.Containers.Cli.of_wasi bridge sat

end Silmaril.Containers.Cli
