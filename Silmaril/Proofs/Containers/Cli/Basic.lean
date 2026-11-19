module

public import Silmaril.Containers.Cli.Defs

public section
namespace Silmaril.Proofs.Containers.Cli
open Silmaril.Containers

theorem stdioView_exit_matches (i : Silmaril.Cli.Input) (t : List (Check.Obs Ev))
    (c expected : UInt8)
    (h : (Silmaril.Cli.Spec.exits expected).Partial i
      (Cli.stdioView i (t ++ [.stop (.exited c)]))) : c = expected := by
  obtain ⟨o, ho, hp⟩ := h
  have hc : (Cli.stdioView i (t ++ [.stop (.exited c)])).exit = some c := by
    simp [Cli.stdioView, List.foldl_append, Cli.stdioStep]
  exact (hp.2.2.2.2.2 c hc).1.trans ho

theorem of_wasi {I P St : Type} {W : Silmaril.Wasi.World} {R : Runtime I P Ev}
    {image : Silmaril.Cli.Input → I} {view : Cli.View} {component : W.Model}
    {theory : Silmaril.Cli.Input → Silmaril.Wasm.Resource.Protocol St Silmaril.Wasi.WEv}
    {wasiView : Silmaril.Wasi.Cli.View} {spec : Silmaril.Cli.Spec}
    (bridge : Cli.Realizes R image view component theory wasiView)
    (sat : Silmaril.Wasi.Cli.CliSat component theory wasiView spec) :
    Cli.Sat R image view spec := by
  intro i b hb t ht
  obtain ⟨play, hp, hhost, honce, heq⟩ := bridge i b hb t ht
  rw [heq]
  exact sat i play hp hhost honce

end Silmaril.Proofs.Containers.Cli
