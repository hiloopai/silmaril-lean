module

public import Silmaril.Containers.Runtime.Defs
public import Silmaril.Containers.Check.Defs
public import Silmaril.Cli.Behaviour.Defs
public import Silmaril.Wasi.Cli.Thms

/-! # Experimental CLI satisfaction adapters

Reuse `Cli.Spec.Partial` and WASI's existing `View`/`CliSat`. A view describes every finite
observation, not just successful exits. Nevertheless CLI satisfaction alone still does not
exclude source UB, blocking or divergence. `Certified` requires source noUB independently. -/

@[expose] public section
namespace Silmaril.Containers.Cli

abbrev View := Silmaril.Cli.Input → List (Check.Obs Ev) → Silmaril.Cli.Seen

/-- A partial stdio observation. Other effects supply no file-state evidence; stops are
observations too, so a completed run cannot hide an incorrect exit status. -/
def stdioStep (p : Silmaril.Cli.Seen) : Check.Obs Ev → Silmaril.Cli.Seen
  | .ev (.stdout bs) => { p with stdout := p.stdout ++ bs }
  | .ev (.stderr bs) => { p with stderr := p.stderr ++ bs }
  | .ev (.stdin bs) => { p with consumed := p.consumed + bs.length }
  | .stop (.exited c) => { p with exit := some c }
  | .stop (.refused _) => { p with refused := true }
  | _ => p

/-- This view does not claim unchanged files, noUB or progress. -/
def stdioView : View := fun _ t => t.foldl stdioStep {}

/-- One CLI specification, read through a container observation view at every prefix. -/
def Sat {I P : Type} (R : Runtime I P Ev) (image : Silmaril.Cli.Input → I) (view : View)
    (spec : Silmaril.Cli.Spec) : Prop :=
  ∀ i b, R.beh (image i) b → ∀ t, Check.ObsPrefix b t → spec.Partial i (view i t)

def Certified {I P : Type} (R : Runtime I P Ev) (image : Silmaril.Cli.Input → I) (view : View)
    (spec : Silmaril.Cli.Spec) : Prop :=
  Sat R image view spec ∧ ∀ i, (R.beh (image i)).Sat Spec.noUB

/-- Semantic bridge to actual WASI plays. Its obligations do not mention a desired CLI spec:
all source prefixes must have a play with an admitted host view, at most one invocation,
and the same partial observation. It therefore cannot be discharged by assuming the result. -/
def Realizes {I P : Type} {W : Silmaril.Wasi.World} {St : Type}
    (R : Runtime I P Ev) (image : Silmaril.Cli.Input → I) (view : View)
    (component : W.Model)
    (theory : Silmaril.Cli.Input → Silmaril.Wasm.Resource.Protocol St Silmaril.Wasi.WEv)
    (wasiView : Silmaril.Wasi.Cli.View) : Prop :=
  ∀ i b, R.beh (image i) b → ∀ t, Check.ObsPrefix b t →
    ∃ play ∈ component, (theory i).Accepts (Silmaril.Wasi.hostView (Silmaril.Wasi.wtrace play)) ∧
      Silmaril.Wasi.Cli.calls wasiView.run (Silmaril.Wasi.wtrace play) ≤ 1 ∧
      view i t = wasiView.seen i (Silmaril.Wasi.wtrace play)

end Silmaril.Containers.Cli
