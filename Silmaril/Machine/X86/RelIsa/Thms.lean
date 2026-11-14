module

public import Silmaril.Machine.X86.RelIsa.Defs
public import Silmaril.Proofs.Machine.X86.RelIsa.Must
public import Silmaril.Proofs.Machine.X86.RelIsa.Sim
public import Silmaril.Proofs.Machine.X86.RelIsa.Loosen
public import Silmaril.Machine.X86.Safe.Open9.Thms
public import Silmaril.Machine.X86.Sse9.Thms

/-!
# Relational x86 machines: what is proved (header)

PROVED (standard axioms; proofs in `Silmaril/Proofs/Machine/X86/RelIsa/{Must,Sim,Loosen}.lean`,
names in `Silmaril.Machine.X86.RelIsa`):

* `Must`: `Must.mono`, `Must.bind`, `Must.step_iff_outcomes`, `Must.ofOutcomes`,
  `Must.of_le` (transfer along `Le`, from a live state), `Must.of_sim` (transfer along a
  simulation), `Must.exists_run` (a run, on a machine with `Progress`);
* `Le.refl`, `Le.trans`, `Le.live_iff`; `Sim.of_le`, `Sim.refl`, `Sim.comp`;
* the deterministic case: `progress_ofIsa`, `must_ofIsa_of_runsIn`, `runsIn_of_must_ofIsa`,
  `must_ofIsa_iff`;
* loosening: `le_loosen`, `loosen_mono`, `must_loosen_of_runsIn`, `must_loosen_of_reaches`,
  `loosen_le_of_refines`, `loosen_le_of_safeRefines`;
* here: `loosen_open9_le_open` (from `Safe.ExtendsOpen Open9.step`), the view equations
  `views_ofIsa_open`, `views_ofIsa_open9`, `views_ofIsa_sse9`, and `views_upd_keeps_ext`
  for the open `MState` and `Sse9.XState` views. The `Features.MState` instance is in
  `RelIsa/Features/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Machine.X86.RelIsa

open Silmaril.X86 (State MState)
open Silmaril.Process (Memory)

/-- The views of `Open.isa` are the `MState` views. -/
theorem views_ofIsa_open : Views.ofIsa Silmaril.Machine.X86.Open.isa = Views.mstate := rfl

/-- The views of `Open9.isa` are the `MState` views. -/
theorem views_ofIsa_open9 : Views.ofIsa Silmaril.Machine.X86.Open9.isa = Views.mstate := rfl

/-- The views of `Sse9.isa` are the `XState` views. -/
theorem views_ofIsa_sse9 : Views.ofIsa Silmaril.Machine.X86.Sse9.isa = Views.xstate := rfl

/-- **Every proof on the loosened `Ext8` open machine transfers to the loosened `Ext9` one**
(and so to `JumpTable.isa = Open9.isa`), by `Must.of_le`. -/
theorem loosen_open9_le_open {P : MState → Prop} :
    Le (loosen Silmaril.Machine.X86.Open9.isa P) (loosen Silmaril.Machine.X86.Open.isa P) :=
  loosen_le_of_safeRefines rfl Safe.ExtendsOpen.ext

/-- An extension frame is kept by the view update. -/
theorem ExtFrame.views_upd_keeps_ext {σ E : Type} {V : Views σ} (F : ExtFrame V E) (s : σ)
    (c : State) (m : Memory) : F.ext (V.upd s c m) = F.ext s :=
  F.ext_upd s c m

/-- `views_upd_keeps_ext` for the open `MState` (trivial extension). -/
theorem views_upd_keeps_ext_mstate (s : MState) (c : State) (m : Memory) :
    ExtFrame.mstate.ext (Views.mstate.upd s c m) = ExtFrame.mstate.ext s := rfl

/-- `views_upd_keeps_ext` for `Sse9.XState`: the view update keeps the XMM file. -/
theorem views_upd_keeps_ext_xstate (x : Silmaril.Machine.X86.Sse9.XState) (c : State)
    (m : Memory) : (Views.xstate.upd x c m).xmm = x.xmm := rfl

end Silmaril.Machine.X86.RelIsa
