module

public import Silmaril.Wasm.Det.CompRef.Defs
public import Silmaril.Wasm.Det.Game.Instance.Thms
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Wasm.Component.Reference.Core3Sem.Defs

/-!
# The IR's Core 3.0 semantics of a module is deterministic (stateless) and trap-strict

`(core3Sem P).sem m` is the instance strategy between the import and export handlers
`importH`/`exportH`; both handlers are trap-strict (a trap answer becomes `none`, `none` becomes
`Answer.trap`), and the instance strategy is deterministic (stateless) when the instance is
`DetModule` (`StatelessModule`), and always strict. `modSem P` uses `core3Sem P` on modules
with an instance and the handler `trapAll` otherwise.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.CompRef

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Game
  Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game Silmaril.Wasm.Det.CompIR Silmaril.Wasm.Det.CompRef
open Silmaril.Wasm.Numerics (Profile)

theorem exportH_strict (m : NumInstance) (q : (CoreIface.sig m.exports).Op) :
    ProgStrict (wasmTraps m.inst.exports) (noneTraps _ q) (exportH m q) := by
  unfold exportH
  dsimp only
  split
  · split
    · refine .call (fun a ha => ?_) fun _ => .pure _
      have ha' : a = .trap := ha
      subst ha'
      exact ⟨none, rfl, rfl⟩
    · exact .pure _
  · exact .pure _

theorem importH_strict (m : NumInstance) (q : (ifaceSig m.inst.imports).Op) :
    ProgStrict (noneTraps _) (wasmTraps m.inst.imports q) (importH m q) := by
  refine .call (fun r hr => ?_) fun _ => .pure _
  have hr' : r = none := hr
  subst hr'
  exact ⟨_, rfl, rfl⟩

/-- Wrapping a good strict instance strategy in the IR handlers. -/
theorem core3Sem_wrap (Good : ∀ {E F : Sig.{0}}, Traps F → Strategy E F → Prop)
    (hcomp : ∀ {E F G : Sig.{0}} {tF : Traps F} {tG : Traps G} {σ : Strategy E F}
      {τ : Strategy F G}, Good tF σ → Good tG τ → Strict tF tG τ → Good tG (σ.comp τ))
    (hhand : ∀ {E F : Sig.{0}} (t : Traps F) (h : Handler E F), Good t (Strategy.ofHandler h))
    {P : Profile} (m : NumInstance)
    (hσ : Good (wasmTraps m.inst.exports) (m.inst.strategy P m.inst.store)) :
    Good (noneTraps _) ((core3Sem P).sem m) ∧
      Strict (noneTraps _) (noneTraps _) ((core3Sem P).sem m) := by
  have hE := strict_ofHandler (exportH_strict m)
  have hI := strict_ofHandler (importH_strict m)
  have hS := strict_strategy (P := P) (I := m.inst) m.inst.store
  exact ⟨hcomp (hhand _ _) (hcomp hσ (hhand _ _) hE) (hS.comp hE), hI.comp (hS.comp hE)⟩

theorem trapAll_strict (n k : Nat) :
    Strict (noneTraps _) (noneTraps _) (trapAll n k) :=
  strict_ofHandler fun _ => .pure _

/-- **`modSem P` is deterministic and strict on a module whose instances are `DetModule`.** -/
theorem modSem_det {P : Profile} {m : NumModule} (hD : ModDet P m) :
    DetMod (noneTraps _) ((modSem P).sem m) ∧
      Strict (noneTraps _) (noneTraps _) ((modSem P).sem m) := by
  unfold modSem
  dsimp only
  split
  · rename_i h
    have hI := h.choose_spec
    obtain ⟨⟨mt, hi⟩, -, -⟩ := hI
    let n : NumInstance := ⟨h.choose, [], m.exports, h.choose_spec.2.1, h.choose_spec.2.2⟩
    exact core3Sem_wrap (fun t σ => DetMod t σ) (fun hσ hτ hst => DetMod.comp hσ hτ hst)
      (fun t h => detMod_ofHandler t h) (P := P) n
      (detMod_strategy (hD _ h.choose_spec) (ExportsTyped.of_wellFormed hi.ok))
  · exact ⟨detMod_ofHandler _ _, trapAll_strict _ _⟩

/-- **`modSem P` is stateless and strict on a module whose instances are `StatelessModule`.** -/
theorem modSem_stateless {P : Profile} {m : NumModule} (hD : ModStateless P m) :
    StatelessMod (noneTraps _) ((modSem P).sem m) ∧
      Strict (noneTraps _) (noneTraps _) ((modSem P).sem m) := by
  unfold modSem
  dsimp only
  split
  · rename_i h
    obtain ⟨⟨mt, hi⟩, -, -⟩ := h.choose_spec
    let n : NumInstance := ⟨h.choose, [], m.exports, h.choose_spec.2.1, h.choose_spec.2.2⟩
    exact core3Sem_wrap (fun t σ => StatelessMod t σ) (fun hσ hτ hst => StatelessMod.comp hσ hτ hst)
      (fun t h => statelessMod_ofHandler t h) (P := P) n
      (statelessMod_strategy (hD _ h.choose_spec) (ExportsTyped.of_wellFormed hi.ok))
  · exact ⟨statelessMod_ofHandler _ _, trapAll_strict _ _⟩

end Silmaril.Proofs.Wasm.Det.CompRef
