module

public import Silmaril.Wasm.Component.FXRes.Example.Defs
public import Silmaril.Wasm.Component.FXRes.Handle.Thms
public import Silmaril.Proofs.Wasm.Component.FXRes.Example.Run

/-!
# Continuations as Component Model resources: an example (results)

Proofs of the run in `Silmaril.Proofs.Wasm.Component.FXRes.Example.Run`.

* `example_run`: from `start s f a ct` (with `s.funcs[a]? = some fi`), the joint system runs
  `cont.new` (store entry `0`), `new` (handle `1`, entry `0` consumed), `take` (entry `1`,
  handle `1` freed) and `resume` (entry `1` consumed) to `finish s f a fi`, where the resumed
  continuation calls `a` under an empty handler frame. Table history
  `[added 1 C, removed 1 C]`, store history `[alloc 0, free 0, alloc 1, free 1]`.
* `example_protocols`: both histories are accepted by the handle protocol in both roles, and the
  ownership history by `obProto` (instances of the general theorems of `FXRes.Handle`).
* `example_dead`: in the final state handle `1` is dead (a second `take`, `drop` or `borrow` of it
  fails), and both continuations are consumed, so resuming either stale reference traps
  (`example_stale_traps`).
* `borrowed_take_rejected`, `double_take_rejected`, `owned_take_accepted`: the ownership
  protocol rejects taking (resuming) a continuation through a borrowed handle and taking an owned
  one twice, and accepts the owned use-then-take of the example (kernel evaluation).

What the example does not show: the run of `a`'s body after the `resume` (it depends on the Core
code of `a`), and the built-ins as host calls of a component engine (see `FXRes.Handle`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.Example

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Resource Silmaril.Wasm.Component.FXRes
open Silmaril.Wasm.Component.Runtime (Table)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- **The example's histories respect the protocols** (also instances of `jsteps_table_protocol`,
`jsteps_own_protocol` and `jsteps_store_protocol` applied to `example_run`). -/
theorem example_protocols (C : ContFX) (r : Role) :
    (handleProto ℕ r).Accepts ([Table.Event.added 1 C, .removed 1 C].map tableEv) ∧
      (obProto ℕ).Accepts ([Table.Event.added 1 C, .removed 1 C].map ownEv) ∧
      (handleProto ℕ r).Accepts [.alloc 0, .free 0, .alloc 1, .free 1] := by
  have ht : [Table.Event.added 1 C, .removed 1 C].map tableEv = [HEv.alloc 1, .free 1] := rfl
  have ho : [Table.Event.added 1 C, .removed 1 C].map ownEv = [OEv.alloc 1, .free 1] := rfl
  rw [ht, ho]
  cases r <;> exact ⟨rfl, rfl, rfl⟩

/-- **In the final state the handle is dead and both continuations are consumed.** -/
theorem example_dead (s : Store H) (f : Frame) (a : ℕ) (fi : FuncInst H) :
    (finish s f a fi).tab.get? 1 = none ∧ (finish s f a fi).tab.remove? 1 = none ∧
      Consumed (finish s f a fi).cfg.conts 0 ∧ Consumed (finish s f a fi).cfg.conts 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Resuming a stale reference of the final state traps. -/
theorem example_stale_traps (s : Store H) (f : Frame) (k : ℕ)
    (hk : k = 0 ∨ k = 1) (ct : TypeIdx) :
    StepFX' P host fx ⟨s, [none, none], f, fvals [] ++ [.contRef k, .fx (.resume ct [])]⟩
      ⟨s, [none, none], f, [.core .trap]⟩ := by
  have hc : Consumed [none, none] k := by
    rcases hk with rfl | rfl <;> rfl
  exact stale_resume_traps hc [] ct []

/-- Taking (resuming) a continuation through a **borrowed** handle violates the ownership
protocol. -/
theorem borrowed_take_rejected : (obProto ℕ).acceptsB [.lend 1, .use 1, .free 1] = false := by
  decide

/-- Taking an owned continuation handle **twice** violates the ownership protocol. -/
theorem double_take_rejected : (obProto ℕ).acceptsB [.alloc 1, .free 1, .free 1] = false := by
  decide

/-- The owned use-then-take of the example is accepted. -/
theorem owned_take_accepted : (obProto ℕ).acceptsB [.alloc 1, .use 1, .free 1] = true := by
  decide

end Silmaril.Wasm.Component.FXRes.Example
